"""Pattern matching over the pattern metalanguage.

Two kinds of subject can be matched: a `Pattern` (which may contain holes) and
a `Term` used as a literal (pointer equality is literal matching, a dividend of
interned AC canonical forms). Pattern variables no longer occur inside terms,
so this module and `pattern.instantiate` are the only places where pattern
variables are interpreted.

Type-hole predicates are purely structural and need no context; semantic
predicates such as positivity go through rule guards and the decision pipeline.
"""

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.errors import BudgetExceeded

_PREDS = {
    "num": lambda t: T.is_num(t),
    "int": lambda t: isinstance(t, T.Int),
    "rat": lambda t: isinstance(t, T.Rat),
    "sym": lambda t: isinstance(t, T.Sym),
    "const": lambda t: isinstance(t, T.Const) or T.is_num(t),
    "expr": lambda t: isinstance(t, T.Expr),
}


def _pred_ok(pat, tgt):
    if pat.pred is None:
        return True
    fn = _PREDS.get(pat.pred)
    return fn is not None and fn(tgt)


# OneIdentity: an AC head with an identity element also matches a bare term,
# so `?a + ?b` matches `x` with the other hole bound to 0 and `?a * ?b` matches
# `x` with the other hole bound to 1. Only holes (PatternVar/PatternSeq) and a
# literal identity element may absorb the identity; a non-hole subpattern must
# match as written.
_ONE_ID = {}


def _one_identity():
    if not _ONE_ID:
        _ONE_ID.update({"Plus": T.ZERO, "Times": T.ONE})
    return _ONE_ID


def _bind_identity(p, ident, sub):
    """Bind pattern argument `p` to the identity element: a PatternVar is
    bound or consistency-checked, a PatternSeq is bound to the empty tuple."""
    if isinstance(p, P.PatternVar):
        if not _pred_ok(p, ident):
            return None
        cur = sub.get(p.name)
        if cur is None:
            s2 = dict(sub)
            s2[p.name] = ident
            return s2
        return sub if cur is ident else None
    if isinstance(p, P.PatternSeq):
        cur = sub.get(p.name)
        if cur is None:
            s2 = dict(sub)
            s2[p.name] = ()
            return s2
        return sub if cur == () else None
    # A literal must be the identity element itself.
    return sub if p is ident else None


def _all_identity(pats, ident, sub, st, binds=()):
    """Make every remaining pattern argument absorb the identity element."""
    if not pats:
        yield sub
        return
    s2 = _bind_identity(pats[0], ident, sub)
    if s2 is not None:
        yield from _all_identity(pats[1:], ident, s2, st, binds)


def _match_one_id(pats, ident, tgt, sub, st, binds=()):
    """OneIdentity channel: exactly one pattern argument consumes `tgt`, the
    rest absorb the identity element."""
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    if not pats:
        return
    p, rest = pats[0], pats[1:]
    # `p` consumes tgt; all the others take the identity element.
    for s2 in _match(p, tgt, sub, st, binds):
        yield from _all_identity(rest, ident, s2, st, binds)
    # `p` absorbs the identity element; tgt goes to a later argument.
    s2 = _bind_identity(p, ident, sub)
    if s2 is not None:
        yield from _match_one_id(rest, ident, tgt, s2, st, binds)


def _restore_db(t, binds):
    """Turn a DB(i) matched inside a Bound body back into the bound symbol.

    A de Bruijn index is only meaningful inside its original binding scope. A
    hole binding leaves that scope to instantiate a template, so carrying the
    raw index would make re-abstraction (mk_bound) shift it (a #1 leak).
    Restoring the symbol lets replace_at's mk_bound re-abstract it correctly.
    """
    if isinstance(t, T.DB) and binds and t.i < len(binds):
        return T.S(binds[-1 - t.i])
    return t


def _match(pat, tgt, sub, st, binds=()):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    # Literal (Term): pointer equality of interned terms is the match.
    if isinstance(pat, T.Term):
        if pat is tgt:
            yield sub
        return
    k = pat.__class__
    if k is P.PatternVar:
        if not _pred_ok(pat, tgt):
            return
        tgt = _restore_db(tgt, binds)
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = tgt
            yield s2
        elif cur is tgt:
            yield sub
        return
    if k is P.PatternSeq:
        tgt = _restore_db(tgt, binds)
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = (tgt,)
            yield s2
        elif cur == (tgt,):
            yield sub
        return
    if k is P.PatternCall:
        if isinstance(tgt, T.Expr) and tgt.head is pat.head:
            if pat.head.name in T.AC:
                yield from _match_orderless(list(pat.args), list(tgt.args), sub, st, binds)
            else:
                yield from _match_seq(list(pat.args), list(tgt.args), sub, st, binds)
            return
        ident = _one_identity().get(pat.head.name)
        if ident is not None:
            yield from _match_one_id(list(pat.args), ident, tgt, sub, st, binds)
        return
    return


def _match_seq(pats, terms, sub, st, binds=()):
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    if isinstance(p, P.PatternSeq):
        n = len(terms)
        for k in range(1, n + 1):
            seg = tuple(_restore_db(x, binds) for x in terms[:k])
            cur = sub.get(p.name)
            if cur is None:
                s2 = dict(sub)
                s2[p.name] = seg
                yield from _match_seq(pats[1:], terms[k:], s2, st, binds)
            else:
                if seg == cur:
                    yield from _match_seq(pats[1:], terms[k:], sub, st, binds)
        return
    if not terms:
        return
    for s2 in _match(p, terms[0], sub, st, binds):
        yield from _match_seq(pats[1:], terms[1:], s2, st, binds)


def _match_orderless(pats, terms, sub, st, binds=()):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    # Literal fast path: interned pointer equality, because AC canonical form
    # turns permutation equivalence into object identity.
    if isinstance(p, T.Term):
        if p in terms:
            rest = list(terms)
            rest.remove(p)
            yield from _match_orderless(pats[1:], rest, sub, st, binds)
        return
    if isinstance(p, P.PatternSeq):
        n = len(terms)
        for i in range(n):
            for ln in range(1, n - i + 1):
                seg = tuple(_restore_db(x, binds) for x in terms[i : i + ln])
                rest = terms[:i] + terms[i + ln :]
                cur = sub.get(p.name)
                if cur is None:
                    s2 = dict(sub)
                    s2[p.name] = seg
                    yield from _match_orderless(pats[1:], rest, s2, st, binds)
                elif cur == seg:
                    yield from _match_orderless(pats[1:], rest, sub, st, binds)
        return
    for i, t in enumerate(terms):
        rest = terms[:i] + terms[i + 1 :]
        for s2 in _match(p, t, sub, st, binds):
            yield from _match_orderless(pats[1:], rest, s2, st, binds)


def _sub_key(sub):
    items = []
    for k, v in sub.items():
        if isinstance(v, tuple):
            items.append((k, tuple(x._h for x in v)))
        else:
            items.append((k, v._h))
    return tuple(sorted(items, key=lambda kv: kv[0]))


def matches(pat, tgt, sub=None, budget=10000):
    """Match `pat` (Pattern | Term) against `tgt` (Term), yielding binding
    dictionaries."""
    st = [budget]
    base = dict(sub) if sub else {}
    seen = set()
    if isinstance(pat, P.PatternVar):
        if not _pred_ok(pat, tgt):
            return
        cur = base.get(pat.name)
        if cur is None or cur is tgt:
            s2 = dict(base)
            s2[pat.name] = tgt
            yield s2
        return
    for s in _match(pat, tgt, base, st):
        k = _sub_key(s)
        if k in seen:
            continue
        seen.add(k)
        yield s
