from cas import term as T
from cas.errors import BudgetExceeded

# 类型洞谓词（结构检查，无需上下文；语义谓词如正负走规则 guard/decide）
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


def _match(pat, tgt, sub, st):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    k = pat.__class__
    if k is T.PatVar:
        if not _pred_ok(pat, tgt):
            return
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = tgt
            yield s2
        elif cur is tgt:
            yield sub
        return
    if k is T.PatSeq:
        cur = sub.get(pat.name)
        if cur is None:
            s2 = dict(sub)
            s2[pat.name] = (tgt,)
            yield s2
        elif cur == (tgt,):
            yield sub
        return
    if k is T.Expr:
        if not isinstance(tgt, T.Expr):
            return
        if tgt.head is not pat.head:
            return
        if pat.head.name in T.AC:
            yield from _match_orderless(list(pat.args), list(tgt.args), sub, st)
        else:
            yield from _match_seq(list(pat.args), list(tgt.args), sub, st)
        return
    if k is T.Bound:
        if isinstance(tgt, T.Bound):
            yield from _match(pat.body, tgt.body, sub, st)
        return
    if pat is tgt:
        yield sub
    return


def _match_seq(pats, terms, sub, st):
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    if isinstance(p, T.PatSeq):
        n = len(terms)
        for k in range(1, n + 1):
            cur = sub.get(p.name)
            if cur is None:
                s2 = dict(sub)
                s2[p.name] = tuple(terms[:k])
                yield from _match_seq(pats[1:], terms[k:], s2, st)
            else:
                if tuple(terms[:k]) == cur:
                    yield from _match_seq(pats[1:], terms[k:], sub, st)
        return
    if not terms:
        return
    for s2 in _match(p, terms[0], sub, st):
        yield from _match_seq(pats[1:], terms[1:], s2, st)


def _match_orderless(pats, terms, sub, st):
    st[0] -= 1
    if st[0] < 0:
        raise BudgetExceeded()
    if not pats:
        if not terms:
            yield sub
        return
    p = pats[0]
    if not isinstance(p, (T.PatVar, T.PatSeq)) and not _has_holes(p):
        if p in terms:
            rest = list(terms)
            rest.remove(p)
            yield from _match_orderless(pats[1:], rest, sub, st)
        return
    if isinstance(p, T.PatSeq):
        n = len(terms)
        for i in range(n):
            for ln in range(1, n - i + 1):
                seq = tuple(terms[i : i + ln])
                rest = terms[:i] + terms[i + ln :]
                cur = sub.get(p.name)
                if cur is None:
                    s2 = dict(sub)
                    s2[p.name] = seq
                    yield from _match_orderless(pats[1:], rest, s2, st)
                elif cur == seq:
                    yield from _match_orderless(pats[1:], rest, sub, st)
        return
    for i, t in enumerate(terms):
        rest = terms[:i] + terms[i + 1 :]
        for s2 in _match(p, t, sub, st):
            yield from _match_orderless(pats[1:], rest, s2, st)


def _has_holes(p):
    if isinstance(p, (T.PatVar, T.PatSeq)):
        return True
    if isinstance(p, T.Expr):
        return any(_has_holes(a) for a in p.args)
    if isinstance(p, T.Bound):
        return _has_holes(p.body)
    return False


def _sub_key(sub):
    items = []
    for k, v in sub.items():
        if isinstance(v, tuple):
            items.append((k, tuple(x._h for x in v)))
        else:
            items.append((k, v._h))
    return tuple(sorted(items, key=lambda kv: kv[0]))


def matches(pat, tgt, sub=None, budget=10000):
    st = [budget]
    base = dict(sub) if sub else {}
    seen = set()
    if isinstance(pat, T.PatVar):
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
