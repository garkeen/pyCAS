from enum import Enum

from cas import term as T
from cas.term import S, N, PI, E
from cas.domain import R, Q, Z, C, DEFAULT_DOMAIN, domain_of


class T3(Enum):
    YES = "YES"
    NO = "NO"
    UNKNOWN = "UNKNOWN"


def and3(a, b):
    if a is T3.NO or b is T3.NO:
        return T3.NO
    if a is T3.YES and b is T3.YES:
        return T3.YES
    return T3.UNKNOWN


def or3(a, b):
    if a is T3.YES or b is T3.YES:
        return T3.YES
    if a is T3.NO and b is T3.NO:
        return T3.NO
    return T3.UNKNOWN


def not3(a):
    if a is T3.YES:
        return T3.NO
    if a is T3.NO:
        return T3.YES
    return T3.UNKNOWN


_NEG = {
    "Gt": ("Le", False),
    "Ge": ("Lt", False),
    "Lt": ("Ge", False),
    "Le": ("Gt", False),
    "Eq": ("Ne", False),
    "Ne": ("Eq", False),
}


def negate(f):
    if isinstance(f, T.Expr) and f.head.name in _NEG:
        name, swap = _NEG[f.head.name]
        a, b = f.args
        if swap:
            a, b = b, a
        return T.mk(S(name), (a, b))
    if isinstance(f, T.Expr) and f.head.name == "Not":
        return f.args[0]
    return T.mk(S("Not"), (f,))


_CMP = ("Lt", "Le", "Gt", "Ge", "Eq", "Ne")
_CMP_INV = {"Lt": "Gt", "Gt": "Lt", "Le": "Ge", "Ge": "Le"}


def _cmp_numeric(op, a, b):
    av = T.num_val(a) if T.is_num(a) else None
    bv = T.num_val(b) if T.is_num(b) else None
    if av is None or bv is None:
        return None
    if op == "Lt":
        r = av < bv
    elif op == "Le":
        r = av <= bv
    elif op == "Gt":
        r = av > bv
    elif op == "Ge":
        r = av >= bv
    elif op == "Eq":
        r = av == bv
    else:
        r = av != bv
    return T3.YES if r else T3.NO


def _same(op, a, b):
    if a is not b:
        return None
    if op in ("Eq", "Le", "Ge"):
        return T3.YES
    return T3.NO


def _poly_eq_check(a, b):
    from cas.poly import Poly, PolyError

    vs = sorted(T.free_vars(a) | T.free_vars(b), key=lambda s: s.name)
    try:
        pa = Poly.from_term(a, tuple(vs))
        pb = Poly.from_term(b, tuple(vs))
    except PolyError:
        return None
    if pa.monos == pb.monos:
        return T3.YES
    return None


def _facts_lookup(fact, ctx):
    for e in ctx.entries:
        f = e.fact
        if f is fact:
            return T3.YES
        if f is negate(fact):
            return T3.NO
        if isinstance(f, T.Expr) and isinstance(fact, T.Expr):
            if f.head.name in _CMP_INV and fact.head.name in _CMP_INV:
                if (
                    f.head.name == _CMP_INV[fact.head.name]
                    and f.args[0] is fact.args[1]
                    and f.args[1] is fact.args[0]
                ):
                    return T3.YES
    return None


def _chain_query(op, a, b, ctx):
    lo = {}
    hi = {}
    for e in ctx.entries:
        f = e.fact
        if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge"):
            u, v = f.args
            if T.is_num(u):
                uu, vv = v, T.num_val(u)
                if f.head.name in ("Lt", "Le"):
                    cur = hi.get(uu)
                    if cur is None or vv < cur[0] or (vv == cur[0] and f.head.name == "Lt" and not cur[1]):
                        hi[uu] = (vv, f.head.name == "Lt")
                else:
                    cur = lo.get(uu)
                    if cur is None or vv > cur[0] or (vv == cur[0] and f.head.name == "Gt" and not cur[1]):
                        lo[uu] = (vv, f.head.name == "Gt")
            elif T.is_num(v):
                vv = T.num_val(v)
                if f.head.name in ("Gt", "Ge"):
                    cur = lo.get(u)
                    if cur is None or vv > cur[0] or (vv == cur[0] and f.head.name == "Gt" and not cur[1]):
                        lo[u] = (vv, f.head.name == "Gt")
                else:
                    cur = hi.get(u)
                    if cur is None or vv < cur[0] or (vv == cur[0] and f.head.name == "Lt" and not cur[1]):
                        hi[u] = (vv, f.head.name == "Lt")
    if T.is_num(b) and not T.is_num(a):
        bv = T.num_val(b)
        l = lo.get(a)
        h = hi.get(a)
        if op == "Gt":
            if l and (l[0] > bv or (l[0] == bv and l[1])):
                return T3.YES
            if h and h[0] <= bv:
                return T3.NO
        elif op == "Ge":
            if l and l[0] >= bv:
                return T3.YES
            if h and h[0] < bv:
                return T3.NO
        elif op == "Lt":
            if h and (h[0] < bv or (h[0] == bv and h[1])):
                return T3.YES
            if l and l[0] >= bv:
                return T3.NO
        elif op == "Le":
            if h and h[0] <= bv:
                return T3.YES
            if l and l[0] > bv:
                return T3.NO
        elif op == "Eq":
            if (l and l[0] > bv) or (h and h[0] < bv):
                return T3.NO
        elif op == "Ne":
            if (l and (l[0] > bv or (l[0] == bv and l[1]))) or (
                h and (h[0] < bv or (h[0] == bv and h[1]))
            ):
                return T3.YES
    elif T.is_num(a) and not T.is_num(b):
        av = T.num_val(a)
        l = lo.get(b)
        h = hi.get(b)
        if op == "Lt":
            if l and (l[0] > av or (l[0] == av and l[1])):
                return T3.YES
            if h and h[0] <= av:
                return T3.NO
        elif op == "Le":
            if l and l[0] >= av:
                return T3.YES
            if h and h[0] < av:
                return T3.NO
        elif op == "Gt":
            if h and (h[0] < av or (h[0] == av and h[1])):
                return T3.YES
            if l and l[0] >= av:
                return T3.NO
        elif op == "Ge":
            if h and h[0] <= av:
                return T3.YES
            if l and l[0] > av:
                return T3.NO
        elif op == "Eq":
            if (l and l[0] > av) or (h and h[0] < av):
                return T3.NO
        elif op == "Ne":
            if (l and (l[0] > av or (l[0] == av and l[1]))) or (
                h and (h[0] < av or (h[0] == av and h[1]))
            ):
                return T3.YES
    adj = {}
    eqclass = {}

    def find(x):
        while x in eqclass:
            x = eqclass[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx is not ry:
            eqclass[rx] = ry

    strict = op in ("Lt", "Gt")
    want = (a, b)
    if op in ("Gt", "Ge"):
        want = (b, a)
    for e in ctx.entries:
        f = e.fact
        if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge"):
            opf = f.head.name
            u, v = f.args
            if opf in ("Gt", "Ge"):
                u, v = v, u
                opf = "Lt" if opf == "Gt" else "Le"
            if opf == "Eq":
                union(u, v)
            else:
                adj.setdefault(u, []).append((v, opf == "Lt"))
    if a is b:
        return T3.YES if op in ("Le", "Ge", "Eq") else T3.NO
    from collections import deque

    start, goal = want
    q = deque([(start, False)])
    seen = {start._h}
    while q:
        cur, ever_strict = q.popleft()
        for nxt, st in adj.get(cur, ()):
            ns = ever_strict or st
            if nxt is goal:
                if not strict or ns:
                    return T3.YES
            key = (nxt._h, ns)
            if nxt._h not in seen or (nxt._h, False) in seen and ns:
                seen.add(key)
                q.append((nxt, ns))
    return None


_RULES = []
_MAX_DEPTH = 6


def derive(name, applies):
    def deco(fn):
        _RULES.append((name, applies, fn))
        return fn
    return deco


def _is_cmp(f):
    return isinstance(f, T.Expr) and f.head.name in _CMP


def _is_ord(f):
    return isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge")


def _zero_cmp_of(a, ctx, q, op):
    nneg = R.nonneg(a, ctx)
    pos = R.pos(a, ctx)
    if op == "Gt":
        if pos is True:
            return T3.YES
        if nneg is False or (nneg is True and pos is False):
            return T3.NO
        return None
    if op == "Ge":
        if nneg is True:
            return T3.YES
        if nneg is False:
            return T3.NO
        return None
    if op == "Lt":
        if pos is True:
            return T3.NO
        if nneg is False:
            return T3.YES
        if nneg is True and pos is False:
            return T3.NO
        return None
    if op == "Le":
        if pos is True:
            return T3.NO
        if nneg is False:
            return T3.YES
        if nneg is True and pos is False:
            return T3.YES
        return None
    return None


@derive("ne-from-ord", lambda f: f.head.name == "Ne")
def _rule_ne_from_ord(f, ctx, q):
    a, b = f.args
    if q(T.mk(S("Gt"), (a, b))) is T3.YES or q(T.mk(S("Lt"), (a, b))) is T3.YES:
        return T3.YES
    if q(T.mk(S("Eq"), (a, b))) is T3.YES:
        return T3.NO
    return None


@derive("cmp-via-eq", lambda f: _is_ord(f))
def _rule_cmp_via_eq(f, ctx, q):
    a, b = f.args
    if T.is_num(b):
        for e in ctx.entries:
            g = e.fact
            if (
                isinstance(g, T.Expr)
                and g.head.name == "Eq"
                and g.args[0] is a
                and T.is_num(g.args[1])
            ):
                return _cmp_numeric(f.head.name, g.args[1], b)
    return None


def _sign_of_term(t, ctx, q):
    if T.is_num(t):
        s = T.sign_num(t)
        if s > 0:
            return 1
        if s < 0:
            return -1
        return 0
    if t is PI or t is E:
        return 1
    r = q(T.mk(S("Gt"), (t, T.ZERO)))
    if r is T3.YES:
        return 1
    r = q(T.mk(S("Lt"), (t, T.ZERO)))
    if r is T3.YES:
        return -1
    r = q(T.mk(S("Eq"), (t, T.ZERO)))
    if r is T3.YES:
        return 0
    r = q(T.mk(S("Ge"), (t, T.ZERO)))
    if r is T3.YES:
        return 2
    return None


@derive("sign-atom", lambda f: _is_ord(f) and f.args[1] is T.ZERO)
def _rule_sign_atom(f, ctx, q):
    return _zero_cmp_of(f.args[0], ctx, q, f.head.name)


@derive("sign-times", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Times")
def _rule_sign_times(f, ctx, q):
    op = f.head.name
    a = f.args[0]
    s_zero = False
    s_nn = False
    neg_count = 0
    for fac in a.args:
        s = _sign_of_term(fac, ctx, q)
        if s is None:
            return None
        if s == 0:
            s_zero = True
        elif s == -1:
            neg_count += 1
        elif s == 2:
            s_nn = True
    if s_zero:
        return T3.NO if op in ("Gt", "Lt") else T3.YES
    odd = neg_count % 2 == 1
    if op == "Gt":
        if odd:
            return T3.NO
        return T3.YES if not s_nn else T3.UNKNOWN
    if op == "Ge":
        if odd and not s_nn:
            return T3.NO
        return T3.UNKNOWN if odd else T3.YES
    if op == "Lt":
        if odd and not s_nn:
            return T3.YES
        return T3.UNKNOWN if odd else T3.NO
    return T3.YES if odd else (T3.UNKNOWN if s_nn else T3.NO)


@derive("sign-even-power", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Power" and isinstance(f.args[0].args[1], T.Int) and f.args[0].args[1].v % 2 == 0)
def _rule_sign_even_power(f, ctx, q):
    op = f.head.name
    b = f.args[0].args[0]
    if op in ("Ge",):
        return T3.YES
    if op == "Lt":
        return T3.NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (b, T.ZERO)))
        if r is T3.YES:
            return T3.YES
        r = q(T.mk(S("Eq"), (b, T.ZERO)))
        if r is T3.YES:
            return T3.NO
        return None
    r = q(T.mk(S("Eq"), (b, T.ZERO)))
    if r is T3.YES:
        return T3.YES
    r = q(T.mk(S("Ne"), (b, T.ZERO)))
    if r is T3.YES:
        return T3.NO
    return None


@derive("sign-abs", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Abs")
def _rule_sign_abs(f, ctx, q):
    op = f.head.name
    u = f.args[0].args[0]
    if op == "Ge":
        return T3.YES
    if op == "Lt":
        return T3.NO
    if op == "Gt":
        r = q(T.mk(S("Ne"), (u, T.ZERO)))
        if r is T3.YES:
            return T3.YES
        r = q(T.mk(S("Eq"), (u, T.ZERO)))
        if r is T3.YES:
            return T3.NO
        return None
    r = q(T.mk(S("Eq"), (u, T.ZERO)))
    if r is T3.YES:
        return T3.YES
    r = q(T.mk(S("Ne"), (u, T.ZERO)))
    if r is T3.YES:
        return T3.NO
    return None


@derive("sign-power", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Power" and isinstance(f.args[0].args[1], T.Int) and f.args[0].args[1].v % 2 == 1)
def _rule_sign_odd_power(f, ctx, q):
    b = f.args[0].args[0]
    return q(T.mk(S(f.head.name), (b, T.ZERO)))


@derive("sign-sum", lambda f: _is_ord(f) and f.args[1] is T.ZERO and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Plus")
def _rule_sign_sum(f, ctx, q):
    op = f.head.name
    a = f.args[0]
    if op in ("Gt", "Ge"):
        all_ge = True
        any_pos = False
        for t_ in a.args:
            r = q(T.mk(S("Ge"), (t_, T.ZERO)))
            if r is not T3.YES:
                all_ge = False
                break
            r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
            if r2 is T3.YES:
                any_pos = True
        if all_ge and any_pos:
            return T3.YES
        all_le = True
        any_neg = False
        for t_ in a.args:
            r = q(T.mk(S("Le"), (t_, T.ZERO)))
            if r is not T3.YES:
                all_le = False
                break
            r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
            if r2 is T3.YES:
                any_neg = True
        if all_le and any_neg:
            return T3.NO
        return None
    all_le = True
    any_neg = False
    for t_ in a.args:
        r = q(T.mk(S("Le"), (t_, T.ZERO)))
        if r is not T3.YES:
            all_le = False
            break
        r2 = q(T.mk(S("Lt"), (t_, T.ZERO)))
        if r2 is T3.YES:
            any_neg = True
    if all_le and any_neg:
        return T3.YES
    all_ge = True
    any_pos = False
    for t_ in a.args:
        r = q(T.mk(S("Ge"), (t_, T.ZERO)))
        if r is not T3.YES:
            all_ge = False
            break
        r2 = q(T.mk(S("Gt"), (t_, T.ZERO)))
        if r2 is T3.YES:
            any_pos = True
    if all_ge and any_pos:
        return T3.NO
    return None


@derive("eq-times-zero", lambda f: f.head.name == "Eq" and isinstance(f.args[0], T.Expr) and f.args[0].head.name == "Times")
def _rule_eq_times_zero(f, ctx, q):
    a = f.args[0]
    any_zero = T3.NO
    for fac in a.args:
        r = q(T.mk(S("Eq"), (fac, T.ZERO)))
        if r is T3.YES:
            return T3.YES
        if r is T3.UNKNOWN:
            any_zero = T3.UNKNOWN
    return any_zero


@derive("sign-num", lambda f: _is_ord(f) and f.args[1] is T.ZERO and T.is_num(f.args[0]))
def _rule_sign_num(f, ctx, q):
    s = T.sign_num(f.args[0])
    op = f.head.name
    if op == "Gt":
        return T3.YES if s > 0 else T3.NO
    if op == "Ge":
        return T3.YES if s >= 0 else T3.NO
    if op == "Lt":
        return T3.YES if s < 0 else T3.NO
    return T3.YES if s <= 0 else T3.NO


@derive("eq-num", lambda f: f.head.name in ("Eq", "Ne") and T.is_num(f.args[0]) and T.is_num(f.args[1]))
def _rule_eq_num(f, ctx, q):
    if f.head.name == "Eq":
        return T3.YES if T.num_val(f.args[0]) == T.num_val(f.args[1]) else T3.NO
    return T3.YES if T.num_val(f.args[0]) != T.num_val(f.args[1]) else T3.NO


@derive("cmp-flip", lambda f: _is_cmp(f) and f.args[0] is T.ZERO and f.args[1] is not T.ZERO)
def _rule_cmp_flip(f, ctx, q):
    op = f.head.name
    a, b = f.args
    if op in ("Eq", "Ne"):
        return q(T.mk(S(op), (b, a)))
    flip = {"Gt": "Lt", "Lt": "Gt", "Ge": "Le", "Le": "Ge"}
    return q(T.mk(S(flip[op]), (b, a)))


def _derive_layer(fact, ctx, depth):
    q = lambda f: decide(f, ctx, depth + 1)
    for name, applies, fn in _RULES:
        if applies(fact):
            r = fn(fact, ctx, q)
            if r is not None:
                return r
    return None


_AXIOM_CHECKS = []


def axiom(fn):
    _AXIOM_CHECKS.append(fn)
    return fn


_CONST_BOUNDS = {id(PI): (3, 4), id(E): (2, 3)}


@axiom
def _axiom_constants(fact, ctx):
    if not (isinstance(fact, T.Expr) and fact.head.name in ("Gt", "Ge", "Lt", "Le")):
        return None
    a, b = fact.args
    if id(a) in _CONST_BOUNDS and T.is_num(b):
        lo, hi = _CONST_BOUNDS[id(a)]
        bv = T.num_val(b)
        op = fact.head.name
        if op in ("Gt", "Ge"):
            if bv <= lo:
                return T3.YES
            if bv >= hi:
                return T3.NO
        else:
            if bv >= hi:
                return T3.YES
            if bv <= lo:
                return T3.NO
    return None


@axiom
def _axiom_abs_bounded(fact, ctx):
    if isinstance(fact, T.Expr) and fact.head.name == "Le":
        a, b = fact.args
        if (
            isinstance(a, T.Expr)
            and a.head.name == "Abs"
            and isinstance(a.args[0], T.Expr)
            and a.args[0].head.name in ("Sin", "Cos")
            and T.is_num(b)
            and T.num_val(b) >= 1
        ):
            return T3.YES
    return None


def _family_cmp(fact, ctx, depth):
    op = fact.head.name
    a, b = fact.args
    if op in ("Eq", "Ne"):
        r = _same(op, a, b)
        if r is not None:
            return r
        r = _cmp_numeric(op, a, b)
        if r is not None:
            return r
        r = _facts_lookup(fact, ctx)
        if r is not None:
            return r
        if op == "Eq":
            r = _poly_eq_check(a, b)
            if r is not None:
                return r
    else:
        r = _cmp_numeric(op, a, b)
        if r is not None:
            return r
        r = _same(op, a, b)
        if r is not None:
            return r
        r = _facts_lookup(fact, ctx)
        if r is not None:
            return r
        r = _chain_query(op, a, b, ctx)
        if r is not None:
            return r
    r = _derive_layer(fact, ctx, depth)
    if r is not None:
        return r
    for ax in _AXIOM_CHECKS:
        r = ax(fact, ctx)
        if r is not None:
            return r
    return T3.UNKNOWN


def _contains(t, pat):
    if t is pat:
        return True
    if isinstance(t, T.Expr):
        return any(_contains(a, pat) for a in t.args)
    return False


def _eq_subst(fact, ctx, depth):
    a, b = fact.args
    for e in ctx.entries:
        f = e.fact
        if isinstance(f, T.Expr) and f.head.name == "Eq" and f is not fact:
            u, v = f.args
            if not (T.is_num(u) or T.is_num(v)):
                continue
            if not (_contains(a, u) or _contains(a, v) or _contains(b, u) or _contains(b, v)):
                continue
            for pat, rep in ((u, v), (v, u)):
                na = T.subst(a, {pat: rep})
                nb = T.subst(b, {pat: rep})
                if na is a and nb is b:
                    continue
                r = decide(T.mk(S("Eq"), (na, nb)), ctx, depth + 1)
                if r is not T3.UNKNOWN:
                    return r
    return None


def decide(fact, ctx, _depth=0):
    if _depth > _MAX_DEPTH:
        return T3.UNKNOWN
    if fact is T.TRUE:
        return T3.YES
    if fact is T.FALSE:
        return T3.NO
    if isinstance(fact, T.Expr):
        name = fact.head.name
        if name in _CMP:
            if name == "Eq":
                r = _eq_subst(fact, ctx, _depth)
                if r is not None:
                    return r
            return _family_cmp(fact, ctx, _depth)
        if name == "And":
            r = T3.YES
            for a in fact.args:
                r = and3(r, decide(a, ctx, _depth))
                if r is T3.NO:
                    return r
            return r
        if name == "Or":
            r = T3.NO
            for a in fact.args:
                r = or3(r, decide(a, ctx, _depth))
                if r is T3.YES:
                    return r
            return r
        if name == "Not":
            return not3(decide(fact.args[0], ctx, _depth))
    return T3.UNKNOWN


def decided(fact, ctx):
    return decide(fact, ctx, 0)


def satisfiable(constraints, ctx):
    for i, c in enumerate(constraints):
        tmp = ctx.clone()
        for j, d in enumerate(constraints):
            if j != i:
                tmp.assume(d, origin="_sat")
        if decide(c, tmp) is T3.NO or decide(negate(c), tmp) is T3.YES:
            return T3.NO
    return T3.YES if not constraints else T3.UNKNOWN


def domain_ok(fact, ctx):
    from cas.domain import dom_condition

    return satisfiable(dom_condition(fact), ctx)


def contradicted(fact, ctx):
    return decide(fact, ctx) is T3.NO or decide(negate(fact), ctx) is T3.YES


def eval_guard(guard, sub, ctx):
    g = T.instantiate(guard, sub)
    r = decide(g, ctx)
    return r.value


def equivalent(a, b, ctx=None, budget=100000):
    from cas.simplify import simplify
    from cas.context import Context

    if a is b:
        return T3.YES
    if T.is_num(a) and T.is_num(b):
        return T3.YES if T.num_val(a) == T.num_val(b) else T3.NO
    r = simplify(T.plus(a, T.neg(b)), budget)
    if r is T.ZERO:
        return T3.YES
    if ctx is None:
        ctx = Context()
    return decide(T.mk(S("Eq"), (r, T.ZERO)), ctx)