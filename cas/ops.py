"""项层结构操作（M2 基础 API）：together/cancel/collect/coefficient/numerator/denominator。

全部建在环规范形与 Poly/RatFunc 之上，纯结构操作、不做判定。
多变量通分可约性受 gcd 能力限制：单变量做约分（cancel 语义），
多变量只通分不约分（诚实标注，见 together 文档）。
"""

from cas import term as T
from cas.term import Expr
from cas.poly import Poly, PolyError, ugcd, mgcd, div_exact
from cas.simplify import expand


def _vars_of(t):
    return sorted(T.free_vars(t), key=lambda s: s.name)


def _frac(t, vs):
    """term -> (P, Q) 通分（递归，不约分）。vs 为变量元组。"""
    if isinstance(t, Expr):
        n = t.head.name
        if n == "Plus":
            acc_p, acc_q = Poly.zero(vs), Poly.one(vs)
            for a in t.args:
                pa, qa = _frac(a, vs)
                acc_p, acc_q = acc_p * qa + pa * acc_q, acc_q * qa
            return acc_p, acc_q
        if n == "Times":
            p, q = Poly.one(vs), Poly.one(vs)
            for a in t.args:
                pa, qa = _frac(a, vs)
                p, q = p * pa, q * qa
            return p, q
        if n == "Power":
            b, e = t.args
            pb, qb = _frac(b, vs)
            if isinstance(e, T.Int):
                if e.v >= 0:
                    return pb ** e.v, qb ** e.v
                return qb ** (-e.v), pb ** (-e.v)
            raise PolyError("non-integer power")
    return Poly.from_term(t, vs), Poly.one(vs)


def _reduce(p, q, vs):
    """约分并首一化分母：单变量走 ugcd，多变量走 mgcd + 精确除法。"""
    if len(vs) == 1:
        g = ugcd(p, q)
        if not g.is_zero():
            p = p.udivmod(g)[0]
            q = q.udivmod(g)[0]
    else:
        g = mgcd(p, q)
        if not g.is_zero() and not g.is_const():
            p = div_exact(p, g)
            q = div_exact(q, g)
    return p, q


def _pair(t):
    vs = tuple(_vars_of(t))
    if not vs:
        raise PolyError("no variables")
    p, q = _frac(t, vs)
    return _reduce(p, q, vs), vs


def together(t):
    """通分并约分（单变量与多变量均可）。返回规范有理式项。"""
    (p, q), _ = _pair(t)
    if q.is_const():
        return p.to_term()
    return T.times(p.to_term(), T.pw(q.to_term(), T.MONE))


def cancel(t):
    """约去分子分母公因子（经同一规范形，与 together 同实现）。"""
    return together(t)


def numerator(t):
    """分子（通分约分后）。"""
    (p, _), _ = _pair(t)
    return p.to_term()


def denominator(t):
    """分母（通分约分后，首一）。常数分母返回 1。"""
    (_, q), _ = _pair(t)
    return q.to_term()


def _poly_with(t, x):
    """以 x 为主变量建 Poly，其余自由符号为次变量。"""
    others = tuple(v for v in _vars_of(t) if v is not x)
    return Poly.from_term(expand(t), (x,) + others), others


def coefficient(t, x, k=1):
    """x^k 的系数（关于其余符号的表达式）。非多项式抛 PolyError。"""
    p, others = _poly_with(t, x)
    m = {exps[1:]: v for exps, v in p.monos.items() if exps[0] == k}
    return Poly(others, m).to_term()


def coefficient_list(t, x):
    """按 x 升幂的系数列表 [c0, c1, ..., cd]。"""
    p, others = _poly_with(t, x)
    d = p.degree(x)
    out = []
    for k in range(d + 1):
        m = {exps[1:]: v for exps, v in p.monos.items() if exps[0] == k}
        out.append(Poly(others, m).to_term())
    return out


def collect(t, x):
    """按 x 的幂收集（仅多项式部分；非多项式形态返回展开式）。"""
    try:
        p, others = _poly_with(t, x)
    except PolyError:
        return expand(t)
    d = p.degree(x)
    if d < 0:
        return T.ZERO
    parts = []
    for k in range(d, -1, -1):
        m = {exps[1:]: v for exps, v in p.monos.items() if exps[0] == k}
        if not m:
            continue
        c = Poly(others, m).to_term()
        if k == 0:
            parts.append(c)
        elif k == 1:
            parts.append(T.times(c, x) if c is not T.ONE else x)
        else:
            xk = T.pw(x, T.N(k))
            parts.append(T.times(c, xk) if c is not T.ONE else xk)
    if not parts:
        return T.ZERO
    if len(parts) == 1:
        return parts[0]
    return T.mk(T.S("Plus"), tuple(parts))
