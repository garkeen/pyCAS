"""解集一等结构（第二批采购清单，solveset 形态）。

头：FiniteSet(a, b, ...) / Interval(lo, hi, lo_open, hi_open) / Union(s1, s2, ...)；
空集 = Special("EmptySet")。端点可为 ±Infinity（开区间）。
隔离根端点（无理根位置）不伪造为精确值——诚实返回 None + 说明。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, BVal, EMPTY_SET


def interval(lo, hi, lo_open=True, hi_open=True):
    """区间项：lo/hi 为项（数值/±Infinity）；开闭标志为 BVal。"""
    lo = lo if lo is not None else T.neg(T.INFINITY)
    hi = hi if hi is not None else T.INFINITY
    return T.mk(T.S("Interval"), (lo, hi, BVal(bool(lo_open)), BVal(bool(hi_open))))


def finite_set(*members):
    if not members:
        return EMPTY_SET
    return T.mk(T.S("FiniteSet"), tuple(members))


def union_of(*sets):
    flat = []
    for s in sets:
        if s is EMPTY_SET:
            continue
        if isinstance(s, Expr) and s.head.name == "Union":
            flat.extend(s.args)
        else:
            flat.append(s)
    if not flat:
        return EMPTY_SET
    if len(flat) == 1:
        return flat[0]
    return T.mk(T.S("Union"), tuple(flat))


def solve_set(f, var):
    """方程 -> 解集项。返回 (set_term, provisos)；非方程/不支持抛 ValueError。"""
    from cas.solve import solve

    if isinstance(f, Expr) and f.head.name == "Eq":
        lhs = T.plus(f.args[0], T.neg(f.args[1]))
    else:
        lhs = f   # f = 0 形态
    r = solve(lhs, var)
    if r.status != "ok":
        raise ValueError(f"solve status: {r.status} ({r.note})")
    return finite_set(*r.solutions), r.provisos


def ineq_set(f, op, var):
    """一元多项式不等式 -> 区间并集项。隔离根端点不可精确表示 -> (None, 说明)。"""
    from cas.ineq import solve_poly_ineq

    ivs, _s = solve_poly_ineq(f, op, var)
    parts = []
    for lo, hi, li, hi_i in ivs:
        for e in (lo, hi):
            if e is not None and not isinstance(e, Fr):
                return None, ("endpoint is an isolating interval (irrational root); "
                              "exact interval set not representable")
        parts.append(interval(
            None if lo is None else T.N(lo), None if hi is None else T.N(hi),
            lo_open=not li, hi_open=not hi_i,
        ))
    return union_of(*parts), ""
