# -*- coding: utf-8 -*-
"""战术层：求解/化简的具体招法（与验证器完全独立）。

架构总纲：验证器不重跑求解算法。战术层交出"证书"（解、标准形），
工作流验证器只按推导类型做独立判定（回代判官、域判等）。
战术失败抛 TacticsError——诚实拒答，不降级猜测。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Sym
from cas.errors import TacticsError
from cas.project import project, zero_of
from cas.domains.poly import Poly
from cas.domains.ratfunc import RatFunc, rf_reduce


def _poly_coefs(p: Poly, var):
    """单变量视图系数：返回 {次数: 系数}。混有其他变元则拒答。"""
    if var not in p.vars:
        raise TacticsError(f"{var.name} 不在多项式变元中")
    i = p.vars.index(var)
    others = [j for j in range(len(p.vars)) if j != i]
    coefs = {}
    for k, c in p.monos:
        if any(k[j] for j in others):
            raise TacticsError("含其他变元的系数：当前仅支持单变量线性")
        coefs[k[i]] = c
    return coefs


def solve_linear(content, var: Sym):
    """线性求解战术：等式 -> 解项（证书）。

    路径：投影到 K[x]/K(x) -> （有理式取约简后分子）-> 次数必须为 1
    -> -b/a 转驻留项。验证由工作流回代判官独立完成，本函数不重复。
    """
    if not (isinstance(content, T.Expr) and content.head.name == "Eq"):
        raise TacticsError("solve 需要等式")
    lhs, rhs = content.args
    diff = T.plus(lhs, T.neg(rhs))
    hit = project(diff)
    if hit is None:
        raise TacticsError("等式差值不在 ℚ/多项式/有理函数域内")
    if hit.element is None:
        raise TacticsError("等式不含该变元")
    ring = hit.domain.ring
    el = hit.element
    if isinstance(el, RatFunc):
        el = rf_reduce(ring, el).num      # num/den = 0 ⟺ num = 0（den≠0 归守卫）
        if el.is_zero():
            raise TacticsError("分子恒零：恒等式，无唯一解")
    if not isinstance(el, Poly):
        raise TacticsError("投影元素非多项式")
    coefs = _poly_coefs(el, var)
    deg = max(coefs) if coefs else 0
    if deg != 1:
        raise TacticsError(f"{deg} 次方程，当前战术仅支持线性")
    a = coefs.get(1)
    if a is None or ring.is_zero(a):
        raise TacticsError("首项系数为零")
    b = coefs.get(0, ring.from_int(0))
    sol = -b / a
    return T.N(sol)


# ---------------------------------------------------------------------------
# 丢番图碎片（ℤ 是可判定碎片的宿主；一般情形是定理级拒答，架构 7.3）
# ---------------------------------------------------------------------------

def solve_diophantine_linear(a: int, b: int, c: int):
    """ax + by = c 的整数解（扩展欧几里得）。

    返回 ((x0, y0), (dx, dy))：特解与周期——全部解为
    (x0 + dx·t, y0 + dy·t), t ∈ ℤ。gcd(a,b) ∤ c 时无解，抛拒答。
    """
    from cas.domains.z import Z_RING
    g, s, t = Z_RING.xgcd(a, b)
    if g == 0:
        if c != 0:
            raise TacticsError("0 = c ≠ 0：无解")
        return ((0, 0), (1, 0))            # 0 = 0：全平面，给平凡参数化
    if c % g != 0:
        raise TacticsError(f"无整数解：gcd({a},{b})={g} 不整除 {c}")
    m = c // g
    return ((s * m, t * m), (b // g, -a // g))


def integer_roots(p, var):
    """整系数单变量多项式的全部整数根（有理根定理）。

    整数根必整除常数项——完备有限候选集，逐个 Horner 精确验证。
    返回升序列表。系数含非整数抛拒答（片段外）。
    """
    if var not in p.vars:
        return []
    i = p.vars.index(var)
    others = [j for j in range(len(p.vars)) if j != i]
    coefs = {}
    for k, c in p.monos:
        if any(k[j] for j in others):
            raise TacticsError("含其他变元：当前仅支持单变量")
        if getattr(c, "denominator", 1) != 1:
            raise TacticsError("系数非整数：整数根定理片段外")
        coefs[k[i]] = int(c)
    if not coefs:
        return []
    roots = []
    while coefs.get(0, 0) == 0:            # x | p：0 是根，逐个降阶
        roots.append(0)
        coefs = {e - 1: c for e, c in coefs.items() if e > 0}
        if not coefs:
            return roots
    deg = max(coefs)
    a0 = coefs[0]
    cands = set()
    for d in range(1, abs(a0) + 1):
        if a0 % d == 0:
            cands.update((d, -d))
    for r in sorted(cands):
        acc = coefs[deg]
        for e in range(deg - 1, -1, -1):   # Horner
            acc = acc * r + coefs.get(e, 0)
        if acc == 0:
            roots.append(r)
    return sorted(set(roots))


def solve_piecewise(f, x: Sym, target):
    """解分段方程 pw(...)=target：逐支求解 + 分支条件成员判定。

    可判定片段：
    · 常值支——支值恒等于 target 则整支区域为解（区域解），否则无贡献；
    · 线性支——线性求解得候选，代入分支条件经判定管线裁决（成立收、
      不成立弃、未决记条件）。
    任一支非线性即拒——漏掉它可能丢解，完备性无法保证，诚实拒答。

    返回 {"points": [点解], "regions": [区域条件], "conditional": [(解,条件)]}。"""
    from cas.piecewise import fold_nested, branches, is_piecewise
    from cas.decide import decide
    from cas.context import Context
    from cas.verdict import YES, NO
    from cas.qarith import fold
    if not is_piecewise(f):
        raise TacticsError("solve_piecewise 需分段函数")
    f = fold_nested(f)
    points, regions, conditional = [], [], []
    for v, c in branches(f):
        if x not in T.free_vars(v):
            z = zero_of(T.plus(v, T.neg(target)))
            if z is True:
                regions.append(c)                 # 常值支恒等 → 整支区域为解
            elif z is None:
                conditional.append((None, c))     # 常值支是否相等未决
            continue
        try:
            sol = solve_linear(T.eq(v, target), x)
        except TacticsError as e:
            raise TacticsError(f"分支非线性，分段求解完备性无法保证：{e}")
        verdict = decide(fold(T.subst(c, {x: sol})), Context())
        if verdict is YES:
            points.append(sol)
        elif verdict is NO:
            continue
        else:
            conditional.append((sol, c))
    return {"points": points, "regions": regions, "conditional": conditional}
