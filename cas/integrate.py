# -*- coding: utf-8 -*-
"""积分骨架（手通道，地基优先）：第一个诚实可判定片段 + 独立验证器。

范围（全部精确、无启发式、无近似）：
· 不定积分：多项式被积式（幂规则）；分段被积式逐支积分。真分式需
  Hermite、超越需 Risch——未建，抛 IntegrateError 拒答。
· 定积分：∫_a^b 遵架构 §6.3——先做 定义域 ∩ [a, b]，缺口不对 0 积分，
  未定义胞腔即拒；分段按开区间胞腔逐段牛莱求和。
· 验证独立：verify_antideriv 用微分层 d/dx 复核，与积分器两套实现。

诚实边界：
· 积分限须为有理数（代数限需 ℚ(α)，未建）；
· 分界点为无理根时拒答（需 ℚ(α) 精确定位）；
· 开区间端点/点洞处的反常性需极限层（§6.5），未建即拒。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Sym
from cas.errors import IntegrateError
from cas.verdict import Reason
from cas.project import project, zero_of
from cas.domains.poly import Poly, to_term, _norm
from cas.domains.ratfunc import RatFunc, ratfunc_domain
from cas.diff import differentiate
from cas.qarith import fold

_UNDEF = T.SP("Undefined")


# ---------------------------------------------------------------------------
# 不定积分：多项式片段
# ---------------------------------------------------------------------------

def poly_antideriv(ring, p: Poly, var_i: int) -> Poly:
    """∫ Σ c·xᵢᵏ = Σ (c/(k+1))·xᵢᵏ⁺¹（逐项幂规则，精确有理）。"""
    d = {}
    for k, c in p.monos:
        e = k[var_i]
        nk = tuple(kj + (1 if j == var_i else 0) for j, kj in enumerate(k))
        d[nk] = ring.div_exact(c, ring.from_int(e + 1))
    return _norm(ring, p.vars, d)


def integrate_term(f, x: Sym):
    """∫ f dx。多项式片段直积；分段逐支；其余诚实拒答。

    返回一个原函数（不含积分常数——不连通定义域上各连通分量的常数
    相互独立，见分段情形说明）。"""
    from cas.piecewise import is_piecewise
    if is_piecewise(f):
        return integrate_piecewise_indefinite(f, x)
    hit = project(f)
    if hit is None:
        raise IntegrateError("被积函数不在 ℚ/多项式/有理函数域", Reason.FRAGMENT)
    if hit.element is None:
        return T.times(f, x)                    # ∫ c dx = c·x
    vs = hit.domain.vars
    if x not in vs:
        return T.times(f, x)                    # 与 x 无关
    idx = vs.index(x)
    ring = hit.domain.ring
    el = hit.element
    if isinstance(el, Poly):
        return to_term(ring, poly_antideriv(ring, el, idx))
    raise IntegrateError("真分式积分需 Hermite 约化，未建", Reason.FRAGMENT)


def integrate_piecewise_indefinite(f, x: Sym):
    """分段被积式逐支积分（条件不动）。

    不连通定义域上每个连通分量的积分常数相互独立——单个 +C 是错的。
    此处返回的逐支原函数省略各分量常数，验证只查逐支 d/dx 是否还原被积式。"""
    from cas.piecewise import fold_nested, branches, piecewise
    f = fold_nested(f)
    return piecewise([(integrate_term(v, x), c) for v, c in branches(f)])


# ---------------------------------------------------------------------------
# 独立验证：d/dx F == f（微分层，另一套实现）
# ---------------------------------------------------------------------------

def _judge_zero_diff(dF, f):
    diff = fold(T.plus(dF, T.neg(f)))
    if diff is T.ZERO:
        return True
    z = zero_of(diff)
    if z is True:
        return True
    if z is False:
        return False
    allv = tuple(sorted(T.free_vars(dF) | T.free_vars(f),
                        key=lambda s: s.name))
    if not allv:
        return False
    return ratfunc_domain(*allv).equal(dF, f) is True


def verify_antideriv(F, f, x: Sym) -> bool:
    """独立验证 F 是 f 的原函数（与积分器无关）。"""
    from cas.piecewise import is_piecewise, fold_nested, branches
    if is_piecewise(f) or is_piecewise(F):
        ff = fold_nested(f)
        FF = fold_nested(F)
        bf, bF = branches(ff), branches(FF)
        if len(bf) != len(bF):
            return False
        for (vf, cf), (vF, cF) in zip(bf, bF):
            if cf is not cF:
                return False
            if not _judge_zero_diff(differentiate(vF, x), vf):
                return False
        return True
    return _judge_zero_diff(differentiate(F, x), f)


# ---------------------------------------------------------------------------
# 定积分：∫_a^b（遵架构 §6.3）
# ---------------------------------------------------------------------------

def _require_rational(t, tag):
    tf = fold(t)
    if not T.is_num(tf):
        raise IntegrateError(f"积分{tag}需有理数（代数限需 ℚ(α)，未建）",
                             Reason.FRAGMENT)
    return T.num_val(tf)


def _ftc(F, x: Sym, a, b):
    """牛莱：F(b) − F(a)（F 为多项式原函数，端点精确求值）。"""
    Fa = fold(T.subst(F, {x: T.N(a)}))
    Fb = fold(T.subst(F, {x: T.N(b)}))
    return fold(T.plus(Fb, T.neg(Fa)))


def _rat_iso(iso, tag):
    """隔离区间 → 有理端点；无理根拒答（需 ℚ(α)）。None 为无界。"""
    if iso is None:
        return None
    a, b = iso
    if a == b:
        return a
    raise IntegrateError(f"分界点为无理根，需 ℚ(α) 精确定位（{tag}）",
                         Reason.FRAGMENT)


def definite_integrate(f, x: Sym, a, b):
    """∫_a^b f dx（a、b 为有理数项）。缺口不对 0 积分，未定义即拒。"""
    ar = _require_rational(a, "下限")
    br = _require_rational(b, "上限")
    if ar > br:
        raise IntegrateError("积分下限大于上限")
    if ar == br:
        return T.ZERO                          # ∫_a^a = 0（牛莱约定）
    from cas.piecewise import is_piecewise
    if is_piecewise(f):
        return _definite_piecewise(f, x, ar, br)
    F = integrate_term(f, x)
    return _ftc(F, x, ar, br)


def _definite_piecewise(f, x: Sym, a, b):
    """分段定积分：对覆盖 [a, b] 的每个开区间胞腔逐段牛莱求和。

    任一与 [a, b] 相交的胞腔未定义（缺口/点洞）即拒——绝不悄悄缩区间，
    也不对缺口积出 0。"""
    from cas.piecewise import domain_cells
    total = None
    for cell, val in domain_cells(f, x):
        lo = _rat_iso(cell.lo, "下界")
        hi = _rat_iso(cell.hi, "上界")
        if cell.kind == "point":
            r = lo
            if a <= r <= b and val is _UNDEF:
                raise IntegrateError("被积函数在 [a, b] 内存在未定义点洞，"
                                     "反常积分需极限层，未建", Reason.FRAGMENT)
            continue                                # 点胞腔测度 0
        L = a if lo is None else max(a, lo)
        R = b if hi is None else min(b, hi)
        if L >= R:
            continue
        if val is _UNDEF:
            raise IntegrateError("被积函数在 [a, b] 内存在缺口，不对缺口积分",
                                 Reason.FRAGMENT)
        t = _ftc(integrate_term(val, x), x, L, R)
        total = t if total is None else fold(T.plus(total, t))
    if total is None:
        raise IntegrateError("积分区间与定义域无交，无定义而非 0",
                             Reason.FRAGMENT)
    return total
