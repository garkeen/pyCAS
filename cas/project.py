# -*- coding: utf-8 -*-
"""域投影层：表达式属于哪个域由投影赋予，不做叶嗅探。

投影 = 按声明序的成员测试阶梯：ℚ → K[x₁..xₙ] → K(x₁..xₙ)。
命中即返回（域对象 + 域内元素）；全部落空返回 None——调用方据此
拒答或升级到更高结构（代数塔/超越塔，待地基完工后挂入本阶梯）。

变元序取自由符号的字典序：同一表达式投影结果确定。将来塔结构加入后，
阶梯在塔上继续生长，本协议不变。
"""

from dataclasses import dataclass

from cas import term as T
from cas.domains.q import QDomain
from cas.domains.z import Z_DOMAIN
from cas.domains.poly import poly_domain, from_term as poly_from_term, Poly, to_term
from cas.domains.ratfunc import ratfunc_domain, rf_from_term, RatFunc, rf_reduce

_Q_DOMAIN = QDomain()


@dataclass(frozen=True, slots=True)
class Projected:
    """投影结果：域对象 + 域内元素表示 + 原项。"""
    domain: object          # Domain 实例
    element: object         # Poly | RatFunc（ℚ 时为 None，直接看 term）
    term: object            # 原驻留项
    name: str               # 域名（步骤归属展示用）


def _vars_of(t):
    return tuple(sorted(T.free_vars(t), key=lambda s: s.name))


def project(t) -> Projected | None:
    """按成员测试阶梯投影。非成员全部落空返回 None（诚实，不猜）。"""
    vs = _vars_of(t)
    if not vs:
        if Z_DOMAIN.member(t):
            return Projected(Z_DOMAIN, None, t, Z_DOMAIN.name)
        if _Q_DOMAIN.member(t):
            return Projected(_Q_DOMAIN, None, t, _Q_DOMAIN.name)
        return None
    pd = poly_domain(*vs)
    p = poly_from_term(pd.ring, t, vs)
    if p is not None:
        return Projected(pd, p, t, pd.name)
    rfd = ratfunc_domain(*vs)
    r = rf_from_term(rfd.ring, t, vs)
    if r is not None:
        return Projected(rfd, r, t, rfd.name)
    return None


def is_zero(hit: Projected) -> bool:
    """投影元素判零（域标准形比较，片段内完全判定）。"""
    if hit.element is None:                 # 常数格（ℤ/ℚ）：直接看项
        from cas.qarith import fold
        f = fold(hit.term)
        return T.is_num(f) and T.num_val(f) == 0
    if isinstance(hit.element, Poly):
        return hit.element.is_zero()
    if isinstance(hit.element, RatFunc):
        return hit.element.num.is_zero()
    raise TypeError(f"unknown projected element {hit.element!r}")


def normalize(hit: Projected):
    """投影元素 → 域标准形驻留项。"""
    if hit.element is None:                 # 常数格（ℤ/ℚ）
        from cas.qarith import fold
        return fold(hit.term)
    if isinstance(hit.element, Poly):
        return to_term(hit.domain.ring, hit.element)
    if isinstance(hit.element, RatFunc):
        rf = rf_reduce(hit.domain.ring, hit.element)
        nt = to_term(hit.domain.ring, rf.num)
        dt = to_term(hit.domain.ring, rf.den)
        if T.is_num(dt) and T.num_val(dt) == 1:
            return nt
        return T.mk(T.S("Times"), (nt, T.pw(dt, T.N(-1))))
    raise TypeError(f"unknown projected element {hit.element!r}")


def zero_of(t):
    """t 的投影判零快捷通道：True/False/None（非成员，片段外不答）。"""
    hit = project(t)
    if hit is None:
        return None
    return is_zero(hit)
