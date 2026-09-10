# -*- coding: utf-8 -*-
"""域投影层：表达式属于哪个域由投影赋予，不做叶嗅探。

投影 = 按声明序的成员测试阶梯：ℚ → K[x₁..xₙ] → K(x₁..xₙ)。
命中即返回（域对象 + 域内元素）；全部落空返回 None——调用方据此
拒答或升级到更高结构（代数塔/超越塔，待地基完工后挂入本阶梯）。

变元序取自由符号的字典序：同一表达式投影结果确定。将来塔结构加入后，
阶梯在塔上继续生长，本协议不变。

常驻基域（ℤ/ℚ/ℚ(i)）的**装配点已上移到 bootstrap**（math/domains/module.py
经 builder 建域、本模块经 bind_domains 绑定单例）：import 本层零副作用。
分工理由见 cas/math/domains/__init__.py 的模块串——核心是 ℚ(i) 必须注入
已声明的 i 常数，而域包只依赖 cas.syntax.term，拿不到常数声明。
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.math.domains.base import register, lookup
from cas.math.domains.q import Q_DOMAIN
from cas.math.domains.z import Z_DOMAIN
from cas.math.domains.qi import QIDomain
from cas.math.domains.poly import poly_domain, from_term as poly_from_term, Poly, to_term
from cas.math.domains.ratfunc import ratfunc_domain, rf_from_term, RatFunc, rf_reduce, rf_to_term

# 常驻基域由 bootstrap 显式装配（v4 §7.1）——原先本模块在 import 期注册并
# lookup 回填单例，注册表内容因此取决于「谁碰巧被 import」。现在 import 本模块
# 零副作用：未绑定时阶梯为空，投影一律落空（调用方拒答），不会静默用错域。
_Z_DOMAIN = None
_Q_DOMAIN = None
_QI_DOMAIN = None


def bind_domains(domains):
    """由 `bootstrap()` 装入常驻基域（ℤ / ℚ / ℚ(i)）并回填单例。

    ℝ(i) 的 `i` 身份在 `math/domains/module.py` 建域时已由 builder 注入——
    域由显式声明进入，不做名字嗅探（v4 §7.6）。
    """
    global _Z_DOMAIN, _Q_DOMAIN, _QI_DOMAIN
    for d in domains:
        if lookup(d.name) is None:
            register(d)
    _Z_DOMAIN = lookup(Z_DOMAIN.name)
    _Q_DOMAIN = lookup(Q_DOMAIN.name)
    _QI_DOMAIN = lookup(QIDomain.name)


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
        if _QI_DOMAIN.member(t):
            return Projected(_QI_DOMAIN, None, t, _QI_DOMAIN.name)
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
    """投影元素判零（域标准形比较，片段内完全判定）。

    常数格（ℤ/ℚ/ℚ(i)）经域判等裁决——对任意常数域统一，不按域
    类型特判：hit 的项是该域成员（投影命中保证），T.ZERO 是一切
    数域的成员，equal 即值比较。"""
    if hit.element is None:
        return hit.domain.equal(hit.term, T.ZERO) is True
    if isinstance(hit.element, Poly):
        return hit.element.is_zero()
    if isinstance(hit.element, RatFunc):
        return hit.element.num.is_zero()
    raise TypeError(f"unknown projected element {hit.element!r}")


def normalize(hit: Projected):
    """投影元素 → 域标准形驻留项。"""
    if hit.element is None:                 # 常数格（ℤ/ℚ/ℚ(i)）：域标准形
        return hit.domain.normalize(hit.term)
    if isinstance(hit.element, Poly):
        return to_term(hit.domain.ring, hit.element)
    if isinstance(hit.element, RatFunc):
        return rf_to_term(hit.domain.ring, rf_reduce(hit.domain.ring, hit.element))
    raise TypeError(f"unknown projected element {hit.element!r}")


def zero_of(t):
    """t 的投影判零快捷通道：True/False/None（非成员，片段外不答）。"""
    hit = project(t)
    if hit is None:
        return None
    return is_zero(hit)
