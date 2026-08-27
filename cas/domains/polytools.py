# -*- coding: utf-8 -*-
"""多项式公共零件（架构 4.1）：结式与无平方分解。

结式是残数法（Rothstein-Trager）与 CAD 投影的公共工具；
无平方分解（Yun）是因式分解与 Hermite 约化的前置。
二者都只在域系数、单变量上实现——子结式链与多元推广
在多元 GCD 就位后按同一接口升级。
"""

from cas.domains.poly import (Poly, p_zero, p_const, p_scale, p_sub,
                              p_divmod_field, p_gcd_univar, p_deriv,
                              _norm)


def p_deg(p: Poly, var_i: int = 0) -> int:
    return p.deg_in(var_i)


def p_lc(p: Poly, var_i: int = 0):
    """关于 var_i 的首项系数。零多项式无首项，调用方自保。"""
    top = max(p.monos, key=lambda kc: kc[0][var_i])
    return top[1]


def p_monic(ring, p: Poly, var_i: int = 0) -> Poly:
    if p.is_zero():
        return p
    return p_scale(ring, p, ring.div_exact(ring.from_int(1), p_lc(p, var_i)))


def p_div_exact(ring, a: Poly, b: Poly, var_i: int = 0) -> Poly:
    """精确除法：余式必须为零，否则调用方违约。"""
    q, r = p_divmod_field(ring, a, b, var_i)
    if not r.is_zero():
        raise ValueError("非精确除法")
    return q


def resultant(ring, a: Poly, b: Poly, var_i: int = 0):
    """结式 res(a, b)（域系数，余式序列递归）。

    性质：res = 0 ⟺ a, b 有公共根（非常数公因子）；
    res(x−r, f) = f(r)（符号约定锚点）。返回环元素。
    """
    if a.is_zero() or b.is_zero():
        return ring.from_int(0)
    s = ring.from_int(1)
    while True:
        m, n = p_deg(a, var_i), p_deg(b, var_i)
        if m < n:
            a, b = b, a
            m, n = n, m
            if (m * n) % 2:
                s = ring.neg(s)
        if n == 0:
            # res(a, c) = c^deg(a)
            c = b.monos[0][1] if not b.is_zero() else ring.from_int(0)
            return ring.mul(s, ring.pow_pos(c, m))
        _, r = p_divmod_field(ring, a, b, var_i)
        if r.is_zero():
            return ring.from_int(0)        # 有公因子
        if (m * n) % 2:
            s = ring.neg(s)
        lc = p_lc(b, var_i)
        s = ring.mul(s, ring.pow_pos(lc, m - p_deg(r, var_i)))
        a, b = b, r


def squarefree(ring, f: Poly):
    """Yun 无平方分解（特征零域）：返回 [(因子, 重数), ...]，因子 monic。

    Π 因子ᵢ^重数ᵢ == monic(f)。常数/零多项式返回空表。
    """
    if f.is_zero() or p_deg(f) == 0:
        return []
    f = p_monic(ring, f)
    df = p_deriv(ring, f, 0)
    g = p_gcd_univar(ring, f, df)
    w = p_div_exact(ring, f, g)
    y = p_div_exact(ring, df, g)
    z = p_sub(ring, y, p_deriv(ring, w, 0))
    out = []
    i = 1
    while p_deg(w) > 0:
        h = p_gcd_univar(ring, w, z)
        if p_deg(h) > 0:
            out.append((h, i))
            w = p_div_exact(ring, w, h)
        y = p_div_exact(ring, z, h) if p_deg(h) > 0 else z
        z = p_sub(ring, y, p_deriv(ring, w, 0))
        i += 1
    return out
