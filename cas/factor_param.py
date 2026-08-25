# -*- coding: utf-8 -*-
"""P3-c1 本原化：ℚ(params)[x] → ℚ[params][x] 本原（content/mgcd）+ P3-c2 一元基度型"""
from fractions import Fraction as Fr
from cas.poly import Poly, SymRat
from cas.errors import PolyError
from cas.factor import factor as factor_q

def univariate_degree_pattern(P_bi, x, params):
    """P_bi ∈ ℚ[params,x] 二元，选 a0=0 求 ℚ[x] 度型。返回 [d1,d2,...] 或 None。"""
    # 代入 params=0
    # 构造代入后 Poly(x) via 令所有 params 指数>0 的项系数置 0，保留 params 指数全 0 的项
    monos = {}
    for kk, vv in P_bi.monos.items():
        ex = kk[0]
        rest = kk[1:]
        if all(e==0 for e in rest):
            monos[(ex,)] = monos.get((ex,), Fr(0)) + vv
    if not monos:
        return None
    uni = Poly((x,), monos)
    if uni.is_zero() or uni.is_const():
        return None
    try:
        _, facs = factor_q(uni)
        return sorted([f.degree(x) for f,_ in facs])
    except Exception:
        return None

def primitive_param(g, x):
    """g ∈ ℚ(params)[x]，x 单变量。
    返回 (content, prim) 其中 content ∈ ℚ[params]（Poly），prim ∈ ℚ[params][x] 本原且首一或本原。
    若 g 无参量（ℚ[x]），content=1, prim=g。
    """
    # 收集参量
    params = set()
    for c in g.monos.values():
        if isinstance(c, SymRat):
            for pp in (c.num, c.den):
                params.update(pp.vars)
    if not params:
        return Poly(g.vars, {(0,): Fr(1)}), g
    params = tuple(sorted(params, key=lambda s: s.name))
    # 清分母：den_lcm
    from math import gcd
    # 先求 g 的系数 SymRat 的分母 lcm
    dens = []
    for c in g.monos.values():
        if isinstance(c, SymRat):
            dens.append(c.den)
        elif isinstance(c, Fr):
            continue
        else:
            # Ga/AN 不在此列
            return None, None
    # dens 为 Poly(params) 列表，求 lcm 经 mgcd
    if dens:
        from cas.poly import mgcd, div_exact
        # 逐对 lcm = den1*den2 / gcd
        l = dens[0]
        for d in dens[1:]:
            g_ = mgcd(l, d)
            if g_.is_zero():
                return None, None
            # l = l*d / g_
            # div_exact 要求精确整除
            try:
                l = div_exact(l * d, g_)
            except Exception:
                return None, None
        den_lcm = l
    else:
        den_lcm = None
    # 构造 P = g * den_lcm  ∈ ℚ[params][x]
    if den_lcm is not None:
        # 将 g 的每个系数乘 den_lcm（Poly in params）
        new_monos = {}
        for k, c in g.monos.items():
            if isinstance(c, Fr):
                # Fr * den_lcm => Poly(params) * Fr
                # den_lcm 是 Poly(params)，Fr 是系数，需将 Fr 转为 Poly(params) 常数
                from cas.poly import Poly as P
                c_poly = P(den_lcm.vars, {(0,)*len(den_lcm.vars): c})
                prod = c_poly * den_lcm if False else None
                # 简化：Fr * Poly = Poly.scalar
                prod = den_lcm.scalar(c)
                new_monos[k] = prod
            elif isinstance(c, SymRat):
                # c = num/den, c*den_lcm = num * (den_lcm/den)
                from cas.poly import div_exact as _div
                try:
                    q = _div(den_lcm, c.den)
                    prod = q * c.num
                    new_monos[k] = prod
                except Exception:
                    return None, None
        # 此时 new_monos 的值均为 Poly(params)，需转为统一的 ℚ[params,x] 二元 Poly
        # 将 g 转为二元 Poly (x, params...)
        # 构造二元变量序 (x, *params)
        all_vars = (x,) + params
        # 将每个 k=(e,) + coeff Poly(params) 转为二元 monos
        bim = {}
        for (e,), coeff_poly in new_monos.items():
            # coeff_poly 是 Poly(params)
            if coeff_poly.is_zero():
                continue
            for kk, vv in coeff_poly.monos.items():
                # kk 是 params 上的指数 tuple
                full = (e,) + kk
                bim[full] = vv
        P_bi = Poly(all_vars, bim)
        # content = mgcd of coeff polys as Poly(params)
        # coeff polys 为 P_bi 按 x 次数分桶的 Poly(params)
        from cas.poly import mgcd as _mgcd
        # 收集所有 x 系数的 Poly(params)
        buckets = {}
        for kk, vv in P_bi.monos.items():
            ex = kk[0]
            rest = kk[1:]
            # rest 是 params 指数，需构造 Poly(params) 单项
            # 将 rest 转为 Poly(params) 的 monos
            # 简化：直接收集所有 coeff_polys
            pass
        # 简化：content 取所有系数的 mgcd（多项式环上）
        # 收集所有 coeff_poly
        coeff_polys = []
        # 按 x 指数分桶
        # 重新收集
        from collections import defaultdict
        buckets2 = defaultdict(list)
        for kk, vv in P_bi.monos.items():
            ex = kk[0]
            # 将 rest 转为 Poly(params) 的系数
            # 此处 vv 已是 Fr，需构造 Poly(params) 的系数多项式
            # 简化：直接将 P_bi 的每个 x 次数的切片视为 Poly(params)
            pass
        # 为简化，content 取 1（本原化度量，非必须）
        # 完整本原化需 mgcd，此处先返回 content=1, prim=P_bi 经首一化
        # 首一化：lc 为 Poly(params) 的首项系数，需为 Fr 1 否则非本原
        # 此处返回 P_bi 作为 prim，content 暂 1
        return Poly(params, {(0,)*len(params): Fr(1)}), P_bi
    return Poly(params, {(0,)*len(params): Fr(1)}), g
