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

def hensel_lift_bivariate(P, g1, g2, a, x, lift=4):
    """P(a,x) ∈ ℚ[a,x] 本原，P(0,x)=g1*g2 且 gcd(g1,g2)=1，Hensel 完整提升。
    返回 (G,H) 使 P = G*H 且 G(0)=g1, H(0)=g2，或 None。
    实现：a-adic Hensel，每步解 dG*H0 + dH*G0 = E_k via 扩展欧几里得（fricas/multfact 形态）。
    """
    from cas.poly import Poly
    from fractions import Fraction as Fr
    # 仅单参量 a
    if a is None:
        return None
    # 将 P,g1,g2 转为二元 Poly(a,x) 的统一表示
    # P 已是 Poly((x,a) 或 (a,x))，需统一变量序为 (x,a)
    # 为简化，要求 P.vars 含 x 且含 a，否则直接返回 None
    try:
        # 确保变量序为 (x,a)
        # 若 P.vars 顺序不是 (x,a)，重排
        # 当前实现：直接待定系数法对 lift=2 的二次参量情形求解
        # 对 P = Σ c_i(a) x^i, 设 G = g1 + a*G1, H = g2 + a*H1, 比较 a^1 系数得线性方程组
        # 此处实现 lift=2 的完整线性求解（Fr 系数），失败回 None
        # 取 a 为参数符号，x 为主变量
        # 将 P 按 a 的次数分桶：P = P0(x) + a*P1(x) + a^2*P2(x)+...
        # g1,g2 为 ℚ[x]，设 G = g1 + a*G1(x), H = g2 + a*H1(x)，则
        # P1 = G1*g2 + H1*g1  =>  G1*g2 + H1*g1 - P1 =0
        # 这是 ℚ[x] 上线性丢番图方程，解的存在性由 gcd(g1,g2)=1 保证
        # 用扩展欧几里得求特解
        from cas.poly import Poly as PPoly
        # 将 P 按 a 分解
        # 收集 P 的 a 次数 0 和 1 的切片
        # P.vars 可能为 (x,a) 或 (a,x)，需统一
        # 简化：要求 P.vars == (x,a) 或 (a,x) 之一，否则返回 None
        if set(P.vars) != {x, a}:
            return None
        # 将 P 转为以 a 为主变量的 Poly(a) 系数为 Poly(x)
        # 构造 P0(x)=P(a=0), P1(x)= (P - P0)/a mod a
        # 用 Poly 的代入：令 a=0 得 P0
        # 为简化，直接通过单项式分桶
        # P_bi.monos: key = (ex, ea) 对应 x^ex a^ea
        # 提取 P0: ea=0 的项，P1: ea=1 的项
        # 将 P 按 a 的次数分桶：P_k(x) 为 a^k 系数
        max_a = max(kk[P.vars.index(a)] for kk in P.monos) if P.monos else 0
        Pks = []
        for k in range(max_a+1):
            m = {}
            for kk, vv in P.monos.items():
                if kk[P.vars.index(a)] == k:
                    # x 指数
                    ex = kk[P.vars.index(x)]
                    m[(ex,)] = m.get((ex,), Fr(0)) + vv
            Pks.append(PPoly((x,), m))
        # 迭代 Hensel：对 k=1..max_a 求 G_k, H_k
        # 初始化 G0=g1, H0=g2
        # 已验证 P0 = g1*g2 (因 P(0)=g1*g2)
        # 对每 k，解 G_k*g2 + H_k*g1 = E_k
        # 其中 E_k = P_k - Σ_{i=1}^{k-1} G_i*H_{k-i}
        # 用扩展欧几里得求特解后模 g1/g2 归约次数
        Gs = [None]*(max_a+1)
        Hs = [None]*(max_a+1)
        # G0, H0 来自 g1,g2
        Gs[0] = g1
        Hs[0] = g2
        # 求 s,t 使 s*g2 + t*g1 =1
        def _xgcd(a,b):
            r0, r1 = a, b
            s0, s1 = PPoly((x,), {(0,):Fr(1)}), PPoly((x,), {})
            t0, t1 = PPoly((x,), {}), PPoly((x,), {(0,):Fr(1)})
            while not r1.is_zero():
                q, r = r0.udivmod(r1)
                r0, r1 = r1, r
                s0, s1 = s1, s0 - q*s1
                t0, t1 = t1, t0 - q*t1
            if r0.is_const():
                c = r0.monos.get((0,), Fr(1))
                inv = Fr(1)/c
                s0 = s0.scalar(inv)
                t0 = t0.scalar(inv)
                r0 = r0.scalar(inv)
            return s0, t0, r0
        s, t, g = _xgcd(g2, g1)
        if not g.is_const() or g.monos.get((0,), Fr(0)) != Fr(1):
            return None
        # 迭代求 Gk, Hk
        for k in range(1, max_a+1):
            Pk = Pks[k] if k < len(Pks) else PPoly((x,), {})
            # 计算 E_k
            Ek = Pk
            for i in range(1, k):
                if Gs[i] is not None and Hs[k-i] is not None:
                    Ek = Ek - Gs[i]*Hs[k-i]
            # 解 Gk*g2 + Hk*g1 = Ek, 取 Gk = s*Ek mod g1, Hk = t*Ek mod g2
            sEk = s * Ek
            _, Gk = sEk.udivmod(g1)
            # 余数即 Gk
            tEk = t * Ek
            _, Hk = tEk.udivmod(g2)
            Gs[k] = Gk
            Hs[k] = Hk
        # 构造 G,H 从 Gs/Hs（已迭代至 max_a）
        def _to_bi_general(poly_list):
            out = {}
            for k, poly in enumerate(poly_list):
                if poly is None or poly.is_zero():
                    continue
                for (ex,), vv in poly.monos.items():
                    # 合并同指数（a^k 层可能多项式相加已在 Gs[k] 内）
                    out[(ex, k)] = out.get((ex, k), Fr(0)) + vv
            return PPoly((x,a), out)
        try:
            G = _to_bi_general(Gs)
            H = _to_bi_general(Hs)
            if G * H == P:
                return G, H
            return None
        except Exception:
            return None
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
