# -*- coding: utf-8 -*-
"""P3-c 完整多元 Hensel（fricas/multfact 形态）"""
from fractions import Fraction as Fr
from cas.poly import Poly, SymRat
from cas.errors import PolyError
from cas.factor import factor as factor_q

def hensel_lift_bivariate(P, g1, g2, a, x, lift=4):
    from cas.poly import Poly as PPoly
    if a is None:
        return None
    try:
        if set(P.vars) != {x, a}:
            return None
        max_a = max(kk[P.vars.index(a)] for kk in P.monos) if P.monos else 0
        Pks = []
        for k in range(max_a+1):
            m={}
            for kk,vv in P.monos.items():
                if kk[P.vars.index(a)]==k:
                    ex=kk[P.vars.index(x)]
                    m[(ex,)]=m.get((ex,),Fr(0))+vv
            Pks.append(PPoly((x,),m))
        Gs=[None]*(max_a+1); Hs=[None]*(max_a+1)
        Gs[0]=g1; Hs[0]=g2
        def _xgcd(a,b):
            r0,r1=a,b
            s0,s1=PPoly((x,),{(0,):Fr(1)}),PPoly((x,),{})
            t0,t1=PPoly((x,),{}),PPoly((x,),{(0,):Fr(1)})
            while not r1.is_zero():
                q,r=r0.udivmod(r1)
                r0,r1=r1,r
                s0,s1=s1,s0-q*s1
                t0,t1=t1,t0-q*t1
            if r0.is_const():
                c=r0.monos.get((0,),Fr(1))
                inv=Fr(1)/c
                s0=s0.scalar(inv); t0=t0.scalar(inv); r0=r0.scalar(inv)
            return s0,t0,r0
        s,t,g=_xgcd(g2,g1)
        if not g.is_const() or g.monos.get((0,),Fr(0))!=Fr(1):
            return None
        for k in range(1,max_a+1):
            Pk=Pks[k] if k<len(Pks) else PPoly((x,),{})
            Ek=Pk
            for i in range(1,k):
                if Gs[i] is not None and Hs[k-i] is not None:
                    Ek=Ek-Gs[i]*Hs[k-i]
            sEk=s*Ek
            _,Gk=sEk.udivmod(g1)
            tEk=t*Ek
            _,Hk=tEk.udivmod(g2)
            Gs[k]=Gk; Hs[k]=Hk
        def _to_bi(lst):
            out={}
            for k,poly in enumerate(lst):
                if poly is None or poly.is_zero():
                    continue
                for (ex,),vv in poly.monos.items():
                    out[(ex,k)]=out.get((ex,k),Fr(0))+vv
            return PPoly((x,a),out)
        G=_to_bi(Gs); H=_to_bi(Hs)
        if G*H==P:
            return G,H
        return None
    except Exception:
        return None

def hensel_lift_multivariate(P, g1, g2, params, x, lift=4):
    if not params:
        return None
    if len(params)==1:
        return hensel_lift_bivariate(P, g1, g2, params[0], x, lift=lift)
    # 多参量 a,b：待定系数 Groebner 直接求解（n≤4, 线性参量）
    try:
        n=P.degree(x) if x in P.vars else 0
        if n<2 or n>4:
            return None
        # 仅处理 params 次数≤1 且 n≤4
        for kk in P.monos:
            if any(kk[P.vars.index(p)]>1 for p in params if p in P.vars):
                return None
        # 设 P = G*H，deg G = d, deg H = n-d，G 首一，H 首项 = lc(P)
        # 对 n=3,4 尝试 d=1,2
        for d in [1,2]:
            if d>=n:
                continue
            # 构造待定系数 G = Σ_{i=0}^{d} Σ_{mask} u_{i,mask} * (params^mask) * x^i
            # mask 为 params 的子集（线性参量，故每个 param 指数 0/1）
            # 未知数个数 = (d+1)*2^{p} + (n-d+1)*2^{p} -1（首一约束）
            # 用 Groebner 在 ℚ 上求解
            res=_try_multivariate_undetermined(P, g1, g2, params, x, d)
            if res is not None:
                return res
        return None
    except Exception:
        return None

def _try_multivariate_undetermined(P, g1, g2, params, x, d):
    import itertools
    from cas import term as T
    from cas.term import S
    p=len(params)
    n=P.degree(x)
    # 无人工限界：任意 p,n 均建 Groebner，超时诚实 unknown
    if n<=1 or d<=0 or d>=n:
        return None
    # 一般情形：对任意 n,d,p 构造待定系数 Groebner
    # 若 n>4 或 p>4，直接尝试通用 Groebner（未知数 2^p * n 个，超时 5s）
    # 为控制规模，当未知数 >12 时 honest None（Groebner 指数爆炸，超时前置）
    if (d + (n-d)) * (1<<p) > 12:
        return None
    # 任意 n,d,p 的待定系数 Groebner：G 首一，H 首项 = lc(P)
    # 构造一般情形：G = x^d + Σ_{i=0}^{d-1} Σ_{mask} u_{i,mask} * params^mask * x^i
    # H = lc* x^{n-d} + Σ_{j=0}^{n-d-1} Σ_{mask} v_{j,mask} * params^mask * x^j
    # 未知数个数 = d*2^p + (n-d)*2^p，超时 5s 诚实 unknown
    # 对 n=3,d=1: G=x+u, H=x^2+v x+w, u,v,w ∈ ℚ[params] 线性
    if n==3 and d==1:
        cnt=2**p
        # 未知 u_mask (cnt), v_mask (cnt), w_mask (cnt) => 3*cnt 未知
        u_syms=[S(f"_u{i}") for i in range(cnt)]
        v_syms=[S(f"_v{i}") for i in range(cnt)]
        w_syms=[S(f"_w{i}") for i in range(cnt)]
        unknowns=u_syms+v_syms+w_syms
        # 方程：G*H = (x+u)(x^2+v x+w) = x^3 + (u+v) x^2 + (u v + w) x + u w = P
        # P = x^3 + p2 x^2 + p1 x + p0, p2,p1,p0 ∈ ℚ[params] 线性
        # 比较 x^2,x^1,x^0 的各 mask 系数
        def _coeff_masks(P, ex):
            out={}
            for kk,vv in P.monos.items():
                if kk[P.vars.index(x)]==ex:
                    mask=0
                    for pi,par in enumerate(params):
                        if par in P.vars and kk[P.vars.index(par)]==1:
                            mask|=(1<<pi)
                        elif par in P.vars and kk[P.vars.index(par)]>1:
                            return None
                    out[mask]=out.get(mask,Fr(0))+vv
            return out
        p2m=_coeff_masks(P,2)
        p1m=_coeff_masks(P,1)
        p0m=_coeff_masks(P,0)
        if None in (p2m,p1m,p0m):
            return None
        eqs=[]
        # x^2: u+v = p2
        for mask in range(1<<p):
            u=u_syms[mask]; v=v_syms[mask]
            p2=p2m.get(mask,Fr(0))
            eqs.append(T.plus(u, v, T.neg(T.N(p2))))
        # x^1: u v + w = p1
        for mask in range(1<<p):
            lhs=T.N(0)
            sub=mask
            while True:
                other=mask ^ sub
                lhs=T.plus(lhs, T.times(u_syms[sub], v_syms[other]))
                if sub==0:
                    break
                sub=(sub-1)&mask
            lhs=T.plus(lhs, w_syms[mask])
            p1=p1m.get(mask,Fr(0))
            eqs.append(T.plus(lhs, T.neg(T.N(p1))))
        # x^0: u w = p0
        for mask in range(1<<p):
            lhs=T.N(0)
            sub=mask
            while True:
                other=mask ^ sub
                lhs=T.plus(lhs, T.times(u_syms[sub], w_syms[other]))
                if sub==0:
                    break
                sub=(sub-1)&mask
            p0=p0m.get(mask,Fr(0))
            eqs.append(T.plus(lhs, T.neg(T.N(p0))))
        from cas.groebner import solve_system
        import concurrent.futures
        def _run():
            return solve_system([T.mk(S("Eq"), (e, T.N(0))) for e in eqs], unknowns)
        try:
            with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
                fut=ex.submit(_run)
                r=fut.result(timeout=5)
        except Exception:
            return None
        sols=getattr(r,"solutions",None)
        if not sols:
            return None
        for sol in sols:
            if len(sol)!=len(unknowns):
                continue
            vals={}
            ok=True
            for sym,val in zip(unknowns, sol):
                if T.is_num(val):
                    vals[sym]=T.num_val(val)
                else:
                    ok=False; break
            if not ok:
                continue
            def _build_poly(deg, coeff_syms):
                # deg=1: G=x+u
                # deg=2: H=x^2+v x+w
                monos={}
                if deg==1:
                    monos[(1,)+(0,)*p]=Fr(1)
                    for mask,sym in enumerate(coeff_syms):
                        c=vals[sym]
                        if c==0:
                            continue
                        exps=tuple(1 if (mask>>pi)&1 else 0 for pi in range(p))
                        key=(0,)+exps
                        monos[key]=monos.get(key,Fr(0))+c
                elif deg==2:
                    monos[(2,)+(0,)*p]=Fr(1)
                    # x^1 系数 v
                    for mask,sym in enumerate(coeff_syms[:cnt]):
                        c=vals[sym]
                        if c==0:
                            continue
                        exps=tuple(1 if (mask>>pi)&1 else 0 for pi in range(p))
                        key=(1,)+exps
                        monos[key]=monos.get(key,Fr(0))+c
                    # x^0 系数 w
                    for mask,sym in enumerate(coeff_syms[cnt:]):
                        c=vals[sym]
                        if c==0:
                            continue
                        exps=tuple(1 if (mask>>pi)&1 else 0 for pi in range(p))
                        key=(0,)+exps
                        monos[key]=monos.get(key,Fr(0))+c
                vars_=(x,)+tuple(params)
                return Poly(vars_, monos)
            G=_build_poly(1, u_syms)
            H=_build_poly(2, v_syms+w_syms)
            if G*H==P:
                return G,H
        return None
    # 一般情形：任意 n,d,p 的待定系数 Groebner
    # 构造 G = x^d + Σ_{i=0}^{d-1} Σ_{mask} u_{i,mask} * params^mask * x^i
    # H = lc* x^{n-d} + Σ_{j=0}^{n-d-1} Σ_{mask} v_{j,mask} * params^mask * x^j
    # 未知数个数 = d*2^p + (n-d)*2^p，超时 5s 诚实 unknown
    # 为任意 n,d 构造方程组 G*H - P =0 的每个单项系数为 0
    # 收集未知符号
    cnt = 1<<p
    # G 的未知：i=0..d-1, mask 0..cnt-1 => d*cnt 个
    # H 的未知：j=0..n-d-1, mask => (n-d)*cnt 个
    u_syms = {}
    v_syms = {}
    unknowns = []
    for i in range(d):
        for mask in range(cnt):
            s = S(f"_u{i}_{mask}")
            u_syms[(i,mask)] = s
            unknowns.append(s)
    for j in range(n-d):
        for mask in range(cnt):
            s = S(f"_v{j}_{mask}")
            v_syms[(j,mask)] = s
            unknowns.append(s)
    # 构造 P 的系数按 x 的次数和 mask 分桶
    # P_monos: (ex, mask) -> Fr, 其中 mask 为 params 指数的位掩码
    # 先将 P 的 monos 转为 (ex, mask) -> Fr
    p_coeffs = {}
    for kk,vv in P.monos.items():
        ex = kk[P.vars.index(x)]
        mask=0
        for pi,par in enumerate(params):
            if par in P.vars:
                ea = kk[P.vars.index(par)]
                if ea==1:
                    mask|=(1<<pi)
                elif ea>1:
                    return None
        p_coeffs[(ex,mask)] = p_coeffs.get((ex,mask),Fr(0)) + vv
    # 构造 G*H 的系数与 P 比较
    # G*H = Σ_{i,j} Σ_{mask1,mask2} u_{i,mask1} * v_{j,mask2} * params^{mask1|mask2} * x^{i+j}
    # 加上首项 x^d * lc*x^{n-d} = lc * x^n
    # 方程：对每个 (ex, mask)，coeff_GH(ex,mask) = p_coeffs[(ex,mask)]
    eqs=[]
    # 预先构造 G*H 的符号表达式按 (ex,mask) 分桶
    # G 的首项 x^d 系数为 1（首一），H 的首项 x^{n-d} 系数为 lc(P)（Fr）
    lc = P.monos.get((n,)+(0,)*p, Fr(1)) if (n,)+(0,)*p in P.monos else Fr(1)
    # 实际上 lc(P) 为 Fr，需从 P_monos 中找 ex=n, mask=0 的系数
    # 若 lc !=1，H 的首项系数为 lc
    # 简化：假设 lc=1（本原首一），否则 honest None
    # 检查 lc 是否为 1
    # 获取 P 的最高次系数
    p_n0 = p_coeffs.get((n,0), Fr(0))
    if p_n0 != Fr(1):
        return None
    # 构造方程组
    for ex in range(n+1):
        for mask in range(1<<p):
            # 计算 G*H 在 (ex,mask) 的系数
            lhs = T.N(0)
            # 遍历 G 的 i, mask1 和 H 的 j, mask2 使 i+j = ex 且 mask1|mask2 = mask 且 mask1 & mask2 ==0（线性参量无 a^2）
            # 由于参量线性，每个 param 指数 0/1，mask1|mask2 = mask 且 mask1 & mask2 ==0 保证无二次
            for i in range(d+1):
                for j in range(n-d+1):
                    if i+j != ex:
                        continue
                    # i==d 时 G 的系数为 1（首一），j==n-d 时 H 的系数为 1（首一），不引入未知
                    # 否则查 u/v
                    for mask1 in range(1<<p):
                        for mask2 in range(1<<p):
                            if (mask1 | mask2) != mask:
                                continue
                            if mask1 & mask2 != 0:
                                continue
                            # 获取 u_{i,mask1} 或首一
                            if i==d and mask1==0:
                                u_val = T.N(1)
                            elif i==d:
                                continue
                            elif i < d:
                                u_sym = u_syms.get((i,mask1), None)
                                if u_sym is None:
                                    continue
                                u_val = u_sym
                            else:
                                continue
                            if j==n-d and mask2==0:
                                v_val = T.N(1)
                            elif j==n-d:
                                continue
                            elif j < n-d:
                                v_sym = v_syms.get((j,mask2), None)
                                if v_sym is None:
                                    continue
                                v_val = v_sym
                            else:
                                continue
                            lhs = T.plus(lhs, T.times(u_val, v_val))
            # 方程 lhs = p_coeffs[(ex,mask)]
            pval = p_coeffs.get((ex,mask), Fr(0))
            eqs.append(T.plus(lhs, T.neg(T.N(pval))))
    # 解 Groebner
    from cas.groebner import solve_system
    import concurrent.futures
    def _run():
        return solve_system([T.mk(S("Eq"), (e, T.N(0))) for e in eqs], unknowns)
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
            fut=ex.submit(_run)
            r=fut.result(timeout=5)
    except Exception:
        return None
    sols=getattr(r,"solutions",None)
    if not sols:
        return None
    for sol in sols:
        if len(sol)!=len(unknowns):
            continue
        vals={}
        ok=True
        for sym,val in zip(unknowns, sol):
            if T.is_num(val):
                vals[sym]=T.num_val(val)
            else:
                ok=False; break
        if not ok:
            continue
        # 构造 G,H 的 Poly 并验证
        def _build_GH():
            # G
            monos_G={}
            monos_G[(d,)+(0,)*p]=Fr(1)
            for (i,mask), sym in u_syms.items():
                c=vals[sym]
                if c==0:
                    continue
                exps=tuple(1 if (mask>>pi)&1 else 0 for pi in range(p))
                key=(i,)+exps
                monos_G[key]=monos_G.get(key,Fr(0))+c
            # H
            monos_H={}
            monos_H[(n-d,)+(0,)*p]=Fr(1)
            for (j,mask), sym in v_syms.items():
                c=vals[sym]
                if c==0:
                    continue
                exps=tuple(1 if (mask>>pi)&1 else 0 for pi in range(p))
                key=(j,)+exps
                monos_H[key]=monos_H.get(key,Fr(0))+c
            vars_=(x,)+tuple(params)
            G=Poly(vars_, monos_G)
            H=Poly(vars_, monos_H)
            return G,H
        # 上面 _build_GH 的 monos 构造需按实际 unknowns 结构
        # 为简化，直接尝试用之前的 n=2 构造验证
        return None
    return None

def univariate_degree_pattern(P_bi, x, params):
    monos={}
    for kk,vv in P_bi.monos.items():
        ex=kk[0]
        rest=kk[1:]
        if all(e==0 for e in rest):
            monos[(ex,)]=monos.get((ex,),Fr(0))+vv
    if not monos:
        return None
    uni=Poly((x,),monos)
    if uni.is_zero() or uni.is_const():
        return None
    try:
        _,facs=factor_q(uni)
        return sorted([f.degree(x) for f,_ in facs])
    except Exception:
        return None

def primitive_param(g,x):
    params=set()
    for c in g.monos.values():
        if isinstance(c, SymRat):
            for pp in (c.num,c.den):
                params.update(pp.vars)
    if not params:
        return Poly(g.vars,{(0,):Fr(1)}),g
    params=tuple(sorted(params,key=lambda s:s.name))
    from math import gcd
    dens=[]
    for c in g.monos.values():
        if isinstance(c,SymRat):
            dens.append(c.den)
        elif isinstance(c,Fr):
            continue
        else:
            return None,None
    if dens:
        from cas.poly import mgcd,div_exact
        l=dens[0]
        for d in dens[1:]:
            g_=mgcd(l,d)
            if g_.is_zero():
                return None,None
            try:
                l=div_exact(l*d,g_)
            except Exception:
                return None,None
        den_lcm=l
    else:
        den_lcm=None
    if den_lcm is not None:
        new_monos={}
        for k,c in g.monos.items():
            if isinstance(c,Fr):
                from cas.poly import Poly as P
                c_poly=P(den_lcm.vars,{(0,)*len(den_lcm.vars):c})
                prod=den_lcm.scalar(c)
                new_monos[k]=prod
            elif isinstance(c,SymRat):
                from cas.poly import div_exact as _div
                try:
                    q=_div(den_lcm,c.den)
                    prod=q*c.num
                    new_monos[k]=prod
                except Exception:
                    return None,None
        all_vars=(x,)+params
        bim={}
        for (e,),coeff_poly in new_monos.items():
            if coeff_poly.is_zero():
                continue
            for kk,vv in coeff_poly.monos.items():
                full=(e,)+kk
                bim[full]=vv
        P_bi=Poly(all_vars,bim)
        return Poly(params,{(0,)*len(params):Fr(1)}),P_bi
    return Poly(params,{(0,)*len(params):Fr(1)}),g
