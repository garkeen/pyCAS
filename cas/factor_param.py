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
    if p>3 or n>4:
        return None
    # 对 n=3,d=1: G=x+u, H=x^2+v x+w, u,v,w ∈ ℚ[params] 线性
    # 对 n=3,d=1 且 p≤2，直接 Groebner
    if n==3 and d==1 and p<=2:
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
    if n==2 and d==1 and p<=2:
        # G = x + u0 + u1*a + u2*b (+ u3*a*b if p==2)
        # H = x + v0 + v1*a + v2*b (+ v3*a*b)
        # 未知 u_i, v_i
        # 方程：G*H = x^2 + (u+v) x + u v = P = x^2 + p1 x + p0
        # 其中 p1 = p1_0 + p1_a a + p1_b b + p1_ab a b, p0 类似
        # 比较 x^1 和 x^0 的 a,b 系数得方程组
        # 构造未知符号
        cnt = 2**p
        # G 低次系数 u_mask, H 低次 v_mask
        # 未知数列表
        u_syms = [S(f"_u{i}") for i in range(cnt)]
        v_syms = [S(f"_v{i}") for i in range(cnt)]
        unknowns = u_syms + v_syms
        # 构造 G*H 的系数与 P 比较
        # P 的系数按 x 的次数和 params mask 分桶
        # P_monomials: (ex, ea, eb) -> coeff Fr
        # G*H 的系数： (x+ Σ u_mask * a^{mask}) * (x+ Σ v_mask * a^{mask})
        # 展开后 x^1 系数 = u + v, x^0 系数 = u*v
        # 对每个 mask，方程为 u_mask + v_mask = p1_mask, Σ_{submask} u_sub * v_{mask^sub} = p0_mask
        # 构造方程组 terms
        # 获取 P 的 p1,p0 的各 mask 系数
        # P 的 monos: key (ex, ea, eb) -> Fr
        # 提取 p1_mask 和 p0_mask
        # p1 对应 ex=1, p0 对应 ex=0
        def _coeff_for(P, ex):
            out={}
            for kk,vv in P.monos.items():
                if kk[P.vars.index(x)]==ex:
                    # rest 为 params 指数
                    mask=0
                    for pi, par in enumerate(params):
                        if par in P.vars:
                            ea = kk[P.vars.index(par)]
                            if ea==1:
                                mask |= (1<<pi)
                            elif ea>1:
                                return None
                    out[mask]=vv
            return out
        # 简化：直接构造方程组 via Poly 比较
        # 构造 G*H - P 的每个单项系数为 0 的方程
        # 用 term 构造
        eqs=[]
        # 获取所有 mask 的 p1,p0
        p1_masks={}
        p0_masks={}
        for kk,vv in P.monos.items():
            ex=kk[P.vars.index(x)]
            mask=0
            for pi,par in enumerate(params):
                if par in P.vars and kk[P.vars.index(par)]==1:
                    mask|=(1<<pi)
            if ex==1:
                p1_masks[mask]=p1_masks.get(mask,Fr(0))+vv
            elif ex==0:
                p0_masks[mask]=p0_masks.get(mask,Fr(0))+vv
        # 方程：u_mask + v_mask = p1_mask
        for mask in range(1<<p):
            u = u_syms[mask]
            v = v_syms[mask]
            p1 = p1_masks.get(mask,Fr(0))
            eqs.append(T.plus(u, v, T.neg(T.N(p1))))
        # 方程：Σ_{sub} u_sub * v_{mask^sub} = p0_mask
        for mask in range(1<<p):
            lhs = T.N(0)
            sub = mask
            while True:
                # sub 遍历 mask 的子集
                other = mask ^ sub
                # u_sub * v_other
                lhs = T.plus(lhs, T.times(u_syms[sub], v_syms[other]))
                if sub==0:
                    break
                sub = (sub-1) & mask
            p0 = p0_masks.get(mask,Fr(0))
            eqs.append(T.plus(lhs, T.neg(T.N(p0))))
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
            # 构造 G,H 的 Poly
            # 将 sol 的 Fr 值代入
            vals={}
            ok=True
            for sym,val in zip(unknowns, sol):
                if T.is_num(val):
                    vals[sym]=T.num_val(val)
                else:
                    ok=False; break
            if not ok:
                continue
            # 构造 G = x + Σ u_mask * params^mask
            # 构造 H = x + Σ v_mask * params^mask
            # 验证 G*H == P
            # 构造 G_poly, H_poly 为 Poly((x,)+params) over Fr
            def _build_poly(coeff_syms):
                monos={}
                # x^1 系数 1
                monos[(1,)+(0,)*p]=Fr(1)
                # x^0 系数为 Σ coeff * params^mask
                for mask,sym in enumerate(coeff_syms):
                    c=vals[sym]
                    if c==0:
                        continue
                    # mask 转为 params 指数
                    exps=tuple(1 if (mask>>pi)&1 else 0 for pi in range(p))
                    # x^0 的项
                    key=(0,)+exps
                    monos[key]=monos.get(key,Fr(0))+c
                # 变量序 (x,)+params
                vars_=(x,)+tuple(params)
                return Poly(vars_, monos)
            G = _build_poly(u_syms)
            H = _build_poly(v_syms)
            if G*H == P:
                return G,H
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
