# -*- coding: utf-8 -*-
"""微分域塔·参数化判定件（自 cas/risch.py 拆出）：对数导数-根式判定
（is_logderiv_radical + 基级 _ldrad_base）、参数化对数导数 _pld_solve
三态、_limited_int_prim 比率定理。

M5 收官批 #1（参数化对数导数完备化）要点：系数约束统一为零空间线性
代数；全 τ-free 目标经结构定理下降（exp 层 v=c·τ^j·u 分解）；基级
z-常数兜底（有界本原对枚举 + 逐个精确验证）；'und' 显式上抛——
绝不把启发失败伪装成证明否定。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N, Expr, Sym, Const, ONE
from cas.poly import Poly
from cas.errors import PolyError
from cas.gaussian import Ga
from cas.univar import (from_poly, u_add, u_sub, u_mul, u_pow, u_deg,
                        u_trim, u_divmod, u_gcd, u_inv_mod,
                        u_formal_deriv, u_is_zero)
from cas.scalarutil import rf_const_ga, ga_den, lcm2, ga_vec_to_ints, mk_zero_like

from cas.risch_core import (
    RischUnsupported, _embed, _tower_deriv_frac, _frac_from_term,
)
from cas.risch_exp import (
    _poly_to_list, _neg_poly, _sylvester_res, _squarefree_decomp_t,
    _residue_sqfr, _constant_roots, _from_univar,
)
from cas.risch_rdesup import (_restrict, _make_der_fn, _dk_pair,
                              _split_ns)


def _const_to_term(c):
    return c.to_term() if hasattr(c, "to_term") else N(c)


def _rf_of_cs(cs, allv, tau):
    from cas.ratfunc import RatFunc as _RF
    n_, d_ = _from_univar(cs, allv, tau)
    return _RF(n_, d_)


def _cs_const_val(cs, allv):
    """univar list 是否整体为零多项式；非零时无意义（仅供零检查）。"""
    return all(c.is_zero() for c in cs)


def _ldrad_base(f_rf, de):
    """ℚ(i)(x) 上的对数导数-根式判定（base case，Poly 级实现）。

    f 真分式且分母无平方时：R(z)=Res_x(a−z·b',b) 的根全为 ℚ(i)
    常数 <=> ∃n,u: n·f=D(u)/u；n=lcm(残数分母)、u=Πg^{n·r}。
    """
    from cas.poly import ugcd as _pugcd
    from cas.factor import squarefree_decomp
    from math import lcm as _lcm3
    from cas.ratfunc import RatFunc

    def _uni_strip(p):
        if len(p.vars) <= 1:
            return p
        for k, _c in p.monos.items():
            if any(e != 0 for e in k[1:]):
                raise RischUnsupported(
                    "internal: base-level poly carries higher tower vars")
        return Poly((p.vars[0],),
                    {(k[0],): c for k, c in p.monos.items()})

    xv = de.levels[0]
    a = _uni_strip(f_rf.p)
    b = _uni_strip(f_rf.q)
    if a.is_zero():
        return 1, RatFunc.one((xv,))
    if b.degree(xv) == 0:
        return None                    # 无极点：非常数 f 不可能是 dlog
    if a.degree(xv) >= b.degree(xv):
        return None                    # 非真分式（多项式部分无处承载）
    try:
        parts = squarefree_decomp(b)
    except Exception:
        return None
    if len(parts) != 1 or parts[0][1] != 1:
        return None                    # 分母须无平方

    db = b.deriv(xv)
    la, lb, ldb = _poly_to_list(a), _poly_to_list(b), _poly_to_list(db)
    from cas.ratfunc import RatFunc as _RFb

    def _wrap_list(lst):
        return [_RFb.from_poly(Poly.const((xv,), v)) for v in lst]

    la, lb, ldb = _wrap_list(la), _wrap_list(lb), _wrap_list(ldb)
    nb = max(len(la), len(lb), len(ldb))
    lap = la + [_RFb.from_poly(Poly.const((xv,), Fr(0)))
                for _ in range(nb - len(la))]
    lbp = lb + [_RFb.from_poly(Poly.const((xv,), Fr(0)))
                for _ in range(nb - len(lb))]
    ldbp = ldb + [_RFb.from_poly(Poly.const((xv,), Fr(0)))
                  for _ in range(nb - len(ldb))]
    fz = [[aa, _neg_poly(dd)] for aa, dd in zip(lap, ldbp)]
    gz = [[cc] for cc in lbp]
    Rz = _sylvester_res(fz, gz)
    if u_is_zero(Rz):
        return None

    roots = _constant_roots(Rz, xv=xv)   # 无法判定 => 异常上抛（诚实）
    residueterms = []

    def _neg_val(v):
        if isinstance(v, Ga):
            return Ga(-v.re, -v.im)
        return -v

    for c in roots:
        diffp = a + db.scalar(_neg_val(c))
        g = _pugcd(diffp, b)
        if g.degree(xv) <= 0:
            continue
        dn_ = ga_den(c) if isinstance(c, Ga) else c.denominator
        residueterms.append((g, c, dn_))
    if not residueterms:
        return None
    n = 1
    for _, _, dn_ in residueterms:
        n = _lcm3(n, dn_)
    # u = Π g^{n·c}：负指数残数进分母（对数导数的极点合法形态；
    # 旧版一律乘分子，遇负残数 Poly 负幂直接炸——休眠 bug）
    u_num = Poly.one((xv,))
    u_den = Poly.one((xv,))
    for g, c, _dn in residueterms:
        ee = n * c
        if isinstance(ee, Ga):
            if ee.im != 0 or ee.re.denominator != 1:
                return None
            ee = ee.re
        if not isinstance(ee, int) and ee.denominator != 1:
            return None
        ee = int(ee)
        if ee >= 0:
            u_num = u_num * g ** ee if ee > 0 else u_num
        else:
            u_den = u_den * g ** (-ee)
    return _ld_finish(n, RatFunc(u_num, u_den), f_rf, de)


def _term_within_field(val_t, de, jl):
    """term 的 Log/Exp 参数是否全部落在允许塔层（≤jl）内。

    基层有理积分会以实形态吐 Log——若其参数恰为某允许层的原函数
    形态则该层符号可承载（合法），否则为域外泄漏。
    """
    allowed_args = []
    for i in range(1, jl + 1):
        tm = de.terms[i]
        if isinstance(tm, Expr) and len(tm.args) == 1:
            allowed_args.append(tm.args[0])
    stack = [val_t]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr) and u.head.name in ("Log", "Exp") \
                and len(u.args) == 1:
            if not any(u.args[0] == ag for ag in allowed_args):
                return False
            stack.extend(u.args)
            continue
        if isinstance(u, Expr):
            stack.extend(u.args)
    return True


def _limited_int_prim(al_rf, v_rf, de, jl, cap=16):
    """完备化版：α = m·η + D(z) 的共振界修正（M5 收官批 #2）。

    核心洞察（余陪集定理 + 多项式约束）：
    - η = D(τ) 在塔内恒可积（∫η = τ），故 k·η 可积 ⟺ η 可积
      ⟹ S₀ = {k : k·η 可积} ∈ {{0}, ℤ}
    - α = m·η + D(z)、z ∈ K₀[τ]（多项式）⟹ D(z)/η = D(z)/D(τ) 为常数
      ⟹ z = c·τ + const ⟹ α/η = m + c = 整数常数
    - 逆否：α/η 非整数常数 => 无多项式共振 => 朴素界正确

    故 α/η 的常数整数性检验是完备的——无需有界积分探测。

    三态：('ok', m)  m = 正整数共振度，或 0（无共振）
           ('und', None) 理论受限（仅 η=0 或比率计算异常的极端情形）
    """
    if v_rf.is_zero():
        return "ok", 0
    allv_sub = tuple(de.levels[:jl + 1])
    try:
        al_r = _restrict(al_rf, allv_sub)
        v_r = _restrict(v_rf, allv_sub)
    except PolyError:
        return "ok", 0
    try:
        rho = al_r / v_r
    except Exception:
        return "ok", 0
    cv = rf_const_ga(rho)
    if cv is not None and cv.im == 0 \
            and cv.re.denominator == 1 and cv.re > 0:
        return "ok", int(cv.re)
    return "ok", 0


def _is_logderiv_radical(f_rf, de, jv, depth=0):
    """主判定入口。f_rf: RatFunc over levels[:jv+1]，视图 τ=levels[jv]。"""
    from cas.ratfunc import RatFunc

    if depth > 8:
        return None
    if f_rf.is_zero():
        return 1, RatFunc.one(tuple(de.levels[:jv + 1]))

    if jv == 0:
        return _ldrad_base(f_rf, de)

    tau = de.levels[jv]
    allv = tuple(de.levels[:jv + 1])
    sub = tuple(de.levels[:jv])
    zero = RatFunc.zero(sub)
    one_c = zero.one(sub)
    der_fn = _make_der_fn(de, jv)

    # τ 不在变量集 => f ∈ K_{jv-1}：直接降层递归（结构定理模式）
    if tau not in f_rf.p.vars and tau not in f_rf.q.vars:
        return _is_logderiv_radical(f_rf, de, jv - 1, depth + 1)

    fn_cs = from_poly(f_rf.p, tau)
    fd_cs = from_poly(f_rf.q, tau)

    # ---- -1) τ-gcd 约分（未约分形态会污染残数结果式）----
    g0 = u_gcd(fn_cs, fd_cs, zero)
    if len(g0) > 1:
        fn_cs = u_divmod(fn_cs, g0, zero)[0]
        fd_cs = u_divmod(fd_cs, g0, zero)[0]

    # ---- 0) 分母须无平方（对数导数只有单极点）----
    sqf = _squarefree_decomp_t(fd_cs, zero)
    if any(e >= 2 for _, e in sqf):
        return None

    # ---- 1) 多项式部分 + 逐因子残数（复用 _integrate_normal 模式）----
    Q_cs, _R_all = u_divmod(fn_cs, fd_cs, zero)
    logs = []                        # [(c(Ga|Fr), g_cs)]
    ok = True
    rem_polys = []                   # 各因子的可除余商（τ-poly）
    for p1, _e1 in sqf:
        cof = u_divmod(fd_cs, p1, zero)[0]
        Bm = u_divmod(
            u_mul(fn_cs, u_inv_mod(cof, fd_cs, zero), zero), p1, zero)[1]
        lg, rem = _residue_sqfr(Bm, p1, de, jv, zero)
        for c, g in lg:
            cv = c if isinstance(c, (Fr, Ga)) else None
            if cv is None:
                try:
                    cv = Fr(c)
                except Exception:
                    return None      # 非常数残数 => 非对数导数
            logs.append((cv, g))
        if u_is_zero(rem):
            continue
        qq, rr = u_divmod(rem, p1, zero)
        if not u_is_zero(rr):
            return None              # normal 极点未被解释 => 非对数导数
        rem_polys.append(qq)

    # ---- 2) p_final = 多项式部分 − Σ c·D(g)/g，须为 τ-常数（∈K_{jv}）----
    P_n, P_d = list(Q_cs), [one_c]
    for qq in rem_polys:
        P_n = u_add(P_n, qq, zero)
    P_rf = _rf_of_cs(P_n, allv, tau) / _rf_of_cs(P_d, allv, tau)
    for cv, g in logs:
        g_rf = _rf_of_cs(list(g), allv, tau)
        dg_rf = _rf_of_cs(der_fn(g), allv, tau)
        term = dg_rf / g_rf * cv
        P_rf = P_rf - term
    # τ-free 门（deg < max(1, deg(Dτ)) 的等价形式）
    Pp_cs = from_poly(P_rf.p, tau)
    Pq_cs = from_poly(P_rf.q, tau)
    if u_deg(u_formal_deriv(Pp_cs)) >= 0 or \
            u_deg(u_formal_deriv(Pq_cs)) >= 0:
        return None

    # ---- 3) case 分派 ----
    def dens_lcm():
        nd = 1
        for cv, _g in logs:
            nd = lcm2(nd, ga_den(cv) if isinstance(cv, Ga)
                       else cv.denominator)
        return nd

    if jv == 0:
        # base：P 必须为零（无更低层承载）
        if not u_is_zero(from_poly(P_rf.p, tau)) and not P_rf.p.is_zero():
            if not P_rf.p.is_zero() or not P_rf.q.is_one():
                if not P_rf.p.is_zero():
                    return None
        if not P_rf.p.is_zero():
            return None
        n = dens_lcm()
        u = RatFunc(one_c * 0 + Poly.one(allv), Poly.one(allv))
        uacc = RatFunc(Poly.one(allv), Poly.one(allv))
        for cv, g in logs:
            ee = int(n * cv)
            gp = u_pow(list(g), ee, zero)
            gu, gd = _from_univar(gp, allv, tau)
            uacc = uacc * RatFunc(gu, gd)
        U = uacc
    elif de.cases[jv] == "primitive":
        rec = _is_logderiv_radical(P_rf, de, jv - 1, depth + 1)
        if rec is None:
            return None
        n_l, v = rec
        N = lcm2(n_l, dens_lcm())
        mm = N // n_l
        uacc = v ** mm
        for cv, g in logs:
            ee = int(N * cv)
            gp = u_pow(list(g), ee, zero)
            gu, gd = _from_univar(gp, allv, tau)
            uacc = uacc * RatFunc(gu, gd)
        N_final, U = N, uacc
        return _ld_finish(N_final, U, f_rf, de)
    else:  # exp
        eta = de.ws[jv]
        # 常数 P 平凡参数化（heu 的结构定理限制补全）：
        # v=1 时 n·P = m·η <=> P/η ∈ ℚ，取 n=分母、m=分子、U=τ^m/n·?
        # 即 U=τ^E，E/n = P/η。
        P_cv = rf_const_ga(P_rf)
        if P_cv is not None:
            eta_cv = rf_const_ga(eta)
            if eta_cv is not None and not eta_cv.is_zero():
                rho = P_cv / eta_cv
                if rho.im == 0 and rho.re.denominator != 0:
                    nn = rho.re.denominator
                    EE = int(rho.re * nn)
                    tau_u = (RatFunc(Poly.mono(allv, tau, EE),
                                     Poly.one(allv)) if EE > 0 else
                             RatFunc(Poly.one(allv),
                                     Poly.mono(allv, tau, -EE))
                             if EE < 0 else
                             RatFunc(Poly.one(allv), Poly.one(allv)))
                    return _ld_finish(nn, tau_u, f_rf, de)
        rec = _pld_solve(P_rf, [eta], de, jv - 1, depth + 1)
        if rec[0] == "no":
            return None          # 子判定完备证明否定
        if rec[0] == "und":
            raise RischUnsupported(
                "parametric log derivative undecided: " + str(rec[1]))
        _n2, n_l, ms_l, v = rec
        m_l = ms_l[0]
        N = lcm2(n_l, dens_lcm())
        mm = N // n_l
        uacc = v ** mm
        for cv, g in logs:
            ee = int(N * cv)
            gp = u_pow(list(g), ee, zero)
            gu, gd = _from_univar(gp, allv, tau)
            uacc = uacc * RatFunc(gu, gd)
        E = mm * m_l
        if E > 0:
            uacc = uacc * RatFunc(Poly.mono(allv, tau, E), Poly.one(allv))
        elif E < 0:
            uacc = uacc / RatFunc(Poly.mono(allv, tau, -E),
                                  Poly.one(allv))
        return _ld_finish(N, uacc, f_rf, de)

    # base 路径收尾（带验证）
    return _ld_finish(n, U, f_rf, de)


def _ld_finish(N, U, f_rf, de):
    """出口全量精确验证 D(U)==N·f·U；失败=内部错误（绝不静默）。"""
    from cas.ratfunc import RatFunc
    if U.p.vars != f_rf.p.vars:
        U = RatFunc(_embed(U.p, f_rf.p.vars), _embed(U.q, f_rf.p.vars))

    DU = _tower_deriv_frac(U.p, U.q, de)
    lhs = DU / U
    rhs = f_rf * N
    diff = lhs - rhs
    if not diff.p.is_zero():
        raise RischUnsupported(
            "internal: log-deriv radical witness failed exact verify "
            "(this is a bug, not an honest refusal)")
    return N, U


def _poly_dep(p, v):
    """Poly 对变量 v 是否实际依赖（指数非零；成员≠依赖）。"""
    try:
        j = p.vars.index(v)
    except ValueError:
        return False
    return any(k[j] != 0 for k in p.monos)


def _pld_solve(f_rf, ws_rf, de, jl, depth=0):
    """参数化对数导数判定（三态，M5 收官批 #1 完备化版）：

    解 n·f = D(v)/v + Σ mᵢ·wᵢ（n,mᵢ∈ℤ, v∈levels[:jl+1]*）。

    返回：
      ('ok', n, ms, v)   ms 与 ws_rf 对齐；恒等式经出口精确验证
      ('no', reason)     无解的机器证明（必要条件矛盾/唯一候选被
                         低层完备判定否证）
      ('und', reason)    当前理论不可判——调用方保守处理，绝不猜测

    算法（Bronstein z-归约 + 结构定理下降）：
      1. 全目标 τ-free => 本层无约束：exp 层按 v=c·τ^j·u 分解把 j 吸收
         为幂因子后降层；primitive 层 τ-含量被迫平凡直接降层；基级落
         通用路径。
      2. 通用路径：多项式部分系数行（i>B 区，B=deg Dτ−1 上界）∪
         z-余数行（z=special(l)·gcd(normal,D(normal))，l=分母 lcm）
         联合零空间。dim 0 => 'no'；每个本原整候选递归低层验证。
      3. z 常数且高区无行 => 'und'（中间层残数域约束，诚实放弃）；
         基级 => 有界枚举兜底。
    """
    from cas.ratfunc import RatFunc

    if depth > 12:
        return "und", "depth exhausted"
    tp = de.levels[jl]
    sub2 = tuple(de.levels[:jl])
    zero = RatFunc.zero(sub2)
    one_c = zero.one(zero.p.vars)
    der_fn = _make_der_fn(de, jl)

    if f_rf.is_zero():
        return "ok", 1, [0 for _ in ws_rf], \
            RatFunc.one(tuple(de.levels[:jl + 1]))

        # ---- 0b. 变量集收紧：投影到实际依赖的塔变量（冗余零指数维度
    #         会让跨层递归的 RatFunc 算术 var-mismatch）----
    used = set()
    for pp in [f_rf.p, f_rf.q] + [c for w_ in ws_rf
                                  for c in (w_.p, w_.q)]:
        for kk in pp.monos:
            for vi, ee in enumerate(kk):
                if ee:
                    used.add(pp.vars[vi])
    order = tuple(v for v in de.levels[:jl + 1] if v in used)

    def _proj(rf):
        if rf.p.vars == order:
            return rf

        def _shrink(p):
            ki = [p.vars.index(v) for v in order]
            return Poly(order, {tuple(k[i] for i in ki): c
                                for k, c in p.monos.items()})
        return RatFunc(_shrink(rf.p), _shrink(rf.q))

    f_rf = _proj(f_rf)
    ws_rf = [_proj(w_) for w_ in ws_rf]

    def _emb_full(v):
        allv = tuple(de.levels[:jl + 1])
        if v.p.vars == allv:
            return v
        return RatFunc(_embed(v.p, allv), _embed(v.q, allv))

    # ---- 0. 目标归并：零目标丢弃；Ga 常数倍目标合并（系数相加，
    #         恒等式等价；返回时按映射展开保持与调用方对齐）----
    groups = []                      # [w_kept, [(orig_idx, scale)]]
    for idx0, w0 in enumerate(ws_rf):
        if w0.is_zero():
            continue
        placed = False
        for g in groups:
            cv0 = rf_const_ga(w0 / g[0])
            if cv0 is not None and cv0.im == 0:
                g[1].append((idx0, cv0.re))
                placed = True
                break
        if not placed:
            groups.append([w0, [(idx0, Fr(1))]])
    ws_m = [g[0] for g in groups]

    def _expand(ms_kept):
        # 首成员全担系数（其余置 0）：Σmᵢwᵢ = m_kept·w_kept 等价保持。
        # 旧版逐成员重复分摊会把系数翻倍（假见证教训）
        out = [Fr(0) for _ in ws_rf]
        for g, mk in zip(groups, ms_kept):
            oi0, sc0 = g[1][0]
            out[oi0] = out[oi0] + mk / sc0
        return out

    def _pld_end_verify(n_v, ms_v, v_v):
        """端到端精确验证 D(v)/v == n·f − Σm·w（下降路径也过闸）。"""
        lhs = _tower_deriv_frac(v_v.p, v_v.q, de) / v_v
        rhs = f_rf * n_v
        for m_v, w_v in zip(ms_v, ws_rf):
            rhs = rhs - w_v * m_v
        if lhs.p.vars != rhs.p.vars:
            rhs = RatFunc(_embed(rhs.p, lhs.p.vars),
                          _embed(rhs.q, lhs.p.vars))
        if not (lhs - rhs).p.is_zero():
            raise RischUnsupported(
                "internal: parametric log deriv descent witness failed "
                "exact verify (bug, not honest refusal)")


    f_free = not _poly_dep(f_rf.p, tp) and not _poly_dep(f_rf.q, tp)
    ws_free = all(not _poly_dep(w.p, tp) and not _poly_dep(w.q, tp)
                  for w in ws_m)

    # ---- 1. 全 τ-free：结构定理下降 ----
    if f_free and ws_free:
        if jl == 0:
            rec0 = _pld_base_pair(f_rf, list(ws_m), de)
            if rec0[0] != "ok":
                return rec0
            ms_x = _expand(rec0[2])
            v_x = _emb_full(rec0[3])
            _pld_end_verify(rec0[1], ms_x, v_x)
            return "ok", rec0[1], ms_x, v_x
        if de.cases[jl] == "exp":
            # v = c·τ^j·u ⟹ n·f = D(u)/u + Σm·w + j·η；追加 η 为目标，
            # 返回后把该系数折进幂因子（D(τ^j)/τ^j = j·η 精确恒等）
            rec = _pld_solve(f_rf, list(ws_m) + [de.ws[jl]],
                             de, jl - 1, depth + 1)
            if rec[0] != "ok":
                return rec
            _n, ms_full, v = rec[1], rec[2], rec[3]
            own, j_extra = ms_full[:len(ws_m)], ms_full[len(ws_m):]
            allv = tuple(de.levels[:jl + 1])
            if v.p.vars != allv:
                v = RatFunc(_embed(v.p, allv), _embed(v.q, allv))
            j_eff = sum(j_extra)
            if j_eff > 0:
                v = v * RatFunc(Poly.mono(allv, tp, j_eff),
                                Poly.one(allv))
            elif j_eff < 0:
                v = v / RatFunc(Poly.mono(allv, tp, -j_eff),
                                Poly.one(allv))
            ms_x = _expand(own)
            v_x = _emb_full(v)
            _pld_end_verify(_n, ms_x, v_x)
            return "ok", _n, ms_x, v_x
        rec = _pld_solve(f_rf, list(ws_m), de, jl - 1, depth + 1)
        if rec[0] != "ok":
            return rec
        ms_x = _expand(rec[2])
        v_x = _emb_full(rec[3])
        _pld_end_verify(rec[1], ms_x, v_x)
        return "ok", rec[1], ms_x, v_x

    # ---- 2. 通用路径：系数行零空间 ----
    k = len(ws_m)
    f_n = from_poly(f_rf.p, tp)
    f_d = from_poly(f_rf.q, tp)
    ws_nd = [(from_poly(w.p, tp), from_poly(w.q, tp)) for w in ws_m]

    def _coef(cs, i):
        return cs[i] if i < len(cs) else zero

    dk_cs, _dkd = _dk_pair(de, jl)
    B = max(0, u_deg(dk_cs) - 1)

    pparts = [u_divmod(f_n, f_d, zero)[0]]
    for n_, d_ in ws_nd:
        pparts.append(u_divmod(n_, d_, zero)[0])
    C = max(u_deg(q) for q in pparts)

    rows = []
    if C > B:
        for i in range(B + 1, C + 1):
            rows.append([_coef(pparts[0], i)] +
                        [_coef(pparts[j + 1], i) * Fr(-1)
                         for j in range(k)])

    # l = 分母 monic lcm；z = special(l)·gcd(normal(l), D(normal(l)))
    dens = [f_d] + [d_ for _, d_ in ws_nd]
    l_cs = None
    for d_ in dens:
        dm = u_divmod(d_, [u_trim(list(d_))[-1]], zero)[0]
        if l_cs is None:
            l_cs = dm
        else:
            g2 = u_gcd(l_cs, dm, zero)
            l_cs = u_mul(l_cs, u_divmod(dm, g2, zero)[0], zero)
    ln_, ls_ = _split_ns(l_cs, der_fn, zero)
    z_const_case = False
    if u_is_zero(ln_):
        z_const_case = True
    else:
        gg = u_gcd(ln_, der_fn(ln_), zero)
        z_cs = u_mul(ls_, gg, zero)
        if u_deg(z_cs) < 1:
            z_const_case = True
        else:
            lfs = [u_mul(f_n, u_divmod(l_cs, f_d, zero)[0], zero)]
            for n_, d_ in ws_nd:
                lfs.append(u_mul(n_, u_divmod(l_cs, d_, zero)[0], zero))
            rems = [u_divmod(h_, z_cs, zero)[1] for h_ in lfs]
            zdeg = len(u_trim(list(z_cs))) - 1
            for i in range(max(len(r) for r in rems)):
                rows.append([_coef(rems[0], i)] +
                            [_coef(rems[j + 1], i) * Fr(-1)
                             for j in range(k)])

    if not rows:
        if jl == 0:
            rec0 = _pld_base_pair(f_rf, list(ws_m), de)
            if rec0[0] != "ok":
                return rec0
            ms_x = _expand(rec0[2])
            v_x = _emb_full(rec0[3])
            _pld_end_verify(rec0[1], ms_x, v_x)
            return "ok", rec0[1], ms_x, v_x
        return "und", "no constraints at level (z constant)"

    basis = _rf_nullspace(rows, k + 1, zero, one_c)

    if not basis:
        return "no", "coefficient null space empty (necessary " \
                      "conditions contradictory)"

    # 候选枚举：dim 1 直接取；dim ≥2 小系数组合封顶（超限诚实 und）
    cands = []
    if len(basis) == 1:
        cands.append(basis[0])
    else:
        from itertools import product as _iproduct
        small = [-2, -1, 0, 1, 2]
        for combo in _iproduct(small, repeat=len(basis)):
            if all(c_ == 0 for c_ in combo):
                continue
            vec = None
            for c_, bvec in zip(combo, basis):
                if c_ == 0:
                    continue
                scaled = [e * Fr(c_) for e in bvec]
                vec = scaled if vec is None else \
                    [a + b for a, b in zip(vec, scaled)]
            cands.append(vec)
            if len(cands) >= 24:
                break
        if len(basis) > 3 and len(cands) >= 24:
            return "und", "null space dimension too large"

    allv = tuple(de.levels[:jl + 1])
    saw_alive = False
    for vec in cands:
        ints = ga_vec_to_ints(vec)
        if ints is None:
            saw_alive = True          # 非整数常数向量：不可判死也不可用
            continue
        n_i = ints[0]
        if n_i <= 0:
            ints = [-v2 for v2 in ints]
            n_i = -n_i
        if n_i == 0:
            continue                  # 全零或 n=0：非正规化解
        ms_i = ints[1:]
        h = f_rf * n_i
        for m_j, w_j in zip(ms_i, ws_m):
            h = h - w_j * m_j
        # 上层 τ 残留 => 恒等式两端 τ-含量必不匹配（RHS D(v)/v 对
        # 子塔 v 无本层含量）=> 此候选证明性判死，绝不流向下层
        if _poly_dep(h.p, tp) or _poly_dep(h.q, tp):
            continue
        if h.is_zero():
            # 平凡恒等：v = 1
            ms_x = _expand(ms_i)
            v_x = RatFunc.one(tuple(de.levels[:jl + 1]))
            _pld_end_verify(n_i, ms_x, v_x)
            return "ok", n_i, ms_x, v_x
        try:
            if jl == 0:
                rad = _ldrad_base(h, de)
            else:
                rad = _is_logderiv_radical(h, de, jl - 1, depth + 1)
        except RischUnsupported as _ru:
            return "und", str(_ru)
        except Exception:
            rad = None                # 该候选证伪/不可判——继续其余
        if rad is None:
            continue                  # 此比例证明无解
        saw_alive = True
        Qn, u_v = rad
        v_fin = u_v
        if v_fin.p.vars != h.p.vars:
            v_fin = RatFunc(_embed(v_fin.p, h.p.vars),
                            _embed(v_fin.q, h.p.vars))
        # 出口精确验证：D(v)/(v·Q) == h（内部错误绝不静默）
        DU = _tower_deriv_frac(v_fin.p, v_fin.q, de)
        lhs = DU / (v_fin * Fr(Qn))
        if not (lhs - h).p.is_zero():
            raise RischUnsupported(
                "internal: parametric log deriv witness failed exact "
                "verify (bug, not honest refusal)")
        ms_x = _expand([Qn * m_j for m_j in ms_i])
        v_x = _emb_full(v_fin)
        return "ok", Qn * n_i, ms_x, v_x
    if saw_alive:
        return "und", "candidates alive but unverifiable"
    return "no", "all projective candidates proved dead"


def _rf_nullspace(rows, ncols, zero, one_c):
    """RatFunc 系数齐次系统零空间基（行主元消元）；空表 = 仅零解。"""
    mat = [list(r) for r in rows]
    pivots = []
    r = 0
    for c in range(ncols):
        pr = None
        for i in range(r, len(mat)):
            if not mat[i][c].is_zero():
                pr = i
                break
        if pr is None:
            continue
        mat[r], mat[pr] = mat[pr], mat[r]
        inv = one_c / mat[r][c]
        mat[r] = [x * inv for x in mat[r]]
        for i in range(len(mat)):
            if i != r and not mat[i][c].is_zero():
                fac = mat[i][c]
                mat[i] = [a - fac * b for a, b in zip(mat[i], mat[r])]
        pivots.append((r, c))
        r += 1
        if r == len(mat):
            break
    free_cols = [c for c in range(ncols) if c not in
                 {pc for _pr, pc in pivots}]
    basis = []
    for fc in free_cols:
        vec = [mk_zero_like(one_c) for _ in range(ncols)]
        vec[fc] = one_c
        for ri, pc in pivots:
            vec[pc] = mat[ri][fc] * Fr(-1)
        basis.append(vec)
    return basis


def _pld_base_pair(f_rf, ws_rf, de):
    """基级 z-常数兜底：有界本原对枚举 + _ldrad_base 精确验证。

    完备性边界：窗口（|n| ≤ 6、|m| ≤ 6、单目标）内穷尽；窗口外/
    多目标诚实 'und'。方向安全：漏枚举只损失覆盖，_ldrad_base 验证
    背书杜绝假阳性。"""
    from cas.ratfunc import RatFunc
    from math import gcd as _g3

    if len(ws_rf) != 1:
        return "und", "base fallback limited to single target"
    w_rf = ws_rf[0]
    for n_i in range(1, 7):
        for m_i in range(-6, 7):
            if m_i != 0 and _g3(abs(n_i), abs(m_i)) != 1:
                continue          # 非本原对与约简对同解，跳过
            h = f_rf * n_i - w_rf * m_i
            if h.is_zero():
                return "ok", n_i, [m_i], \
                    RatFunc.one(tuple(de.levels[:1]))
            try:
                rad = _ldrad_base(h, de)
            except Exception:
                continue
            if rad is None:
                continue
            Qn, u_v = rad
            return "ok", Qn * n_i, [Qn * m_i], u_v
    return "und", "bounded base enumeration exhausted"
