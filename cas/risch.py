# -*- coding: utf-8 -*-
"""微分域塔（Risch M5）：门面 + 递归驱动。

拆分布局（M6.7；实现按层分居，本文件保留顶层递归与全部历史导入面）：
    cas/risch_core.py   塔构建/DiffExt/derivation/trigs_to_exp/代数常数登记
    cas/risch_exp.py    exp 层 Hermite 推广+RT 残数、K[t] 视图、log 配对实化
    cas/risch_rdesup.py RDE 支撑：weak normalization/split/limited_integrate
    cas/risch_prde.py   参数化对数导数判定（_pld_solve 三态/_ldrad_base）
    cas/risch_rde.py    塔上 RDE 完备判定求解器 + exp 频率分量
    cas/risch.py        本文件——_risch_rec 递归驱动 + 兼容门面

懒导入断环（调用期双方已加载，与全库风格一致）：
    build_extension -> rischi_prde._is_logderiv_radical
    _limited_integrate / _exp_freq_part -> 本文件 _integrate_in_K
"""

from fractions import Fraction as Fr
from math import gcd

from cas import term as T
from cas.term import S, N, Expr, Sym, Const, Int, ONE, IU
from cas.poly import Poly, SymRat
from cas.errors import PolyError
from cas.gaussian import Ga
from cas.univar import (from_poly, u_add, u_sub, u_mul0, u_mul,
                        u_neg, u_pow, u_deg, u_trim, u_divmod, u_gcd,
                        u_xgcd, u_inv_mod, u_inv_mod_t, u_is_zero,
                        u_deriv_x, u_formal_deriv, u_diophantine,
                        u_gauss_solve_k)
from cas.scalarutil import (rf_const_ga, ga_den, lcm2,
                            ga_vec_to_ints, mk_zero_like,
                            leaf_has_ga, symrat_has_ga,
                            coef_zero, coef_re_im, poly_re_im)

# --- core：塔地基 ---
from cas.risch_core import (
    RischUnsupported, RischNonElementary, DiffExt,
    _embed, _rmul_polys, _cancel, _fr_gcd, _radd,
    _collect_exts, _TRIG_HEADS, _param_provisos, _exp_of,
    _ALG_RADICAL_COUNTER, _NCPOW_COUNTER,
    _collect_radical, _const_blockage_hint, _lin_exp_freq,
    _ef_contract, _ef_expand_trans, _neg_term, _iu,
    trigs_to_exp, _as_real_rat, _group_integer_powers, _ratio,
    _scale_arg, _try_qx, _fresh_sym,
    _tower_deriv_frac, _tower_logderiv, build_extension,
    _frac_from_term, _frac_num, derivation, tower_to_term_pair,
    _norm_const_base_powers, _parametrize_const_logs,
)
from cas.algfield import ALG_FIELDS   # M7.0-b 统一登记处（兼容导出面）

# --- exp 层 ---
from cas.risch_exp import (
    _realify_one_log, _realify_log_pairing,
    _from_univar, _derive_ut, _exp_w,
    _poly_to_list, _list_to_poly, _gauss_solve, _rde_exp_solve,
    risch_exp_integrate, _integrate_proper, _integrate_normal,
    _squarefree_decomp_t, _hermite_pe, _hermite_factor, _neg_poly,
    _sylvester_res, _bareiss_det, _uz_trim_det, _residue_sqfr,
    _uz_trim_list, _iter_subterms, _term_to_ga, _frac_sqrt,
    _ga_sqrt_exact, _const_roots_ga_quad, _term_to_symrat,
    _constant_roots, _free_of_x, assemble_exp_result,
)

# --- RDE 支撑 ---
from cas.risch_rdesup import (
    _coef_iter, _iter_leaf_coefs_m, _limited_integrate,
    _has_trans_head, _decompose_integral, _log_u_factor_generic,
    _map_known_log, _primitive_poly_part, _restrict,
    _fu_add, _fu_mul, _split_ns, _normal_part, _make_der_fn,
    _wn_normalize, _dk_pair,
)

# --- 参数化判定件 ---
from cas.risch_prde import (
    _const_to_term, _rf_of_cs, _cs_const_val, _ldrad_base,
    _term_within_field, _limited_int_prim, _is_logderiv_radical,
    _ld_finish, _poly_dep, _pld_solve, _rf_nullspace, _pld_base_pair,
)

# --- RDE 求解器 ---
from cas.risch_rde import (
    _parse_imag_exp_arg, _imag_exp_level_info, _poly_map_leaves,
    _ga_conj_leaf, _rf_split_im, _RealifyFail, _realify_laurent,
    b_rf_zero, _solve_low, _rde_base_rde, _poly_rde_final,
    _rde_tower_solve, _exp_freq_part,
)


def _mixed_domain_leaf(c):
    """叶是否属于 Q(i,x_params) 混合轨道（SymRat 内含 Ga 叶，或 Ga
    分量为 SymRat）。"""
    if isinstance(c, SymRat):
        for pp in (c.num, c.den):
            for cc in pp.monos.values():
                if hasattr(cc, "norm") and not isinstance(cc, Fr):
                    return True
        return False
    if hasattr(c, "norm") and isinstance(c, Ga):
        return isinstance(c.re, SymRat) or isinstance(c.im, SymRat)
    return False


def _has_mixed_domain(*polys):
    """多 Poly 的叶是否含 ℚ(i,params) 混合。"""
    for p in polys:
        if any(_mixed_domain_leaf(c) for c in _iter_leaf_coefs_m(p)):
            return True
    return False


def _split_tower_rational(fa, fd):
    """fa/fd（塔上 Poly）共轭展开实虚拆分（A4 泛化至多变量塔）。

    返回 (num_re, num_im, den) 或 None（无混合域叶时不需拆分）。
    num_re/den 与 num_im/den 各自纯参数叶（Fr/SymRat，无 Ga）——
    消除 _rde_tower_solve 的域泛化 gcd 需求。
    """
    if not _has_mixed_domain(fa, fd):
        return None
    from cas.scalarutil import poly_re_im
    fa_re, fa_im = poly_re_im(fa)
    fd_re, fd_im = poly_re_im(fd)
    den = fd_re * fd_re + fd_im * fd_im
    if den.is_zero():
        raise PolyError("zero denominator after conjugate expansion")
    num_re = fa_re * fd_re + fa_im * fd_im
    num_im = fa_im * fd_re - fa_re * fd_im
    return num_re, num_im, den


def _risch_rec_mixed(fa, fd, de, j):
    """_risch_rec 的混合域前置拆分包装。

    混合域（ℚ(i,params)）输入 => 共轭拆分 => 两条纯参数链 =>
    线性合并 re + i·im。非混合 => 直通 _risch_rec。
    """
    split = _split_tower_rational(fa, fd)
    if split is None:
        return _risch_rec(fa, fd, de, j)
    num_re, num_im, den = split
    expr_re = _risch_rec(num_re, den, de, j)
    if num_im.is_zero():
        return expr_re
    expr_im = _risch_rec(num_im, den, de, j)
    from cas import term as T
    from cas.term import S
    return T.plus(expr_re, T.times(IU, expr_im))


def integrate_exp_tower(f, x):
    """顶层 API：term -> (term, de)（初等原函数）或异常。

    M6.1 双塔合一：薄壳委托 structs.TowerStruct——project/compute
    是唯一实现，本函数不再持有流水线拷贝（防漂移复发）。
    常量被积函数快捷通道留在壳内（塔机制不适用，且保持用户原始
    形态出口）。
    """
    if x not in T.free_vars(f):
        return T.times(f, x), DiffExt(x)
    from cas.structs import TowerStruct
    ts = TowerStruct()
    st = ts.project(f, x, None)
    expr = ts.compute(st)[0]
    return expr, st[1]


def _integrate_in_K(g, de, j):
    """∫g dx，g ∈ K_j = ℚ(x, t₁..t_{j-1})（RatFunc on levels[:j]）→ term。"""
    from cas.integrate import integrate_rational

    if j <= 1:
        xv = de.levels[0]
        if g.is_const():
            # 常数被积函数（含 ℚ(i) 常数，M5.3 复指数化的 k=0 分量）
            cv = g.const_val()
            ct = cv.to_term() if hasattr(cv, "to_term") else N(cv)
            return T.times(ct, xv)
        # 基域有理积分：Fr/ℚ(params)（M5.6 参数轨道完备）/ℚ(i) 及
        # ℚ(i,params) 混合（A4 共轭拆分）全部由 integrate_rational
        # 入口统一路由——旧 "pending" 守卫是参数轨道完备前的遗留
        val, ok, _prov = integrate_rational(g.p, g.q, xv)
        if not ok:
            raise RischUnsupported("rational integration failed in base field")
        return val
    return _risch_rec(g.p, g.q, de, j - 1)


def _try_quad_algebraic(fa, fd, de, j):
    """二次代数扩张 y²=a x²+b x+c 的有理参数化快路（intaf quadIfCan）。

    仅 q=2 且 Mp 为 ℚ 上二次时尝试；成功返回积分 term，否则 None。
    覆盖 y²=x²+1 / y²=x+1 等亏格 0 情形，M78.7a 前置。
    优先特化：y²=x²+1 且被积式=1/y → log(x+y)（旗舰，闭式验证）。
    """
    try:
        from fractions import Fraction as Fr
        from math import isqrt
        from cas.poly import Poly
        from cas import term as _T
        from cas.term import S as _S
        q, mp_low = de.minpolys[j]
        if q != 2:
            return None
        # Mp = -mp_low[0]，mp_low = y² - Mp
        if len(mp_low.monos) != 2:
            return None
        # 提取 Mp（Poly in lower vars）
        Mp = None
        for k, v in mp_low.monos.items():
            if k[0] == 0:
                Mp = -v if isinstance(v, Poly) else None
        if Mp is None or Mp.is_zero():
            return None
        xv = de.levels[0]
        if Mp.vars != (xv,) and set(Mp.vars) != {xv}:
            # 仅单变量二次
            return None
        if Mp.degree(xv) != 2:
            return None
        # 确保无高次项（x³ 等）
        if any(k[0] not in (0, 1, 2) for k in Mp.monos):
            return None
        # Mp = a x² + b x + c
        a = Mp.monos.get((2,), Fr(0))
        b = Mp.monos.get((1,), Fr(0))
        c = Mp.monos.get((0,), Fr(0))
        if not all(isinstance(v, Fr) for v in (a, b, c)):
            return None
        # 旗舰特化：y²=x²+1
        _is_y = (fd.vars == tuple(de.levels[:j+1]) and
                 fd.monos == {(0,)*j + (1,): Fr(1)})
        _is_one = fa.is_const() and fa.const_val() == Fr(1)
        _is_x = (fa.vars == tuple(de.levels[:j+1]) and fa.monos == {(1,)+(0,)*j: Fr(1)})
        _is_y_num = (fa.vars == tuple(de.levels[:j+1]) and fa.monos == {(0,)*j + (1,): Fr(1)} and fd.is_const() and fd.const_val() == Fr(1))
        if a == Fr(1) and b == Fr(0) and c == Fr(1):
            y_sym = de.levels[j]
            xv_sym = de.levels[0]
            if _is_y and _is_one:
                return _T.fn("Log")(_T.plus(xv_sym, y_sym))
            if _is_y and _is_x:
                return y_sym
            if _is_y_num:
                return _T.div(_T.plus(_T.times(xv_sym, y_sym), _T.fn("Log")(_T.plus(xv_sym, y_sym))), _T.N(2))
        # y²=x+1 特化：1/y → 2y
        if a == Fr(0) and b == Fr(1) and c == Fr(1) and _is_y and _is_one:
            y_sym = de.levels[j]
            return _T.times(_T.N(2), y_sym)
        # 需 a 或 c 为有理平方（保证有理点）
        def _is_sq(f):
            if f < 0:
                return None
            n, d = f.numerator, f.denominator
            rn, rd = isqrt(n), isqrt(d)
            if rn * rn == n and rd * rd == d:
                return Fr(rn, rd)
            return None
        s_a = _is_sq(a) if a != 0 else None
        s_c = _is_sq(c) if c != 0 else None
        if s_a is None and s_c is None:
            return None
        # 一般二次有理参数化（a 或 c 为平方时亏格0，intaf quadIfCan）
        from cas.poly import Poly
        from cas.ratfunc import RatFunc
        from cas import term as _T
        from cas.term import S as _S
        t = _S("_quad_t")
        one = _T.ONE
        t_sym = t
        t2 = _T.pw(t_sym, _T.N(2))
        if s_a is not None:
            # t = y - s_a x, x=(c - t²)/(2 s_a t - b), y=t + s_a x
            s_a_t = _T.N(s_a)
            # x = (c - t²)/(2 s_a t - b)
            num_x = _T.plus(_T.N(c), _T.neg(t2))
            den_x = _T.plus(_T.times(_T.N(2 * s_a), t_sym), _T.neg(_T.N(b)))
            x_t = _T.div(num_x, den_x)
            # y = t + s_a x
            y_t = _T.plus(t_sym, _T.times(s_a_t, x_t))
            # dx/dt = [ -2t(2 s_a t - b) - (c - t²)2 s_a ]/(2 s_a t - b)²
            # 为简化用项层求导：直接构造 dx/dt via - (t² + s_a c?) 复杂，改用
            # 符号求导：x(t) 求导后有理式，通用有理积分会处理，此处用
            # 数值微分式 dx = -(t² + s_a c?) 简化为通用公式推导
            # 实际 dx/dt = (-2t(2 s_a t - b) -2 s_a(c - t²))/ (2 s_a t - b)²
            # = -(2 s_a t² - b t + s_a c)/? 复杂，直接用项层自动微分：
            # 构造 dx_dt term via differentiate? 简化：用 - (y + s_a x)/ (s_a t - b/2) ?
            # 为保持 PROBABLE 升 VERIFIED 的 _ta_reduce 路径，此处直接
            # 用通用有理参数化后的标准 dx/dt = -(t² + a c?) 推导
            # 对 y²=x²+1 特化为 -(t²+1)/2t²，其余二次用导数公式
            # 通用：dx/dt = (-2t(2 s_a t - b) -2 s_a(c - t²))/ (2 s_a t - b)²
            # = -(2 s_a t² - b t + s_a c + s_a t²)/... 简化直接构造
            # 为避免复杂，直接用项层微分：dx_dt = d(x_t)/dt via T.diff
            # 此处简化：对一般二次，用 t = y - s_a x 的逆，dx/dt 可经
            # y' = (2 a x + b)/2y 推导，但此处直接用有理式通用公式
            # 通用 dx/dt via term 微分（有理函数，精确）
            from cas.diff import d as _d
            try:
                dx_dt = _d(x_t, t_sym)
            except Exception:
                return None
            # 被积式在塔上为 fa/fd（Poly in x,y），转 term 后替换
            from cas.risch_core import tower_to_term_pair
            # fa/fd -> term in x,y
            f_term = tower_to_term_pair(fa, fd, de, backsub=False)
            xv_sym = de.levels[0]
            y_sym = de.levels[j]
            f_sub = _T.subst(f_term, {xv_sym: x_t, y_sym: y_t})
            g_t = _T.times(f_sub, dx_dt)
            # g_t 仅含 t（及常数），转 RatFunc 并有理积分
            from cas.integrate import integrate_rational
            # g_t 为 t 的有理函数，需通分后有理积分
            from cas.ops import together
            # 简化：直接用 integrate 理论中的有理积分入口处理 g_t
            # g_t 已是 t 的有理式（含 t 的负幂），用 Poly 转 RatFunc
            try:
                # 将 g_t 通分到 Poly
                from cas.poly import Poly as _P
                # 尝试直接用 integrate_rational 的底层：需 (P,Q) in t
                # 用 _frac 助手
                from cas.ratint import _rat_pair
                # _rat_pair 要求 x 为 t
                # 构造临时 term 的有理对：用 Poly.from_term 经 RatFunc
                # 简化：走 integrate(t) 的完整管线（已含 Risch）
                # 此处直接调用 integrate_rational 的上游：先转 RatFunc
                from cas.ratfunc import RatFunc as _RF
                # 将 g_t 转为 RatFunc in t via Poly
                # 用 together + numerator/denominator 提取
                from cas.ops import numerator as _num, denominator as _den
                # Fallback：尝试用 Poly.from_term 直接
                # 若 g_t 是 t 的有理函数，Poly.from_term 会抛，需走 together
                gt_together = together(g_t)
                # 提取分子分母 term 再转 Poly
                import cas.term as _TT
                # 简化：走 _rat_pair 风格但对 t
                # 直接尝试 Poly 构造
                # 若失败则返回 None 让通用 RDE 尝试
                # 以下为 t 的有理积分
                from cas.poly import Poly
                # 尝试将 gt_together 转为 (P,Q)
                # 用 Poly 的 from_term 对 t
                # 先试 together 后的 term 是否多项式可转
                try:
                    P = Poly.from_term(gt_together, (t,))
                    Q = Poly.one((t,))
                except Exception:
                    # gt_together 含分式，需用 ops.together 已通分，直接用 _rat_pair 逻辑
                    # 用 ratint 的 _frac 助手
                    from cas.ratint import _rat_pair as _rp2
                    # _rp2 expects x variable, but we have t
                    # 临时替换 x 为 t 的名字？直接用 Poly 分子分母提取
                    # 简化：用 together 后的 term 的 numerator/denominator
                    from cas.ops import numerator as _Nnum, denominator as _Dden
                    num_t = _Nnum(gt_together)
                    den_t = _Dden(gt_together)
                    P = Poly.from_term(num_t, (t,))
                    Q = Poly.from_term(den_t, (t,))
                val, ok, _ = integrate_rational(P, Q, t)
                if val is None:
                    return None
                # 回代 t = y - s_a x
                t_back = _T.plus(y_sym, _T.neg(_T.times(_T.N(s_a), xv_sym)))
                res = _T.subst(val, {t: t_back})
                return res
            except Exception:
                return None
        elif s_c is not None:
            # t = (y - s_c)/x, x=(b -2 t s_c)/(t² - a), y= t x + s_c
            s_c_t = _T.N(s_c)
            num_x = _T.plus(_T.N(b), _T.neg(_T.times(_T.N(2 * s_c), t_sym)))
            den_x = _T.plus(t2, _T.neg(_T.N(a)))
            x_t = _T.div(num_x, den_x)
            y_t = _T.plus(_T.times(t_sym, x_t), s_c_t)
            from cas.diff import d as _d2
            try:
                dx_dt = _d2(x_t, t_sym)
            except Exception:
                return None
            from cas.risch_core import tower_to_term_pair
            f_term = tower_to_term_pair(fa, fd, de, backsub=False)
            xv_sym2 = de.levels[0]
            y_sym2 = de.levels[j]
            f_sub2 = _T.subst(f_term, {xv_sym2: x_t, y_sym2: y_t})
            g_t2 = _T.times(f_sub2, dx_dt)
            from cas.integrate import integrate_rational
            from cas.ops import together
            try:
                gt2 = together(g_t2)
                from cas.ops import numerator as _num2, denominator as _den2
                from cas.poly import Poly as _P2
                try:
                    P2 = _P2.from_term(gt2, (t,))
                    Q2 = _P2.one((t,))
                except Exception:
                    num_t2 = _num2(gt2)
                    den_t2 = _den2(gt2)
                    P2 = _P2.from_term(num_t2, (t,))
                    Q2 = _P2.from_term(den_t2, (t,))
                val2, ok2, _ = integrate_rational(P2, Q2, t)
                if val2 is None:
                    return None
                t_back2 = _T.div(_T.plus(y_sym2, _T.neg(s_c_t)), xv_sym2)
                res2 = _T.subst(val2, {t: t_back2})
                return res2
            except Exception:
                return None
        return None
    except Exception:
        return None


def _risch_rec(fa, fd, de, j):
    """在第 j 层积分 fa/fd（Poly(levels[:j+1])）——递归塔核心。

    商/真分式分离后按 case 分派：primitive 多项式走 limited 循环，
    exp 多项式走频率 RDE；真分式共用 Hermite+residue（泛型）；
    leftover 按 case 回本层多项式循环（primitive，deg 严格降）或
    低层递归积分（exp 的 k=0 分量）。
    """
    from cas.ratfunc import RatFunc
    from cas.integrate import integrate_rational

    sub = tuple(de.levels[:j])
    zero = RatFunc.zero(sub)
    tj = de.levels[j]
    case = de.cases[j]

    A = from_poly(fa, tj)
    D = from_poly(fd, tj)
    if u_is_zero(A):
        return T.ZERO

    dq = len(D) - 1
    dp = len(A) - 1
    if dp >= dq:
        Q, R = u_divmod(A, D, zero)
    else:
        Q, R = [], A

    expr = T.ZERO
    if case == "primitive":
        for bk, k in _primitive_poly_part(Q, de, j):
            bt = bk.to_term()   # 塔符号形态
            tk = T.pw(T.S(tj.name), N(k)) if k != 1 else T.S(tj.name)
            expr = T.plus(expr, T.times(bt, tk))
        res, negf, st = (None, None, None, None), {}, "ok"
        if not u_is_zero(R):
            res, negf, st = _integrate_proper(R, D, de, j, zero)
    elif case == "algebraic":
        # M78.7a：二次代数快路（y²=x²+1 等）优先，失败回退通用 RDE
        quad = _try_quad_algebraic(fa, fd, de, j)
        if quad is not None:
            return quad
        # 通用代数 Hermite/RDE（当前复用 exp 频率 RDE，待迹推广）
        freqs = {k: c for k, c in enumerate(Q) if not c.is_zero()}
        res, negf, st = (None, None, None, None), {}, "ok"
        if not u_is_zero(R):
            res, negf, st = _integrate_proper(R, D, de, j, zero)
        for k, v in negf.items():
            freqs[k] = freqs[k] + v if k in freqs else v
        expr = T.plus(expr, _exp_freq_part(freqs, de, j))
    else:
        freqs = {k: c for k, c in enumerate(Q) if not c.is_zero()}
        res, negf, st = (None, None, None, None), {}, "ok"
        if not u_is_zero(R):
            res, negf, st = _integrate_proper(R, D, de, j, zero)
        for k, v in negf.items():
            freqs[k] = freqs[k] + v if k in freqs else v
        expr = T.plus(expr, _exp_freq_part(freqs, de, j))

    rat_part, logs, nonel, leftover = res
    expr = T.plus(expr, assemble_exp_result(rat_part, logs, nonel, de, j))

    if leftover is not None and any(not c.is_zero() for c in leftover):
        lf = u_trim(list(leftover))
        if case == "primitive":
            # θ-多项式剩余：回本层多项式积分（deg 严格降，终止）
            fn, fdd = _from_univar(lf, de.vars, tj)
            expr = T.plus(expr, _risch_rec(fn, fdd, de, j))
        else:
            # exp：ℚ 常数剩余（非常数系数已在频率分量中）
            cv = Fr(0)
            for c in lf:
                if not c.is_zero():
                    cv += c.const_val()
            if cv != 0:
                xv = de.levels[0]
                val, ok, _m = integrate_rational(Poly.const((xv,), cv),
                                                 Poly.one((xv,)), xv)
                if not ok:
                    raise RischUnsupported("leftover rational integration failed")
                expr = T.plus(expr, val)
    return expr
