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
