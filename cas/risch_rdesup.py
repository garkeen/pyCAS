# -*- coding: utf-8 -*-
"""微分域塔·RDE 支撑层（自 cas/risch.py 拆出）：K[t] 分式算术、
normal/special 分解、weak normalization（FriCAS intpar.spad :920/:1237）、
视图导子、limited integration 与其分解件。

上游：risch_core（塔）/ risch_exp（K[t] 视图与残数装置）；
下游：risch_prde（参数化判定）、risch_rde（完备求解器）。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import S
from cas.poly import Poly, SymRat
from cas.errors import PolyError
from cas.univar import (from_poly, u_add, u_sub, u_mul, u_neg, u_pow,
                        u_deg, u_trim, u_divmod, u_gcd, u_xgcd,
                        u_inv_mod, u_formal_deriv, u_is_zero)
from cas.risch_core import RischUnsupported
from cas.risch_exp import (_sylvester_res, _constant_roots, _derive_ut,
                           _from_univar)


def _coef_iter(rf):
    """RatFunc 的全部叶系数。"""
    yield from _iter_leaf_coefs_m(rf.p)
    yield from _iter_leaf_coefs_m(rf.q)


def _iter_leaf_coefs_m(p):
    if not p.monos:
        return
    if len(p.vars) <= 1:
        for v in p.monos.values():
            yield v
        return
    from cas.poly import _rec_view
    for sub in _rec_view(p).values():
        yield from _iter_leaf_coefs_m(sub)


def _limited_integrate(a, de, j):
    """K_j 上求 (b_rf, c) 使 Db + c·v = a（limited integration 问题）。

    全程塔符号空间：c = ∫a 中 log(θ_j) 成分系数——θ_j 的对数形态
    Log(u_j) 的塔符号即本层变量自身。其余 log/atan 成分无法由 b ∈ K_j
    解释 -> rest ≠ 0 表示该塔内无解形态。
    """
    from cas.ratfunc import RatFunc

    syms = {de.terms[i]: T.S(de.levels[i].name)
            for i in range(1, len(de.levels))}
    u_sym = T.subst(de.terms[j].args[0], syms)   # u_j 的塔符号形态
    # 懒导入断环：_integrate_in_K 位于门面（递归驱动层），调用期已加载
    from cas.risch import _integrate_in_K
    val = _integrate_in_K(a, de, j)
    rat_t, alpha, rest = _decompose_integral(val, u_sym, syms)
    if rest is not T.ZERO:
        return None, None, rest
    try:
        b_rf = RatFunc.from_term(rat_t, tuple(de.levels[:j]))
    except PolyError:
        return None, None, val
    return b_rf, (alpha if alpha != 0 else None), T.ZERO


def _has_trans_head(t):
    """t 是否含 Log/Atan 头（任意深度）。"""
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, T.Expr):
            if u.head.name in ("Log", "Atan"):
                return True
            stack.extend(u.args)
    return False


def _decompose_integral(val, u_sym, syms):
    """塔符号空间的初等原函数 term -> (rat_term, alpha, rest)。

    - Log(g) 且 g ≡ u_sym：alpha 累加（limited 的 c）
    - Log(g) 且 g ≡ 某已建层参数 u_i：替换为塔符号 S(levels[i])（低层
      residue 出的 log(θ_i) 即 θ_i 自身形态，归 rat）
    - 其余含 Log/Atan 头：rest（新层候选，塔外成分）
    - 纯有理：rat
    """
    parts = val.args if isinstance(val, T.Expr) and val.head.name == "Plus" \
        else (val,)
    alpha = Fr(0)
    rest_parts = []
    rat_parts = []
    for t in parts:
        hit, coef = _log_u_factor_generic(t, u_sym)
        if hit:
            alpha += T.num_val(coef)
            continue
        mapped, new_t = _map_known_log(t, syms)
        if mapped:
            rat_parts.append(new_t)
        elif _has_trans_head(t):
            rest_parts.append(t)
        else:
            rat_parts.append(t)
    rat_t = T.mk(S("Plus"), tuple(rat_parts)) if len(rat_parts) > 1 \
        else (rat_parts[0] if rat_parts else T.ZERO)
    rest = T.mk(S("Plus"), tuple(rest_parts)) if len(rest_parts) > 1 \
        else (rest_parts[0] if rest_parts else T.ZERO)
    return rat_t, alpha, rest


def _log_u_factor_generic(t, u_sym):
    """t 是否含 Log(恰为 u_sym) 因子。-> (bool, 系数 term)。"""
    if isinstance(t, T.Expr) and t.head.name == "Log" \
            and len(t.args) == 1 and t.args[0] is u_sym:
        return True, T.ONE
    if isinstance(t, T.Expr) and t.head.name == "Times":
        lgs = [a for a in t.args if isinstance(a, T.Expr)
               and a.head.name == "Log" and len(a.args) == 1
               and a.args[0] is u_sym]
        if len(lgs) == 1:
            coef = T.ONE
            for o in t.args:
                if o is not lgs[0]:
                    coef = T.times(coef, o)
            return True, coef
    return False, None


def _map_known_log(t, syms):
    """t 中 Log(u_i)（u_i = 第 i 层参数）替换为塔符号 S(levels[i])。

    返回 (是否替换发生, 新 term)。t 不含任何已知 Log 时 (False, t)。
    """
    if not isinstance(t, T.Expr):
        return False, t
    hit = [False]

    def rec(u):
        if not isinstance(u, T.Expr):
            return u
        if u.head.name == "Log" and len(u.args) == 1:
            for key, sym in syms.items():
                if isinstance(key, T.Expr) and key.head.name == "Log" \
                        and len(key.args) == 1 and key.args[0] is u.args[0]:
                    hit[0] = True
                    return sym
        return T.mk(u.head, tuple(rec(a) for a in u.args))

    out = rec(t)
    return hit[0], out


def _primitive_poly_part(Q, de, j):
    """∫ Σ a_k θ^k：limited_integrate 循环（sympy integrate_primitive_polynomial
    同构）。每轮残差最高次严格下降，终止。"""
    from cas.ratfunc import RatFunc
    from cas.pprint import to_str as _ts

    sub = tuple(de.levels[:j])
    zero = RatFunc.zero(sub)
    out = []
    p = list(Q)
    while not u_is_zero(p):
        m = len(p) - 1
        a = p[m]
        b_rf, c, rest = _limited_integrate(a, de, j)
        if b_rf is None:
            raise RischUnsupported(
                "component requires integration outside the tower: "
                + _ts(rest)[:80])
        q0 = [zero] * (m + 2)
        if c is not None:
            q0[m + 1] = zero.one(zero.p.vars) * (Fr(c) / Fr(m + 1))
        q0[m] = b_rf
        p = u_sub(p, _derive_ut(q0, de, j))
        if not q0[m + 1].is_zero():
            out.append((q0[m + 1], m + 1))
        if not q0[m].is_zero():
            out.append((q0[m], m))
    return out


# ---------------------------------------------------------------------------
# M5.2c：塔系数域上的 Risch 微分方程（exp 层频率方程 y' + k·w·y = g，
# y ∈ K_j 含低层塔变量）。f = k·w 不含塔变量（exp 守卫保证）=> 极点分析
# 直接成立：den(y) | Π s^{e-1}（s^e ∥ den(g) 正规因子）——无需 weak
# normalization（那处理的是 f 本身有塔极点的 cancellation 情形）。
# 多项式化后 K 域线性系统待定系数；有解经精确验证输出，无解返回 None
# （unsupported，绝不误判不可积——完整 cancellation 分析留后续）。
# ---------------------------------------------------------------------------


def _restrict(rf, vars_):
    """RatFunc 收缩到指定变量集（缺失维度指数须全零，否则 PolyError）。"""
    from cas.ratfunc import RatFunc as _RF

    def shrink(p):
        if p.vars == tuple(vars_):
            return p
        idx = {v: i for i, v in enumerate(p.vars)}
        out = {}
        for k, c in p.monos.items():
            for v in p.vars:
                if v not in vars_ and k[idx[v]] != 0:
                    raise PolyError("cannot restrict: variable present")
            out[tuple(k[idx[v]] if v in idx else 0 for v in vars_)] = c
        return Poly(tuple(vars_), out)

    return _RF(shrink(rf.p), shrink(rf.q))


def _fu_add(n1, d1, n2, d2, zero):
    """K[t] 分式加法（n/d 为 univar list；空分母按单位 1 规范化）。"""
    one_c = zero.one(zero.p.vars)
    d1 = d1 if d1 else [one_c]
    d2 = d2 if d2 else [one_c]
    return (u_add(u_mul(n1, d2, zero), u_mul(n2, d1, zero), zero),
            u_mul(d1, d2, zero))


def _fu_mul(n1, d1, n2, d2, zero):
    one_c = zero.one(zero.p.vars)
    d1 = d1 if d1 else [one_c]
    d2 = d2 if d2 else [one_c]
    return (u_mul(n1, n2, zero), u_mul(d1, d2, zero))


def _fu_sub(n1, d1, n2, d2, zero):
    """K[t] 分式减法（_fu_add 对偶）。

    M6.7 缺陷修复：_wn_normalize 的右端缩放步（intpar.spad :1237，
    f − Σ mᵢ·D(πᵢ)/πᵢ）自引入即调用本函数，但定义从未落地——正重数
    normal 因子路径一触即 NameError，主路径测试不覆盖故长期潜伏。
    """
    return _fu_add(n1, d1, u_neg(n2, lambda c: c * Fr(-1)), d2, zero)


def _split_ns(p, der_fn, zero):
    """intrf.spad:141 split：p = normal·special。

    normal 的平方因子与 D(p) 互素；special 为 D-不变型因子。
    返回 (normal_list, special_list)。
    """
    p = u_trim(list(p))
    if u_is_zero(p) or len(p) <= 1:
        return list(p), []
    dp = der_fn(p)
    dfp = u_formal_deriv(p)
    if u_is_zero(u_sub(dp, dfp)):
        return list(p), []
    g = u_gcd(p, dp, zero)
    if len(g) <= 1:
        return list(p), []
    gd = u_gcd(p, dfp, zero)
    if len(gd) <= 1:
        pbar = list(g)
    else:
        pbar, r = u_divmod(g, gd, zero)
        if not u_is_zero(r):
            return list(p), []
    if len(pbar) <= 1:
        return list(p), []
    rest, rr = u_divmod(p, pbar, zero)
    if not u_is_zero(rr):
        return list(p), []
    rn, rs = _split_ns(rest, der_fn, zero)
    return rn, u_mul(pbar, rs, zero)


def _normal_part(p, der_fn, zero):
    return _split_ns(p, der_fn, zero)[0]


def _make_der_fn(de, jv):
    """视图层 jv 的 K[t]-导子 der1：D(Σcᵢτⁱ)。jv==0 时 D=d/dx、dk=1。

    基级系数为纯常数（子变量集空），自身导数项恒零——只保留
    i·cᵢτ^{i-1} 移位项（旧版对常数 RatFunc 求 levels[0]-导会炸）。"""
    if jv == 0:
        def der_fn(cs):
            out = []
            for i in range(1, len(cs)):
                out.append(cs[i] * Fr(i))
            return u_trim(out)
        return der_fn
    return lambda cs: _derive_ut(cs, de, jv)


def _wn_normalize(fn, fd, de, jv, der_fn, zero):
    """intpar.spad:920 weak normalization（非参数化特化）。

    返回 (fn2, fd2, pn, pd)：f_new = fn2/fd2 已消 normal 极点；
    p = pn/pd 使 v = y·p 时新方程右端须 ×p（intpar:1237）、解 ÷p（:1239）。
    无法判定返回 None。
    """
    one_c = zero.one(zero.p.vars)
    pn, pd = [one_c], []
    d = _normal_part(fd, der_fn, zero)
    if len(d) <= 1:
        return list(fn), list(fd), pn, pd
    g0 = u_gcd(d, der_fn(d), zero)
    d0 = u_divmod(d, g0, zero)[0]
    dd = u_gcd(d0, g0, zero)
    d1 = u_divmod(d0, dd, zero)[0]
    if len(d1) <= 1:
        return list(fn), list(fd), pn, pd
    q2, r2 = u_divmod(fd, d1, zero)
    if not u_is_zero(r2):
        return None
    d2 = q2
    s_, _t_, g_ = u_xgcd(d2, d1, zero)
    if u_is_zero(g_):
        return None
    qqf, rf = u_divmod(fn, g_, zero)
    if not u_is_zero(rf):
        return None
    a_ = u_mul(s_, qqf, zero)
    d1d = der_fn(d1)
    nb = max(len(a_), len(d1d))
    a_pad = list(a_) + [zero for _ in range(nb - len(a_))]
    d_pad = list(d1d) + [zero for _ in range(nb - len(d1d))]
    fz = [[ai, c * Fr(-1)] for ai, c in zip(a_pad, d_pad)]
    gz = [[ci] for ci in d1]
    Rz = _sylvester_res(fz, gz)
    rl = []
    if Rz and not u_is_zero(Rz):
        for mval in _constant_roots(Rz, xv=de.levels[0]):
            try:
                mv = mval if isinstance(mval, Fr) else Fr(mval)
            except Exception:
                return None
            if mv.denominator != 1 or mv <= 0:
                continue
            fm = u_sub(a_pad, [c * mv for c in d_pad])
            pi_m = u_gcd(fm, d1, zero)
            if len(pi_m) <= 1:
                continue
            rl.append((pi_m, int(mv)))
    fn2, fd2 = list(fn), list(fd)
    for pi_m, mv in rl:
        fn2, fd2 = _fu_sub(fn2, fd2,
                           [c * Fr(mv) for c in der_fn(pi_m)],
                           list(pi_m), zero)
        for _ in range(mv):
            pn, pd = _fu_mul(pn, pd, list(pi_m), [], zero)
    return fn2, fd2, pn, pd


def _dk_pair(de, jv):
    """D(levels[jv]) 的 τ-系数表示 (n_list, d_list)。"""
    tview = de.levels[jv]
    dk_n, dk_d = de.dpair(jv, tuple(de.levels[:jv + 1]))
    return from_poly(dk_n, tview), from_poly(dk_d, tview)
