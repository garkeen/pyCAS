# -*- coding: utf-8 -*-
"""微分域塔·RDE 完备判定求解器（自 cas/risch.py 拆出）：
D(y) + f·y = g 的三态判定（ok / proved / undecided）、weak normalization
消费端、Laurent 对角下降、出口实化（_realify_laurent）、exp 频率分量。

唯一算法参考：FriCAS intpar.spad ParametricRischDE + sympy rde.py
分派细节。三态语义：有理解（精确验证兜底）/ 无解机器证明 /
当前理论不可判（绝不猜测、绝不误证）。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N, Expr, Sym, ONE
from cas.poly import Poly
from cas.errors import PolyError
from cas.gaussian import Ga
from cas.univar import (from_poly, u_add, u_sub, u_mul, u_pow, u_deg,
                        u_trim, u_divmod, u_gcd, u_formal_deriv,
                        u_diophantine, u_is_zero)

from cas.risch_core import (
    RischUnsupported, RischNonElementary, _embed, _tower_deriv_frac,
)
from cas.risch_exp import (
    _rde_exp_solve, _iter_subterms, assemble_exp_result, _from_univar,
)
from cas.risch_rdesup import (_make_der_fn, _dk_pair, _split_ns,
                              _normal_part, _fu_mul, _wn_normalize,
                              _primitive_poly_part)
from cas.risch_prde import (_is_logderiv_radical, _pld_solve,
                            _limited_int_prim)


# ---------------------------------------------------------------------------
# M5.3 出口实化（可判定子集）：tau = e^{i*sgn*u} 视角的 Laurent 解
# -> 实三角形态。全部精确恒等式，无启发式搜索：
#
#   C* = 全共轭：子域叶系数 Ga(a,b) -> a-b，且 tau -> tau^{-1}。
#   实原函数的判定 = y == C*(y)（RatFunc 分子 is_zero，精确非数值）。
#   R = (y + C*y)/2 的 tau-系数必实（_rf_split_im 拆分后断言）。
#   单位圆恒等式 (C+iS)^{-e} = (C-iS)^e 保证负幂无分母。
#   奇 i-相位单项式总和必为零（对称性，精确多项式零检查断言）。
# 任一环节不满足 => 返回 None，调用方保留复形态（诚实回退）。
# ---------------------------------------------------------------------------

def _parse_imag_exp_arg(arg):
    """Exp 参数 = q*i*u（q 非 0 有理）-> (sgn, u_eff=|q|*u)；否则 None。"""
    if not isinstance(arg, Expr) or arg.head.name != "Times":
        return None
    q = Fr(1)
    i_cnt = 0
    rest = []
    for a in arg.args:
        if isinstance(a, Sym) and a.name == "i":
            i_cnt += 1
            continue
        if T.is_num(a):
            try:
                q *= Fr(T.num_val(a))
            except Exception:
                return None
            continue
        rest.append(a)
    if i_cnt != 1 or q == 0 or not rest:
        return None
    u_eff = rest[0] if len(rest) == 1 else T.mk(S("Times"), tuple(rest))
    aq = abs(q)
    if aq != 1:
        u_eff = T.times(N(aq), u_eff)
    return (1 if q > 0 else -1), u_eff


def _imag_exp_level_info(de, jv):
    """视图层 jv 的 Exp 项为 e^{+-iu} -> (sgn, u_eff)；否则 None。"""
    if de.cases[jv] != "exp":
        return None
    tm = de.terms[jv]
    if not isinstance(tm, Expr) or tm.head.name != "Exp":
        return None
    if len(tm.args) != 1:
        return None
    return _parse_imag_exp_arg(tm.args[0])


def _poly_map_leaves(p, fn):
    """Poly 叶系数映射重建（多变量递归）。"""
    from cas.poly import _rec_view, _from_rec
    if not p.monos:
        return p
    if len(p.vars) <= 1:
        return Poly(p.vars, {k: fn(v) for k, v in p.monos.items()})
    rec = {e0: _poly_map_leaves(sub, fn) for e0, sub in _rec_view(p).items()}
    return _from_rec(rec, p.vars)


def _ga_conj_leaf(v):
    if isinstance(v, Ga):
        return Ga(v.re, -v.im)
    return v


def _rf_split_im(rf):
    """RatFunc -> (实部, 虚部) RatFunc（叶系数 Ga 精确拆分）。"""
    from cas.ratfunc import RatFunc

    def sp(p, take):
        def fn(v):
            if isinstance(v, Ga):
                return v.re if take == "re" else v.im
            return v if take == "re" else Fr(0)
        return _poly_map_leaves(p, fn)

    pn, pi_ = sp(rf.p, "re"), sp(rf.p, "im")
    qn, qi = sp(rf.q, "re"), sp(rf.q, "im")
    den_n = qn * qn + qi * qi
    return RatFunc(pn * qn + pi_ * qi, den_n), RatFunc(pi_ * qn - pn * qi, den_n)


class _RealifyFail(Exception):
    pass


def _realify_laurent(y_rf, tau, sgn, u_eff, xv):
    """tau=e^{i*sgn*u_eff} 视角 Laurent 解 -> 实三角 term；否则 None。

    可判定核心：
      1) y 归一为显式指数字典 {(p0-q0)+j: 系数}；
      2) 实性 <=> 对每个非零指数 k 存在 -k 且系数互为共轭
         （叶系数 Ga 精确比较，非数值）；零指数系数必须实；
      3) 共轭对直接公式化：s_e=a+ib =>
             2a*cos(e*theta) - 2b*sin(e*theta)，theta=sgn*u_eff。
    无启发式搜索；任一前提不满足返回 None（调用方保留复形态）。
    """
    from cas.ratfunc import RatFunc

    # tau 不在变量集 => y 为 tau^0：仅须实（虚部精确零）
    if tau not in y_rf.p.vars:
        a_rf, b_rf = _rf_split_im(y_rf)
        if not b_rf.p.is_zero():
            return None
        return y_rf.to_term()

    def conj_rf(rf):
        return RatFunc(_poly_map_leaves(rf.p, _ga_conj_leaf),
                       _poly_map_leaves(rf.q, _ga_conj_leaf))

    one_p = Poly.one(y_rf.p.vars)

    # ---- 1) 归一化：y = tau^K * P(tau)/c，K=p0-q0、c 为分母首非零 ----
    P_cs = from_poly(y_rf.p, tau)
    Q_cs = from_poly(y_rf.q, tau)

    def mono_power(cs):
        """cs 必须为单项式 c*tau^v -> (v, c)；否则 None。"""
        first = None
        for idx, c in enumerate(cs):
            if c.is_zero():
                continue
            if first is not None:
                return None          # 非单项式
            first = (idx, c)
        return first

    p0 = None
    while len(P_cs) > 0 and P_cs[0].is_zero():
        P_cs = P_cs[1:]
        p0 = 0
    # 分子允许一般多项式：记录最低次
    p_lo = 0
    P_trim = u_trim(list(P_cs))
    if u_is_zero(P_trim):
        return None
    while P_cs[p_lo].is_zero():
        p_lo += 1

    qmono = mono_power(Q_cs)
    if qmono is None:
        return None                  # 分母含非常数非常单项式因子
    q0, c_den = qmono
    K = p_lo - q0
    # 分子其余部分仍是一般多项式（从 p_lo 起到尾部）
    body = {}
    ok_any = False
    for idx in range(p_lo, len(P_cs)):
        c = P_cs[idx]
        if c.is_zero():
            continue
        body[(idx - p_lo) + K] = c / c_den
        ok_any = True
    if not ok_any:
        return None

    # ---- 2) 实性：逐指数配对 ----
    half_done = set()
    parts = []
    u_arg_cache = {}

    def u_arg_of(e):
        if e not in u_arg_cache:
            u_arg_cache[e] = u_eff if e == 1 else T.times(N(e), u_eff)
        return u_arg_cache[e]

    keys = sorted(body.keys())
    for k in keys:
        if k in half_done:
            continue
        s_k = body[k]
        if k == 0:
            a_rf, b_rf = _rf_split_im(s_k)
            if not b_rf.p.is_zero():
                return None
            if not a_rf.p.is_zero():
                parts.append(a_rf.to_term())
            half_done.add(0)
            continue
        kn = -k
        s_n = body.get(kn)
        if s_n is None:
            return None              # 缺共轭伙伴 => 非实
        if not (conj_rf(s_k) - s_n).p.is_zero():
            return None              # 系数非共轭（精确零判定）
        s_pos = s_k if k > 0 else s_n
        e = abs(k)
        a_rf, b_rf = _rf_split_im(s_pos)
        ct = T.mk(S("Cos"), (u_arg_of(e),))
        st_t = T.mk(S("Sin"), (u_arg_of(e),))
        t1 = a_rf * Fr(2)
        t2 = b_rf * Fr(-2 * sgn)
        if not t1.p.is_zero():
            parts.append(T.times(t1.to_term(), ct))
        if not t2.p.is_zero():
            parts.append(T.times(t2.to_term(), st_t))
        half_done.add(k)
        half_done.add(kn)

    if not parts:
        return None
    body_t = parts[0] if len(parts) == 1 else T.mk(S("Plus"), tuple(parts))
    return body_t


def b_rf_zero(b0):
    return b0.p.is_zero()


def _solve_low(lam, rhs, de, jl):
    """低层 RDE D(s)+λ·s=rhs，s ∈ levels[:jl]（jl>=1 递归，jl==0 基层）。"""
    if jl >= 1:
        return _rde_tower_solve(lam, rhs, de, jl)
    return _rde_base_rde(lam, rhs, de)


def _rde_base_rde(lam, rhs, de):
    """ℚ(x)：D(s)+λ·s=rhs。λ 多项式 -> 极点分析完备判定；否则 undecided。"""
    from cas.ratfunc import RatFunc

    xv = de.levels[0]
    if not (lam.q.is_const() and lam.p.vars == (xv,) and
            rhs.p.vars == (xv,) and rhs.q.vars == (xv,)):
        return None, 'undecided'
    if lam.is_const() and lam.const_val() == 0:
        # λ=0：D(s)=rhs 纯有理积分（S-b B=0 下降的基层落点）。
        # 域内精确性门：解含 Log => 需要塔外元素 => 该层无解（proved）
        from cas.integrate import integrate_rational
        val, ok, _m = integrate_rational(rhs.p, rhs.q, xv)
        if not ok:
            return None, 'undecided'
        if T.free_vars(val) and any(
                isinstance(n_, Expr) and n_.head.name == "Log"
                for n_ in _iter_subterms(val)):
            return None, 'proved'
        return RatFunc.from_term(val, (xv,)), 'ok'
    # λ 任意多项式（含常数）、rhs 任意有理式：极点分析 + 待定系数完备
    b = _rde_exp_solve(1, lam.p, rhs.p, rhs.q, Poly.zero((xv,)))
    if b is None:
        return None, 'proved'
    if isinstance(b, Poly):
        b = RatFunc.from_poly(b)
    return b, 'ok'


def _poly_rde_final(bbr, cn, n, case_v, base_flag, dk_deg, dk_ncs,
                    der_fn, de, jv, zero):
    """sympy solve_poly_rde 非参数版：解 D(u)+bbr·u=cn（deg u ≤ n）。

    返回 ('ok', u_list) | ('proved', None) | ('undecided', reason)。
    """
    dB = u_deg(bbr)
    thr = max(0, dk_deg - 1)

    def corr(cc, pmono):
        return u_sub(cc, u_add(der_fn(pmono), u_mul(bbr, pmono, zero),
                                 zero))

    # no_cancel_b_large
    if not u_is_zero(bbr) and (base_flag or dB > thr):
        u_acc, cc, mm = [], list(cn), n
        while not u_is_zero(cc):
            stp = u_deg(cc) - dB
            if stp < 0 or stp > mm:
                return 'proved', None
            pmono = [zero for _ in range(stp)] + [cc[-1] / bbr[dB]]
            u_acc = u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        return 'ok', u_acc

    # no_cancel_b_small（含降到低层的 (h,b0,c0) 归约）
    if (u_is_zero(bbr) or dB < dk_deg - 1) and (base_flag or dk_deg >= 2):
        u_acc, cc, mm = [], list(cn), n
        low_eq = None
        while not u_is_zero(cc):
            dcc = u_deg(cc)
            stp = 0 if mm == 0 else dcc - dk_deg + 1
            if stp < 0 or stp > mm:
                return 'proved', None
            if stp > 0:
                pmono = [zero for _ in range(stp)] + \
                    [cc[-1] / (dk_ncs[dk_deg] * Fr(stp))]
            else:
                if dB != dcc:
                    return 'proved', None
                if dB == 0:
                    low_eq = (bbr[0], cc[0])
                    break
                pmono = [cc[-1] / bbr[0]]
            u_acc = u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        if low_eq is not None:
            yl, stl = _solve_low(low_eq[0], low_eq[1], de, jv)
            if stl != 'ok':
                return stl, None
            return 'ok', u_add(u_acc, [yl], zero)
        return 'ok', u_acc

    # no_cancel_equal（共振贪心，自包含）
    if dk_deg >= 2 and dB == dk_deg - 1:
        lc_ratio = (bbr[dB] * Fr(-1)) / dk_ncs[dk_deg]
        big_m = -1
        if lc_ratio.is_const() and lc_ratio.const_val().denominator == 1 \
                and lc_ratio.const_val() > 0:
            big_m = int(lc_ratio.const_val())
        u_acc, cc, mm = [], list(cn), n
        while not u_is_zero(cc):
            dcc = u_deg(cc)
            stp = max(big_m, dcc - dk_deg + 1)
            if stp < 0 or stp > mm:
                return 'proved', None
            uu = stp * dk_ncs[dk_deg] + bbr[dB]
            if uu.is_zero():
                return 'undecided', 'no_cancel_equal tail recursion pending'
            if stp > 0:
                pmono = [zero for _ in range(stp)] + [cc[-1] / uu]
            else:
                if dcc != dk_deg - 1:
                    return 'proved', None
                pmono = [cc[-1] / bbr[dB]]
            u_acc = u_add(u_acc, pmono, zero)
            mm = stp - 1
            cc = corr(cc, pmono)
        return 'ok', u_acc

    # cancellation 形态
    # B=0（S-b 已修复）：方程 D(u)=cn 即纯塔积分——对角/三角下降对
    # lam=0 同样完备（每度独立解低层 D(s)=c_jd，不可解即 proved）
    if not u_is_zero(bbr) and dB != 0:
        return 'undecided', 'unexpected B degree in cancellation shape'
    if u_is_zero(bbr):
        lam = zero
    else:
        lam = bbr[0]
    w_eta = de.ws[jv] if case_v == 'exp' and jv >= 1 else None
    u_acc, cc, mm = [], list(cn), n
    while not u_is_zero(cc):
        jd = u_deg(cc)
        if jd > mm:
            return 'proved', None
        lam_j = lam + w_eta * Fr(jd) if w_eta is not None else lam
        s_rf, stl = _solve_low(lam_j, cc[-1], de, jv)
        if stl != 'ok':
            return stl, None
        stm = [zero for _ in range(jd)] + [s_rf]
        u_acc = u_add(u_acc, stm, zero)
        mm = jd - 1
        cc = corr(cc, stm)
    return 'ok', u_acc


def _rde_tower_solve(f, g, de, j):
    """完备判定求解器入口（契约见块注释）。j>=2 进塔机制（视图 jv=j-1>=1）；
    j==1 即 ℚ(x) 基层，直接委托极点分析（基层无更低视图，塔机制不适用）。"""
    from cas.ratfunc import RatFunc

    if j < 1:
        return None, 'undecided'
    # M5 收官批 #3：混合域门控退役——顶层 _risch_rec_mixed 已做
    # 共轭拆分，此处的 f, g 系数已纯参数化（Fr/SymRat 无 Ga）
    if j == 1:
        return _rde_base_rde(f, g, de)
    tview = de.levels[j - 1]
    case_v = de.cases[j - 1]
    jv = j - 1
    sub_vars = tuple(de.levels[:jv])

    def RF_of(ncs, dcs):
        nump = _from_univar(ncs, tuple(de.levels[:j]), tview)
        denp = _from_univar(dcs, tuple(de.levels[:j]), tview)
        if nump[0].is_zero():
            return RatFunc.zero(tuple(de.levels[:j]))
        return RatFunc(nump[0] * denp[1], denp[0] * nump[1])

    zero = RatFunc.zero(sub_vars)
    one_c = zero.one(sub_vars)
    der_fn = _make_der_fn(de, jv)

    dk_ncs, dk_dcs = _dk_pair(de, jv)
    if u_deg(u_formal_deriv(dk_dcs)) >= 0:
        return None, 'undecided'
    dk_deg = u_deg(dk_ncs)

    fn = from_poly(f.p, tview)
    fd = from_poly(f.q, tview)
    gn = from_poly(g.p, tview)
    gd = from_poly(g.q, tview)

    # ---- Step 1: weak normalization（intpar:920；右端缩放 :1237）----
    wn = _wn_normalize(fn, fd, de, jv, der_fn, zero)
    if wn is None:
        return None, 'undecided'
    fn2, fd2, pn, pd = wn
    gn2, gd2 = _fu_mul(gn, gd, pn, pd, zero)

    # ---- Step 2: normal denominator -> 多项式方程（intpar:910, 1406-1410）----
    dn_ = _normal_part(fd2, der_fn, zero)
    en_ = _normal_part(gd2, der_fn, zero)
    gg = u_gcd(dn_, en_, zero)
    hq, hr = u_divmod(u_gcd(en_, der_fn(en_), zero),
                      u_gcd(gg, der_fn(gg), zero), zero)
    if not u_is_zero(hr):
        return None, 'undecided'
    h = hq
    aa = u_mul(dn_, h, zero)
    dh = der_fn(h)
    bbr_n = u_sub(u_mul(aa, fn2, zero), u_mul(dn_, dh, zero))
    bq, br = u_divmod(bbr_n, fd2, zero)
    if not u_is_zero(br):
        return None, 'undecided'
    bbr = bq
    aa1 = u_mul(aa, h, zero)
    cn, cd = _fu_mul(aa1, [one_c], gn2, gd2, zero)

    # ---- Step 3: C 的分母结构分流 ----
    # exp 视角 special 型 τ-分母（τ^v 单项式）=> Laurent 对角下降
    # （FriCAS do_SPDE_exp0 的 GP 形态：special 因子 = τ 幂，展开后
    # 系数 τ-free，各指数独立）。混合/normal 型分母仍走原路线。
    laurent = None
    if case_v == 'exp' and u_deg(u_formal_deriv(cd)) >= 0:
        v_tau = 0
        cd_w = list(cd)
        while len(cd_w) > 0 and cd_w[0].is_zero():
            cd_w = cd_w[1:]
            v_tau += 1
        rest = u_trim(cd_w)
        rest_const = len(rest) <= 1
        if rest_const and u_deg(aa) == 0 and u_deg(bbr) == 0 \
                and not u_is_zero(cn):
            laurent = (v_tau, rest[0])
        else:
            return None, 'undecided'
    elif u_deg(u_formal_deriv(cd)) >= 0:
        return None, 'undecided'

    u_list = []
    if laurent is not None:
        # ---- Laurent 对角下降 ----
        # c = cn/(τ^v·r)：指数 e=idx−v，系数=cn[idx]/r；逐指数解
        # D(s)+(lam+e·η)s=c_e（对角：D(τ^e)=e·η·τ^e 不跨指数），
        # 残差同步消去该指数。η=D(τ)/τ=ws[jv]。
        v_tau, r_coef = laurent
        eta_w = de.ws[jv]
        lam = bbr[0] / aa[0]
        inv_r = one_c / r_coef
        cc = {idx - v_tau: c * inv_r for idx, c in enumerate(cn)
              if not c.is_zero()}
        u_parts = {}
        guard = 0
        while cc:
            guard += 1
            if guard > 64:
                return None, 'undecided'
            e_top = max(cc.keys())
            c_e = cc.pop(e_top)
            lam_e = lam + eta_w * Fr(e_top)
            s_rf, st_l = _solve_low(lam_e, c_e, de, jv)
            if st_l != 'ok':
                return None, st_l
            u_parts[e_top] = s_rf
            # 残差：D(s·τ^e)+B·s·τ^e 的 e-系数 = D_low? 此处 s ∈ K_{j-1}，
            # 其 D 含 η·s 已含在低层方程内——残差恰为 (D_K(s)+e·η·s+B·s)τ^e，
            # 而低层方程 D_low(s)+(lam+e·η)s=c_e 中 D_low 即 K_{j-1} 全导数，
            # 解代入后该指数余量 = c_e − [D_low(s)+(lam+eη)s] = 0 恒成立，
            # 无跨指数泄漏（exp 对角保证），无需额外扣减。
        if not u_parts:
            y_final = RatFunc.zero(tuple(de.levels[:j]))
        else:
            e_min = min(u_parts.keys())
            e_max = max(u_parts.keys())
            num_cs = [zero for _ in range(e_max - e_min + 1)]
            for e, s_rf in u_parts.items():
                num_cs[e - e_min] = s_rf
            np_, nd_ = _from_univar(num_cs, tuple(de.levels[:j]), tview)
            if e_min < 0:
                tau_v = Poly.mono(tuple(de.levels[:j]), tview, -e_min)
                y_final = RatFunc(np_, nd_ * tau_v)
            else:
                y_final = RatFunc(np_, nd_)
        # Laurent 出口直接验证（常数 a、b 路径下 h、p 均为单位）
        dy = _tower_deriv_frac(y_final.p, y_final.q, de)
        if not (dy + f * y_final - g).p.is_zero():
            raise RischUnsupported(
                "internal: Laurent RDE candidate failed exact verify")
        # 实化在 _exp_freq_part 组装层做（t^k 频率因子须一并参与）
        return y_final, 'ok'
    if not u_is_zero(cn):
        inv_cd = one_c / cd[0]
        cn = [c * inv_cd for c in cn]

        da, db, dc = u_deg(aa), u_deg(bbr), u_deg(cn)
        base_flag = (case_v == 'base')

        # ---- Step 4: 次数界（sympy bound_degree 移植 + 切片边界）----
        if case_v == 'base':
            n = max(0, dc - max(db, da - 1))
            if db == da - 1 and da >= 1:
                al = (bbr[db] * Fr(-1)) / aa[da]
                if al.is_const():
                    cv = al.const_val()
                    if cv.denominator == 1:
                        n = max(n, int(cv), dc - db)
                else:
                    return None, 'undecided'
        elif case_v == 'primitive':
            n = max(0, dc - db) if db > da else max(0, dc - da + 1)
            if db == da - 1:
                al = (bbr[db] * Fr(-1)) / aa[da]
                eta_rf = RF_of(dk_ncs, dk_dcs)
                if not eta_rf.is_zero():
                    # M5 收官批 #2：完备版 _limited_int_prim 退化
                    # 为比率检验——α/η 整数常数 <=> 共振；
                    # 否则朴素界正确。不再返回 undecided（消除假拒答）。
                    st_m, m_v = _limited_int_prim(al, eta_rf, de, jv - 1)
                    if st_m == 'ok' and m_v > 0:
                        n = max(n, m_v)
            elif db == da and da != 0:
                # S-a 第二阶修正（sympy bound_degree primitive db==da 分支）：
                # α 为对数导数-根式（n_l==1）时经 beta 公式再探 limited
                al = (bbr[db] * Fr(-1)) / aa[da]
                try:
                    rec = _is_logderiv_radical(al, de, jv - 1)
                except RischUnsupported:
                    return None, 'undecided'          # S-a（保守）
                if rec is None:
                    return None, 'undecided'          # S-a（保守）
                n_l, z_rf = rec
                if n_l == 1:
                    lc_a, lc_b = aa[da], bbr[db]
                    Dz = _tower_deriv_frac(z_rf.p, z_rf.q, de)
                    num = lc_a * Dz + lc_b * z_rf
                    beta = -(num / (z_rf * lc_a))
                    eta_rf = RF_of(dk_ncs, dk_dcs)
                    st_m, m_v = _limited_int_prim(beta, eta_rf, de, jv - 1)
                    if st_m == 'ok' and m_v > 0:
                        n = max(n, m_v)
            # da==db==0：cancellation 逐度下降，naive 界 n>=dc 不截断，
            # 无需共振修正（安全性：各度独立处理到底）
        else:  # exp
            n = max(0, dc - max(da, db))
            if da == db and da != 0:
                # 共振界修正：α = m·η + D(v)/v 型判定经 _pld_solve。
                # 仅干净形态（n==1、无中间层幂因子、m>0）抬界；
                # 'no'/'und'/异形一律保守 undecided（欠界会误证不可积，
                # 方向安全压倒覆盖）。
                al = (bbr[db] * Fr(-1)) / aa[da]
                try:
                    rec = _pld_solve(al, [de.ws[jv]], de, jv - 1)
                except RischUnsupported:
                    return None, 'undecided'
                if rec[0] == "ok" and rec[1] == 1 and rec[2][0] > 0:
                    n = max(n, rec[2][0])
                else:
                    return None, 'undecided'
            # da==db==0：exp 对角下降同理安全

        # ---- Step 5: spde 归约核（sympy spde 忠实移植）----
        alpha_l = [one_c]
        beta_l = []
        proved = False
        guard = 0
        while True:
            guard += 1
            if guard > 64:
                return None, 'undecided'
            if u_is_zero(cn):
                break
            if n < 0:
                proved = True
                break
            gfac = u_gcd(aa, bbr, zero)
            qa_, ra_ = u_divmod(aa, gfac, zero)
            qb_, rb_ = u_divmod(bbr, gfac, zero)
            qc_, rc_ = u_divmod(cn, gfac, zero)
            if not u_is_zero(rc_) or not u_is_zero(ra_) \
                    or not u_is_zero(rb_):
                proved = True                         # gcd ∤ => 无解
                break
            aa, bbr, cn = qa_, qb_, qc_
            if u_deg(aa) == 0:
                inv_a = one_c / aa[0]
                bbr = [c * inv_a for c in bbr]
                cn = [c * inv_a for c in cn]
                break
            rz = u_diophantine(bbr, aa, cn, zero)
            if rz is None:
                proved = True
                break
            r_, z_ = rz
            bbr = u_add(bbr, der_fn(aa), zero)
            cn = u_sub(z_, der_fn(r_))
            n -= u_deg(aa)
            beta_l = u_add(beta_l, u_mul(alpha_l, r_, zero), zero)
            alpha_l = u_mul(alpha_l, aa, zero)

        if proved:
            return None, 'proved'

        # ---- Step 6: 终解分派 ----
        if u_is_zero(cn):
            u_list = list(beta_l)
        else:
            st_f, res_u = _poly_rde_final(bbr, cn, n, case_v, base_flag,
                                          dk_deg, dk_ncs, der_fn, de, jv,
                                          zero)
            if st_f != 'ok':
                return None, st_f
            u_list = u_add(u_mul(alpha_l, res_u, zero), beta_l, zero)

    # ---- Step 7: 组合 y = u/(h·p) + 出口精确验证 ----
    oneL = [one_c]
    ynum_cs = u_mul(u_list, list(pd) or oneL, zero)
    yden_cs = u_mul(h, list(pn) or oneL, zero)
    y = RF_of(ynum_cs, yden_cs)
    dy = _tower_deriv_frac(y.p, y.q, de)
    if not (dy + f * y - g).p.is_zero():
        raise RischUnsupported(
            "internal: RDE candidate failed exact verify "
            "(this is a bug, not an honest refusal)")
    return y, 'ok'


def _exp_freq_part(freqs, de, j):
    """exp 频率分量：k=0 → 低层递归积分；k≠0 → RDE。任一频率无解
    => 不可初等证明；理论无法判定（多元 cancellation 等）=> unsupported。"""
    from cas.ratfunc import RatFunc

    tj = de.levels[j]
    xv = de.levels[0]
    expr = T.ZERO
    freq_terms = []
    rde_fail = None
    # 顶层虚指数层：±k 频率对可合并做共轭对实化（单个 k 分量不实，
    # 合并后才实——sin(2x) 类的核心形态）
    imag_top = _imag_exp_level_info(de, j) if de.cases[j] == "exp" else None
    re_pairs = {} if imag_top is not None else None
    for k in sorted(freqs):
        g = freqs[k]
        if k == 0:
            # 懒导入断环：_integrate_in_K 在门面递归驱动层
            from cas.risch import _integrate_in_K
            expr = T.plus(expr, _integrate_in_K(g, de, j))
            continue
        w = de.ws[j] * Fr(k)
        if g.q.is_const() and g.p.vars == (xv,) \
                and w.q.is_const() and w.p.vars == (xv,):
            # base 快路径：现有 ℚ(x) 极点分析求解器（无解即 proved——
            # η' 多项式保证界严格）
            b = _rde_exp_solve(k, de.ws[j].p, g.p, g.q, Poly.zero((xv,)))
            proved = b is None
        else:
            # 塔系数域：M5.2c-ii 完备判定求解器
            b, st = _rde_tower_solve(w, g, de, j)
            if st == 'proved':
                rde_fail = k
                break
            if st != 'ok':
                raise RischUnsupported(
                    "Risch DE on the tower undecidable with current theory "
                    "(%s); frequency k=%d" % (st, k))
        if b is None:
            if proved:
                rde_fail = k
                break
            raise RischUnsupported(
                "Risch DE on the tower undecidable with current theory "
                "(cancellation analysis pending); frequency k=%d" % k)
        bp = b
        if not bp.is_zero():
            # ---- 通道 A（顶层虚指数层）：±k 合并后一次共轭对实化 ----
            if re_pairs is not None:
                from cas.ratfunc import RatFunc as _RF
                if isinstance(bp, Poly):
                    re_pairs[k] = _RF.from_poly(
                        _embed(bp, tuple(de.levels[:j])))
                else:
                    re_pairs[k] = bp
                continue
            # ---- 通道 B（嵌套：虚层在系数域内）：逐 k 实化 b 本身，
            # 外层实指数因子 τ_j^k 以项形态外乘。----
            re_t = None
            if j >= 2:
                info = _imag_exp_level_info(de, j - 1)
                tau_im = de.levels[j - 1]
            else:
                info = None
            if info is not None:
                sgn_i, u_eff_i = info
                if isinstance(bp, Poly):
                    from cas.ratfunc import RatFunc as _RF
                    bp_rf = _RF.from_poly(_embed(bp, tuple(de.levels[:j])))
                else:
                    bp_rf = bp
                re_t = _realify_laurent(bp_rf, tau_im, sgn_i, u_eff_i, xv)
                if re_t is not None:
                    tk_t = T.pw(de.terms[j], N(k)) if k != 1 else de.terms[j]
                    if k < 0:
                        tk_t = T.div(T.ONE, T.pw(de.terms[j], N(-k)))
                    re_t = re_t if k == 0 else T.times(re_t, tk_t)
            if re_t is not None:
                expr = T.plus(expr, re_t)
            else:
                freq_terms.append((bp, k))
    # ---- 通道 A 汇总实化 ----
    if re_pairs and imag_top is not None:
        sgn_i, u_eff_i = imag_top
        klo, khi = min(re_pairs), max(re_pairs)
        zero_k = RatFunc.zero(tuple(de.levels[:j]))
        cs = [zero_k for _ in range(khi - klo + 1)]
        for kk, rf in re_pairs.items():
            cs[kk - klo] = rf
        n_, d_ = _from_univar(cs, tuple(de.levels[:j + 1]), tj)
        combined = RatFunc(n_, d_)
        # _from_univar 指数从 0 起：补回 klo 偏移
        if klo > 0:
            combined = combined * RatFunc(
                Poly.mono(tuple(de.levels[:j + 1]), tj, klo),
                Poly.one(tuple(de.levels[:j + 1])))
        elif klo < 0:
            combined = combined / RatFunc(
                Poly.mono(tuple(de.levels[:j + 1]), tj, -klo),
                Poly.one(tuple(de.levels[:j + 1])))
        re_t = _realify_laurent(combined, tj, sgn_i, u_eff_i, xv)
        if re_t is not None:
            expr = T.plus(expr, re_t)
        else:
            freq_terms.extend([(rf, kk) for kk, rf
                               in sorted(re_pairs.items())])
    for bk, k in freq_terms:
        bt = bk.to_term()   # 塔符号形态（出口统一回写）
        tk = T.pw(T.S(tj.name), N(k)) if k != 1 else T.S(tj.name)
        expr = T.plus(expr, T.times(bt, tk))
    if rde_fail is not None:
        from cas.pprint import to_str as _ts

        g = freqs[rde_fail]
        raise RischNonElementary(
            "not elementary: the %s component has no rational solution of "
            "the Risch differential equation y' + %d*eta'*y = %s "
            "(proved; eta' = %s)" % (
                ("t^%d" % rde_fail) if rde_fail != 1 else "t",
                rde_fail,
                _ts(g.to_term()),
                _ts(de.ws[j].to_term()),
            )
        )
    return expr
