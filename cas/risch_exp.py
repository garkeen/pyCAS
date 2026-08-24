# -*- coding: utf-8 -*-
"""微分域塔·exp 层积分（自 cas/risch.py 拆出）：Hermite 推广 +
Rothstein-Trager 残数（Bareiss 结式）、K[t] 视图转换、ℚ(i)-常数根、
结果组装、log 配对实化。

表示：K[t] 多项式 = 系数 list [c_0..c_n]（c_i: RatFunc，升序）；
K(t) 分式 = (A, d)（A, d: K[t]）。塔上导数见 _derive_ut。
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

from cas.risch_core import (
    RischUnsupported, RischNonElementary, DiffExt,
    _embed, _cancel, _radd, _rmul_polys,
    _tower_deriv_frac, derivation, tower_to_term_pair,
    _lin_exp_freq,
)


# ---------------------------------------------------------------------------
# M5.3.2 出口实化切片二：log 配对（Laurent 共轭自反分解）
#
# 塔答案中的 Log(u)，u 为单一虚频率指数多项式（如 1+e^{−2ix}）：替换
# z = e^{γx} 得 Laurent 多项式 L(z)；若系数满足共轭自反性
# cₙ = conj(c_{d+m−n})，则 L(e^{γx}) = e^{sγx}·Θ(x)，Θ 为实三角多项式
# ——log u 精确重写为 s·γ·x + log Θ（差常数不影响原函数；整体出口
# 经 verify 背书后才接受，失败保留复形态）。tan 类由此出真实形态。
# --------------------------------------------------------------------


def _realify_one_log(u, x, zsym):
    """Log 参数 u -> (线性校正项, 实三角 Θ term) 或 None。"""
    exps = []
    stack = [u]
    while stack:
        v = stack.pop()
        if isinstance(v, Expr) and getattr(v, "head", None) is not None:
            if v.head.name == "Exp" and len(v.args) == 1:
                exps.append(v)
                continue
            stack.extend(v.args)
    if not exps:
        return None
    freqs = {}
    for e_ in exps:
        g = _lin_exp_freq(e_.args[0], x)
        if g is None or g.im == 0:
            return None          # 本切片仅纯虚频率
        freqs[e_] = True
    gamma = _lin_exp_freq(exps[0].args[0], x)
    usub = T.subst(u, {e_: zsym for e_ in exps})
    if x in T.free_vars(usub):
        return None              # Log 参数含裸 x——本切片不处理
    try:
        lp = Poly.from_term(usub, (zsym,))
    except PolyError:
        return None
    monos = {k[0]: c for k, c in lp.monos.items()}
    degs = [n for n, c in monos.items() if c != 0]
    if not degs:
        return None
    d, m = max(degs), min(degs)
    tot = d + m
    if tot % 2 != 0:
        return None
    s = tot // 2

    def coef(n):
        return monos.get(n, Fr(0))

    for n in range(m, d + 1):
        cn, cm = coef(n), coef(tot - n)
        if isinstance(cn, Fr):
            cn = Ga(cn, Fr(0))
        if isinstance(cm, Fr):
            cm = Ga(cm, Fr(0))
        if cn != cm.conjugate():
            return None
    # Θ = z^{-s} L(z)：Hermitian 对称 -> 实三角组合
    beta = gamma.im           # z = e^{i·beta·x}
    parts = []
    cs = coef(s)
    if isinstance(cs, Fr):
        cs = Ga(cs, Fr(0))
    if cs.re != 0:
        parts.append(N(cs.re))
    hmax = max(abs(d - s), abs(s - m))
    for k in range(1, hmax + 1):
        bk = coef(s + k)
        if isinstance(bk, Fr):
            bk = Ga(bk, Fr(0))
        if bk == Ga(0, 0):
            continue
        re2 = bk.re + bk.re
        im2 = bk.im + bk.im
        # 三角参数折正（cos 偶 / sin 奇吸收符号）
        a_ = Fr(k) * beta
        argn = T.times(N(-a_ if a_ < 0 else a_), x)
        if re2 != 0:
            parts.append(T.times(N(re2), T.fn("Cos")(argn)))
        if im2 != 0:
            base = im2 if a_ < 0 else (-im2)
            parts.append(T.times(N(base), T.fn("Sin")(argn)))
    theta = T.mk(S("Plus"), tuple(parts)) if len(parts) > 1 \
        else (parts[0] if parts else N(Fr(1)))
    # 线性项 = s·γ·x（γ 经 Ga.to_term 以 i 精确重建）
    lin = T.times(N(Fr(s)), T.times(gamma.to_term(), x))
    return lin, theta


def _realify_log_pairing(expr, x):
    """出口扫描：逐个尝试 Log 配对实化；无变化返回 None。"""
    logs = []
    stack = [expr]
    while stack:
        v = stack.pop()
        if isinstance(v, Expr) and getattr(v, "head", None) is not None:
            if v.head.name == "Log" and len(v.args) == 1:
                logs.append(v)
                continue
            stack.extend(v.args)
    subs = {}
    zid = [0]
    for lg in logs:
        zid[0] += 1
        zs = S(f"_rz{zid[0]}")
        r = _realify_one_log(lg.args[0], x, zs)
        if r is None:
            continue
        lin, theta = r
        subs[lg] = T.plus(lin, T.fn("Log")(theta))
    if not subs:
        return None
    return T.subst(expr, subs)


# ---------------------------------------------------------------------------
# M5.1a/M5.2：塔上 K[t] 视图积分（t = exp(eta) 或 primitive θ）
#
# 表示：K[t] 多项式 = 系数 list [c_0..c_n]（c_i: RatFunc——K = Q(x) 显式
#       有理函数域，M5.2 起；升序）；K(t) 分式 = (A, d)（A, d: K[t]）。
# 塔上导数 D: K[t] -> K[t]（K 是域，Dθ = v ∈ K 或 Dt = η'·t）：
#   exp:       D(Σa_k t^k)  = Σ (Da_k + k·η'·a_k) t^k          （对角）
#   primitive: D(Σa_k θ^k)  = Σ_i (Da_i + (i+1)·v·a_{i+1}) θ^i  （移位）
# special 因子：exp 的 t（gcd(t,Dt)=t≠1）；primitive 无（gcd(θ,v)=1，
#   θ 正规）——primitive 全部因子走 normal 路线。
# ---------------------------------------------------------------------------


def _from_univar(coeffs, all_vars, ti):
    """系数 list（RatFunc）-> 塔上 (num, den) Poly 对。"""
    j = all_vars.index(ti)

    def shift(p, e):
        # embed 后 p 已含 t 维度（指数 0）——替换位置 j 的指数，非插入
        return Poly(all_vars, {k[:j] + (e,) + k[j + 1:]: c
                               for k, c in p.monos.items()})

    num = Poly.zero(all_vars)
    den = Poly.one(all_vars)
    for e, c in enumerate(coeffs):
        if c.is_zero():
            continue
        pe = shift(_embed(c.p, all_vars), e)
        qe = _embed(c.q, all_vars)      # 分母不带 θ^e 权重
        num = num * qe + den * pe
        den = den * qe
    return _cancel(num, den)


def _derive_ut(coeffs, de, j):
    """塔上 D 作用于 Σ a_k t_j^k -> K[t] 系数 list（K 是域，无分母）。

    exp:       D(Σa_k t^k) = Σ (Da_k + k·η'·a_k) t^k          （对角）
    primitive: D(Σa_k θ^k) = Σ_i (Da_i + (i+1)·v·a_{i+1}) θ^i  （移位）
    """
    from cas.ratfunc import RatFunc

    w = de.ws[j]
    zv = RatFunc.zero(w.p.vars)   # 系数域零元（vars = levels[:j]）
    n = len(coeffs)
    out = []
    for i in range(n):
        a = coeffs[i]
        # K 层导数必须是塔上导数 D_K（多层时 d/dx 不够——D(l)=1/x 类）
        term = _tower_deriv_frac(a.p, a.q, de) if not a.is_zero() else zv
        if de.cases[j] == "exp":
            if i > 0 and not a.is_zero():
                term = term + a * w * Fr(i)
        else:  # primitive：右邻贡献 (i+1)·v·a_{i+1}
            if i + 1 < n and not coeffs[i + 1].is_zero():
                term = term + coeffs[i + 1] * w * Fr(i + 1)
        out.append(term)
    return u_trim(out)


def _exp_w(de, j):
    """第 j 层的 w = D(t)/t 或 D(θ)（RatFunc）。"""
    return de.ws[j]


# ---------------------------------------------------------------------------
# M5.1b：Risch 微分方程 exp case——y' + k*eta'*y = g（y ∈ Q(x)）
#
# 极点分析：p^m ∥ denom(y) => y' 有 p^{m+1} 极点而 k*eta'*y 只有 p^m
# （eta' 多项式）=> p^{m+1} | denom(g)。故 denom(y) 的界
# D = Π p^{e-1}（p^e ∥ denom(g)，e>=2）；z = y*D 多项式化后待定系数。
# f = k*eta' != 0 保证齐次多项式解只有 0（deg y' < deg f*y）=> 解唯一。
# ---------------------------------------------------------------------------

def _poly_to_list(p):
    """Poly((x,)) -> 升序 Fr 系数 list。"""
    xv = p.vars[0]
    d = p.degree(xv)
    out = [Fr(0)] * (d + 1)
    for k, v in p.monos.items():
        out[k[0]] = v
    return out


def _list_to_poly(cs, vars_):
    """升序 Fr list -> Poly（一元）。"""
    return Poly(vars_, {(e,): c for e, c in enumerate(cs) if c != 0})


def _gauss_solve(M, b):
    """Fr 系数线性方程组高斯消元。返回解 list | None（无解）。

    自由变量取 0（f != 0 时 RDE 齐次只有零解，理论保证无自由变量；
    此处取 0 为防御性特解）。
    """
    n = len(M)
    cols = len(M[0]) if n else 0
    A = [row[:] + [b[i]] for i, row in enumerate(M)]
    piv_cols = []
    r = 0
    for cidx in range(cols):
        piv = None
        for i in range(r, n):
            if A[i][cidx] != 0:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][cidx]
        A[r] = [v / pv for v in A[r]]
        for i in range(n):
            if i != r and A[i][cidx] != 0:
                fac = A[i][cidx]
                A[i] = [vi - fac * vr for vi, vr in zip(A[i], A[r])]
        piv_cols.append(cidx)
        r += 1
        if r == n:
            break
    for i in range(n):
        if all(v == 0 for v in A[i][:cols]) and A[i][-1] != 0:
            return None
    z0 = b[0] * 0 if n else Fr(0)   # 系数域零元（Fr/Ga 通用）
    sol = [z0] * cols
    for i, cidx in enumerate(piv_cols):
        sol[cidx] = A[i][-1]
    return sol


def _rde_exp_solve(k, eta_p, an, ad, zero):
    """解 y' + k*eta'*y = an/ad（y ∈ Q(x)）。返回 y: Poly | None。

    None = 无有理解（该频率分量不可初等的证明载体）。
    """
    xv = zero.vars[0]
    f = eta_p.scalar(Fr(k))
    # 步骤1：分母界 D = Π p^{e-1}（p^e ∥ denom(g)，e>=2）
    Dp = Poly.one(zero.vars)
    from cas.factor import squarefree_decomp

    for pp, e in squarefree_decomp(ad):
        if e >= 2:
            Dp = Dp * pp ** (e - 1)
    # 步骤2：z = y*D；两边乘 ad：ad*D*z' + (f*D − D')*ad*z = an*D²
    A_ = ad * Dp
    B_ = (f * Dp - Dp.deriv(xv)) * ad
    C_ = an * Dp * Dp
    degB = B_.degree(xv)
    degC = C_.degree(xv)
    if degB < 0:
        # B ≡ 0：f*D = D' 且 ad 常数——eta' 多项式时仅 f=0，已排除
        raise RischUnsupported("degenerate RDE (f*D == D')")
    N = degC - degB
    if N < 0:
        # z 只能 = 0；rhs 非零即无解
        return None if not C_.is_zero() else Poly.zero(zero.vars)
    # 步骤3：待定系数线性方程组
    A_l = _poly_to_list(A_)
    B_l = _poly_to_list(B_)
    C_l = _poly_to_list(C_)
    ncols = N + 1
    top = max(len(C_l) - 1, (len(B_l) - 1) + N,
              (len(A_l) - 1) + (N - 1) if N > 0 else 0)
    nrows = max(top, len(C_l) - 1) + 1
    M = [[Fr(0)] * ncols for _ in range(nrows)]
    rhs_v = [Fr(0)] * nrows
    for i, cv in enumerate(C_l):
        rhs_v[i] = cv
    for ci in range(ncols):
        # 基 z = x^ci：LHS = A*(ci*x^(ci-1)) + B*x^ci
        if ci > 0:
            for ai, av in enumerate(A_l):
                m = ai + ci - 1
                M[m][ci] += av * Fr(ci)
        for bi, bv in enumerate(B_l):
            M[bi + ci][ci] += bv
    sol = _gauss_solve(M, rhs_v)
    if sol is None:
        return None
    return _list_to_poly(sol, zero.vars)


def risch_exp_integrate(fa, fd, de, j):
    """exp 单项式积分主入口（M5.1：真分式 + 频率分解）。

    返回 ((rat_part, logs, nonel, leftover), freqs, status)：
    freqs = {k: g_k}（g_k: RatFunc）——全部非零频率分量（正幂商 +
    负幂低幂 + residue t 幂剩余），k≠0 待 RDE；status: 'ok'。
    """
    from cas.ratfunc import RatFunc

    zero = RatFunc.zero((de.levels[0],))
    tj = de.levels[j]

    A = from_poly(fa, tj)
    D = from_poly(fd, tj)
    if u_is_zero(A):
        return (None, None, None, None), {}, "ok"

    # 多项式部分：商 Q 的频率 + 真分式 R
    dq = len(D) - 1
    dp = len(A) - 1
    pos_freqs = {}
    if dp >= dq:
        Q, R = u_divmod(A, D, zero)
        for k, c in enumerate(Q):
            if not c.is_zero():
                pos_freqs[k] = c
        A = R
        if u_is_zero(A):
            return (None, None, None, None), pos_freqs, "ok"

    res, neg_freqs, st = _integrate_proper(A, D, de, j, zero)
    freqs = dict(pos_freqs)
    for k, v in neg_freqs.items():
        freqs[k] = freqs[k] + v if k in freqs else v
    return res, freqs, st


def _integrate_proper(A, D, de, j, zero):
    """真分式积分：special 分离（仅 exp）+ 无平方分解 + Hermite + residue。

    返回 ((rat_part, logs, nonel, leftover), neg_freqs, status)：
    neg_freqs = {k: g_k}——t 负幂频率分量（k<0，M5.1b RDE 处理）。
    primitive 层无 special 因子（gcd(θ,v)=1，θ 正规），全走 normal。
    """
    if de.cases[j] == "primitive":
        res, st = _integrate_normal(A, D, de, j, zero)
        return res, {}, st
    # special 分离：D = t^m * q0（q0[0] != 0）
    m = 0
    q0 = list(D)
    while len(q0) > 0 and q0[0].is_zero():
        q0 = q0[1:]
        m += 1
    q0 = u_trim(q0)
    if m > 0:
        k_m = min(m, len(A))
        low, high = A[:k_m], A[k_m:]
        # 低段 Σ a_k t^{k-m}（负幂频率）；高段走正规路线
        neg_freqs = {}
        for k, c in enumerate(low):
            if not c.is_zero():
                neg_freqs[k - m] = c
        if u_is_zero(high):
            return (None, None, None, None), neg_freqs, "ok"
        res, st = _integrate_normal(high, q0, de, j, zero)
        rat_part, logs, nonel, leftover = res
        if isinstance(leftover, tuple) and leftover \
                and leftover[0] == "special":
            # residue 剩余的 t 幂部分 -> 正频（与 m==0 分支同款转换；
            # 键空间不相交：neg k<0 / pos k>=0）
            pos_freqs = {k: c for k, c in enumerate(leftover[1])
                         if not c.is_zero()}
            return (rat_part, logs, nonel, None), \
                {**neg_freqs, **pos_freqs}, st
        return res, neg_freqs, st
    res, st = _integrate_normal(A, D, de, j, zero)
    rat_part, logs, nonel, leftover = res
    if isinstance(leftover, tuple) and leftover and leftover[0] == "special":
        # residue 剩余的 t 幂部分 -> 正频
        pos_freqs = {k: c for k, c in enumerate(leftover[1]) if not c.is_zero()}
        return (rat_part, logs, nonel, None), pos_freqs, st
    return res, {}, st


def _integrate_normal(A, D, de, j, zero):
    """正规分母真分式：无平方分解 -> 部分分式 -> Hermite(e>1) + residue(e=1)。

    返回 (rat_part, logs, nonel, leftover, status)：
    rat_part = [(u_k, p, k)] 有理部分 u_k/p^k；logs = [(c, g)] 对数项；
    nonel = (num, p)|None 不可初等剩余（residue 无常数根——Bronstein 定理：
    真分式情形 residue 失败即证明不可初等）；leftover = K 分式递归 x 层。
    """
    tj = de.levels[j]
    factors = _squarefree_decomp_t(D, zero)
    rat_part = []
    logs = []
    nonel = None
    leftover = None
    for p, e in factors:
        cof = u_divmod(D, u_pow(p, e, zero), zero)[0]
        B = u_divmod(u_mul(A, u_inv_mod_t(cof, D, zero), zero), u_pow(p, e, zero), zero)[1]
        if e > 1:
            rat, (B1, _) = _hermite_pe(B, p, e, de, j, zero)
            rat_part.extend(rat)
        else:
            B1 = B
        lg, rem = _residue_sqfr(B1, p, de, j, zero)
        logs.extend(lg)
        if not u_is_zero(rem):
            q, r = u_divmod(rem, p, zero)
            if u_is_zero(r):
                # 剩余恰为多项式：exp 下全部进频率（k=0 分量由低层递归
                # 积分处理）；primitive 下回本层多项式循环（leftover）
                if de.cases[j] == "exp":
                    return (rat_part, logs, None, ("special", q)), "ok"
                leftover = q if leftover is None else u_add(leftover, q, zero)
            else:
                nonel = (rem, p)
    return (rat_part, logs, nonel, leftover), "ok"


def _squarefree_decomp_t(D, zero):
    """K[t] 无平方分解 [(p, e)]（形式导数 gcd 递归）。"""
    def rec(cur):
        if len(cur) <= 1 or u_is_zero(cur):
            return []
        dc = u_formal_deriv(cur)
        g = u_gcd(cur, dc, zero)
        if len(g) <= 1:
            return [(cur, 1)]
        core, r = u_divmod(cur, g, zero)
        if not u_is_zero(r):
            raise RischUnsupported("squarefree division failed")
        rest = rec(g)
        single = core
        for pp, _mm in rest:
            single = u_divmod(single, pp, zero)[0]
        out = [(pp, mm + 1) for pp, mm in rest]
        if len(single) > 1:
            out.append((single, 1))
        return out

    out = rec(list(D))
    # 规范序：按次数升序稳定组装
    return sorted(out, key=lambda pe: len(pe[0]))


def _hermite_pe(a, p, e, de, j, zero):
    """∫ a/p^e（p 无平方正规）-> (有理部分 [(u_k, p, k)], 剩余 (b, p))。

    逐层：u ≡ -(k-1)^{-1}*(a mod p)*inv(D(p)) (mod p)；
    v = (a + (k-1)*u*D(p))/p - D(u)，整除性由 u 构造保证。
    """
    rat = []
    cur_a, cur_e = list(a), e
    while cur_e >= 2:
        u, v = _hermite_factor(cur_a, p, cur_e, de, j, zero)
        if not u_is_zero(u):
            rat.append((u, p, cur_e - 1))
        cur_a = v
        cur_e -= 1
    return rat, (cur_a, p)


def _hermite_factor(a, p, e, de, j, zero):
    """单层剥离：∫ a/p^e -> 贡献 u/p^{e-1}，剩余 v/p^{e-1}。

    u ≡ -(e-1)^{-1}·(a mod p)·inv(D(p) mod p) (mod p)（K 域上，无 wd 因子）。
    """
    Pm = _derive_ut(p, de, j)             # D(p)：K[t] 元素
    r = u_divmod(a, p, zero)[1]
    pm1 = u_inv_mod(Pm, p, zero)
    coef = Fr(-1) / (e - 1)
    u = [c * coef for c in u_mul(r, pm1, zero)]
    _, u = u_divmod(u, p, zero)
    # N = a + (e-1)*u*D(p) 整除 p
    N_ = u_add(list(a), u_mul([c * Fr(e - 1) for c in u], Pm, zero), zero)
    M, rem = u_divmod(N_, p, zero)
    if not u_is_zero(rem):
        raise RischUnsupported("hermite divisibility failed")
    Du = _derive_ut(u, de, j)
    v = u_add(M, u_neg(Du, lambda c: c * Fr(-1)), zero)
    return u, v


# ---------------------------------------------------------------------------
# residue_reduce（Rothstein-Trager；结式经 Bareiss 行列式，K[z] 系数）
# ---------------------------------------------------------------------------

def _neg_poly(c):
    return c * Fr(-1)


def _sylvester_res(fz, gz):
    """res_t(f, g)：fz/gz 是 K[z] 多项式（list[K 元素]，z 升序——与 K[t] 同构）。

    Sylvester 矩阵 + Bareiss 行列式（K[z] 整环上 exact division）。
    行列式与标准结式至多差符号——求根用途下无关紧要。
    """
    from cas.ratfunc import RatFunc

    m = len(fz) - 1     # deg f
    n = len(gz) - 1     # deg g
    size = m + n
    if size <= 0:
        return []
    M = []
    for i in range(n):
        row = [[] for _ in range(size)]
        for jj in range(i, min(i + m + 1, size)):
            row[jj] = fz[m - (jj - i)]
        M.append(row)
    for i in range(m):
        row = [[] for _ in range(size)]
        for jj in range(i, min(i + n + 1, size)):
            row[jj] = gz[n - (jj - i)]
        M.append(row)
    zero = RatFunc.zero((T.S("x"),))
    return _bareiss_det(M, size, zero)


# ---------------------------------------------------------------------------
# Bareiss 行列式（元素 = K[z] 多项式 = list[K 元素]，与 K[t] 同构——_u_* 通用）
# ---------------------------------------------------------------------------


def _bareiss_det(M, size, zero):
    """Bareiss 分式免除行列式（元素为 K[z] 多项式，_u_* 层直接适用）。"""
    A = [row[:] for row in M]
    prev = None         # 上一步主元；第一步除数为 1（不除）
    sign = 1
    for k in range(size - 1):
        if u_is_zero(A[k][k]):
            for i in range(k + 1, size):
                if not u_is_zero(A[i][k]):
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return []
        pk = A[k][k]
        for i in range(k + 1, size):
            for jj in range(k + 1, size):
                num = u_sub(u_mul0(A[i][jj], pk), u_mul0(A[i][k], A[k][jj]))
                if prev is not None:
                    q, r = u_divmod(num, prev, zero)
                    if not u_is_zero(r):
                        raise RischUnsupported("bareiss exact division failed")
                    A[i][jj] = q
                else:
                    A[i][jj] = num
        prev = pk
    det = u_trim(A[size - 1][size - 1])
    det = _uz_trim_det(det)
    return det if sign == 1 else u_neg(det, lambda c: c * Fr(-1))


def _uz_trim_det(p):
    return u_trim(p)


def _residue_sqfr(B, p, de, j, zero):
    """∫ B/p（p 无平方正规）-> (logs [(c, g)], rem)。

    R(z) = res_t(B - z*D(p), p)；常数根 c（free of x）->
    贡献 c*log(g)，g = gcd(p, B - c*D(p))；剩余 rem（分母仍 p）
    = 不可初等成分。Bronstein 定理：真分式 + 无常数根 => 不可初等
    （M5.1b 补多项式部分后为完整证明）。solve 无法定根时显式异常——
    绝不静默把可积成分误判为不可积。
    """
    Dp = _derive_ut(p, de, j)
    nb = max(len(B), len(Dp))
    Bp = B + [zero for _ in range(nb - len(B))]
    Dpp = Dp + [zero for _ in range(nb - len(Dp))]
    # fz[i] = B_i - z*Dp_i（K[z] 多项式 = list[K 元素]）
    fz = [[b, _neg_poly(d)] for b, d in zip(Bp, Dpp)]
    gz = [[c] for c in p]
    Rz = _sylvester_res(fz, gz)
    logs = []
    rem = list(B)
    if len(Rz) >= 1 and not u_is_zero(Rz):
        roots = _constant_roots(Rz, xv=de.levels[0])
        for c in roots:
            # fc = fz 代入 z=c：b + c*(-d)
            fc = []
            for zp in fz:
                val = zp[0]
                if len(zp) > 1:
                    val = val + zp[1] * c
                fc.append(val)
            fc = u_trim(fc)
            g = u_gcd(fc, p, zero)
            if len(g) <= 1:
                continue
            logs.append((c, g))
            Dg = _derive_ut(g, de, j)
            cof = u_divmod(p, g, zero)[0]
            ct = zero.one(zero.p.vars) * c
            corr = u_mul([ct], u_mul(Dg, cof, zero), zero)
            rem = u_add(rem, u_neg(corr, lambda cc: cc * Fr(-1)), zero)
    return logs, u_trim(rem)


def _uz_trim_list(cs):
    return u_trim(cs)


def _iter_subterms(t):
    stack = [t]
    while stack:
        u = stack.pop()
        yield u
        if isinstance(u, Expr):
            stack.extend(u.args)


def _term_to_ga(t):
    """term -> Ga（仅含数字与符号 i 的线性形态）；否则 None。"""
    fv = T.free_vars(t)
    if any(v.name != "i" for v in fv):
        return None
    try:
        return Ga.from_term_val(t)
    except Exception:
        return None


def _frac_sqrt(f):
    """有理数的精确平方根；非 Fr 或非完全平方返回 None。"""
    from math import isqrt

    if not isinstance(f, Fr):
        return None          # SymRat/Ga 判别式：非有理平方根
    if f < 0:
        return None
    rn, rd = isqrt(f.numerator), isqrt(f.denominator)
    if rn * rn != f.numerator or rd * rd != f.denominator:
        return None
    return Fr(rn, rd)


def _ga_sqrt_exact(g):
    """Ga 的精确平方根（系数有理域内）；非完全平方返回 None。"""
    A, B = g.re, g.im
    n = A * A + B * B
    sn = _frac_sqrt(n)
    if sn is None:
        return None
    u2 = (A + sn) / 2
    su = _frac_sqrt(u2)
    if su is None:
        return None
    if su == 0:
        sv = _frac_sqrt((A - sn) / 2)
        if sv is None:
            return None
        return Ga(Fr(0), sv)
    return Ga(su, B / (2 * su))


def _const_roots_ga_quad(Rz):
    """R(z) 全 ℚ(i)-常数且次数 ≤2 时精确求根；否则 None。"""
    cs = [c for c in Rz if not c.is_zero()]
    if not cs or len(cs) > 3:
        return None
    vals = []
    for c in cs:
        g = rf_const_ga(c)
        if g is None:
            return None
        vals.append(g)
    if len(vals) == 1:
        return []
    if len(vals) == 2:
        return [-vals[0] / vals[1]]
    a2, b1, c0 = vals
    disc = b1 * b1 - a2 * c0 * 4
    s = _ga_sqrt_exact(disc)
    if s is None:
        return None
    two = Ga(2)
    return [(-b1 + s) / (a2 * 2), (-b1 - s) / (a2 * 2)]


def _term_to_symrat(t_):
    """term -> SymRat（参数/AN 轨道）：显式 (num, den) 对算术求值。

    M5.4 审计修复：残数根落在 ℚ(params,α) 时不再误判为不可积。
    solve 返回的解可能是未规范嵌套分式（如 1/(a²·(-1/a)))——其内部
    结构与打印同形的 parse 树不同，from_term 分支覆盖不了；此处用
    自底向上 (num,den) 对算术（加/乘/整幂/取逆）完全可控。不支持
    形态返回 None。"""
    from cas.poly import _mk_rat

    vs = tuple(sorted(T.free_vars(t_), key=lambda s_: s_.name))
    zero_k = tuple(0 for _ in vs)

    def nd(u):
        # 全部叶子直接在 vs 全空间构造——避免跨空间乘法的 var mismatch
        if T.is_num(u):
            return Poly(vs, {zero_k: T.num_val(u)}), Poly.one(vs)
        if isinstance(u, Sym):
            k = [0] * len(vs)
            k[vs.index(u)] = 1
            return Poly(vs, {tuple(k): Fr(1)}), Poly.one(vs)
        h = getattr(u, "head", None)
        if h is None:
            raise ValueError("atom")
        n = h.name
        if n == "Plus":
            rn = Poly.zero(vs)
            rd = Poly.one(vs)
            for a_ in u.args:
                pn, pd = nd(a_)
                rn, rd = rn * pd + pn * rd, rd * pd
            return rn, rd
        if n == "Times":
            rn, rd = Poly.one(vs), Poly.one(vs)
            for a_ in u.args:
                pn, pd = nd(a_)
                rn, rd = rn * pn, rd * pd
            return rn, rd
        if n == "Power":
            b_, e_ = u.args
            if not isinstance(e_, T.Int):
                raise ValueError("non-int power")
            pn, pd = nd(b_)
            bn, bd = Poly.one(vs), Poly.one(vs)
            if e_.v >= 0:
                for _ in range(e_.v):
                    bn, bd = bn * pn, bd * pd
            else:
                for _ in range(-e_.v):
                    bn, bd = bn * pd, bd * pn
            return bn, bd
        raise ValueError("head " + n)

    try:
        num, den = nd(t_)
        sr = _mk_rat(num, den)
        return sr if isinstance(sr, (SymRat, Fr)) else None
    except Exception:
        return None


def _constant_roots(Rz, xv=None):
    """R(z) ∈ Q(x)[z] 的常数根：转 term 用 solve，含 x 的根丢弃。

    含 x 的根被丢弃正是数学语义：非常数 residue 不对应初等对数项。
    solve 无法判定（unsupported）时抛异常——绝不静默漏根（漏根会把
    可积成分误判为不可初等，违反永不静默错）。根值表示三级回退：
    数值 Fr / ℚ(i)（_term_to_ga）/ ℚ(params,α)（_term_to_symrat，
    M5.4 审计扩容——残数根可安全停留在参数轨道：形式恒等对特化
    保真）；更高阶代数根（真 RootOf 域）显式异常。"""
    # M5 收官批 #3：系数含 SymRat 分母时 solve 报 "not polynomial"。
    # 用 together+numerator 在项级清分母——根不变（乘非零常数倍）。
    from cas.solve import solve as _solve
    from cas.ratfunc import RatFunc

    z = T.S("_rz")
    terms = []
    for e, c in enumerate(Rz):
        if c.is_zero():
            continue
        ct = c.to_term()
        terms.append(T.times(ct, T.pw(z, N(e))) if e else ct)
    if not terms:
        return []
    poly_t = T.mk(S("Plus"), tuple(terms)) if len(terms) > 1 else terms[0]
    # 项级清分母：together 取公分母，numerator 取分子
    # （SymRat 内嵌分母在项级暴露为分数；together 合并后 numerator
    #  揽出多项式分子——根不变，乘非零常数倍。常数多项式无变量时
    #  together 会报 "no variables"——此无害，回退原始项由 solve 处理）
    try:
        from cas.ops import together as _together, numerator as _numer
        cleared = _numer(_together(poly_t))
    except Exception:
        cleared = poly_t
    r = _solve(cleared, z)
    if r.status != "ok":
        # ℚ(i) 常数低次回退：精确二次/一次求根（三角残数常为 ±i 型）
        fb = _const_roots_ga_quad(Rz)
        if fb is not None:
            return fb
        raise RischUnsupported(
            "cannot determine constant roots of the resultant: " + (r.note or ""))
    out = []
    for sol in r.solutions:
        if not _free_of_x(sol):
            continue
        if not T.is_num(sol):
            ga = _term_to_ga(sol)
            if ga is not None:
                out.append(ga)
                continue
            sr = _term_to_symrat(sol)
            if sr is not None:
                out.append(sr)
                continue
            # M7.1 z-常数中间层：残数根落在 ℚ(α)（数值底根式常数，
            # 如 ±1/(4√2) ∈ ℚ(√2)）——经统一登记处建 AlgField、以
            # 参数化符号形态穿过系数算术（乘积出口模约简保次数有界），
            # 出口由 TowerStruct.compute 统一回化根式形态再验证。
            sr = _alg_const_coeff(sol, xv=xv)
            if sr is not None:
                out.append(sr)
                continue
            raise RischUnsupported(
                "algebraic residue roots beyond radical constants pending "
                "(RootOf/nested forms: M7.2/M7.3)")
        out.append(T.num_val(sol))
    return out


def _alg_const_coeff(sol, xv=None):
    """代数常数根 term -> 系数域形态（SymRat over 参数化符号）。

    遍历解项中的数值底有理指数幂叶，逐叶经 risch_core._collect_radical
    登记 AlgField（ALG_FIELDS 单一来源，M7.0-b），解项替换为符号多项式
    后走既有 SymRat 通道。非根式可吸收形态返回 None（诚实上抛）。
    """
    from cas.risch_core import _collect_radical

    subs = {}
    stack = [sol]
    while stack:
        u = stack.pop()
        if isinstance(u, T.Expr):
            if u.head.name == "Power":
                _b, _e = u.args
                if T.is_num(_b) and isinstance(_e, T.Rat):
                    _collect_radical(u, subs)
                    continue
                if xv is not None and isinstance(_e, T.Rat) \
                        and xv not in T.free_vars(_b):
                    _collect_radical(u, subs, xv=xv)
                    continue
                stack.extend(u.args)
                continue
            stack.extend(u.args)
    if not subs:
        return None
    s2 = T.subst(sol, subs)
    if _free_of_x(s2):
        # M7.2 边界守卫：符号底根式常数（√(a²−4) 类，key[0]=='sym'）
        # 一旦进入残数循环，系数域实为 ℚ(params)[α]——当前 RatFunc
        # 系数层无商环感知算术，gcd/结式链次数爆炸（实测挂死级）。
        # 如实拒答，等待代数层入塔（M8.1）。数值底（√2 类）系数是
        # 标量叶，不触发，M7.1 路径照常解锁。
        from cas.algfield import ALG_FIELDS
        if any(ALG_FIELDS[s_].key is not None
               and ALG_FIELDS[s_].key[0] == "sym"
               for s_ in subs.values() if s_ in ALG_FIELDS):
            raise RischUnsupported(
                "residue roots in Q(params,alpha) pending "
                "coefficient-field upgrade (M8.1 algebraic layer)")
        return _term_to_symrat(s2)
    return None


def _free_of_x(t):
    xv = T.S("x")
    return xv not in T.free_vars(t)


# ---------------------------------------------------------------------------
# 结果组装（塔 -> term）
# ---------------------------------------------------------------------------

def assemble_exp_result(rat_part, logs, nonel, de, j):
    """积分结果 -> 塔符号 term（不回写——出口统一 backsubst）。"""
    tj = de.levels[j]
    rat_part = rat_part or []
    logs = logs or []
    parts = []
    for u, p, k in rat_part:
        un, ud = _from_univar(u, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        ut = tower_to_term_pair(un, ud, de, backsub=False)
        pt = tower_to_term_pair(pn, pd, de, backsub=False)
        parts.append(T.div(ut, T.pw(pt, N(k))))
    for c, g in logs:
        gn, gd = _from_univar(g, de.vars, tj)
        gt = tower_to_term_pair(gn, gd, de, backsub=False)
        ct = c.to_term() if hasattr(c, "to_term") else N(c)
        parts.append(T.times(ct, T.log(gt)))
    if nonel is not None:
        num, p = nonel
        nn, nd = _from_univar(num, de.vars, tj)
        pn, pd = _from_univar(p, de.vars, tj)
        from cas.pprint import to_str as _ts

        raise RischNonElementary(
            "integral of " + _ts(T.div(
                tower_to_term_pair(nn, nd, de, backsub=False),
                tower_to_term_pair(pn, pd, de, backsub=False))) +
            " over the tower is not elementary (no constant residue roots)"
        )
    if not parts:
        return T.ZERO
    if len(parts) == 1:
        return parts[0]
    return T.mk(S("Plus"), tuple(parts))
