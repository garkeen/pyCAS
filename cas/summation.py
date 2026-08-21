"""求和/差分模块（M4）：幂和公式 + Gosper 不定求和 + 定界求和。

Faulhaber 公式：Σ_{k=1}^m k^p = 1/(p+1) Σ_{j=0}^p C(p+1,j) B^+_j m^{p+1-j}
其中 B^+ 是 Bernoulli 数（B_1=+1/2 约定）。

Gosper 算法（有理函数版）：对超几何项 t(k)（即 t(k+1)/t(k) 是 k 的有理函数），
找有理函数 S(k) 使 S(k)-S(k-1)=t(k)。简化版假设 Gosper 方程的解 z 是多项式，
解线性方程组 P·f(k+1) - Q·f(k) = P（其中 r=t(k+1)/t(k)=P/Q）。

不定求和 S(x) 满足 S(x)-S(x-1) = f(x)（差分版原函数），
定界求和 Σ_{k=lo}^{hi} f(k) = S(hi) - S(lo-1)（Newton-Leibniz 的离散版）。

当前覆盖：x 的多项式（Faulhaber，含 ℚ(params) 参数系数）+ 有理函数（Gosper，Fr 系数）。
非有理函数的超几何项（阶乘/Pochhammer 表示）留给 M4 后续。
"""

from fractions import Fraction as Fr
from math import comb

from cas import term as T
from cas.term import S, N
from cas.poly import Poly, SymRat, _mk_rat, _coef_to_term, ugcd, div_exact
from cas.errors import PolyError


# ---- Bernoulli 数（B^+ 约定，B_1=+1/2，精确 Fraction，缓存）----

_BERN = [Fr(1)]  # B^+_0 = 1


def _bernoulli_plus(n):
    """第 n 个 Bernoulli 数（B^+ 约定）。递推生成 + 缓存。"""
    while len(_BERN) <= n:
        m = len(_BERN)
        s = sum(comb(m + 1, k) * _BERN[k] for k in range(m))
        _BERN.append(Fr(m + 1 - s, m + 1))
    return _BERN[n]


# ---- 幂和公式（Poly 层，自动展开合并）----

def _pow_sum_poly(x, p):
    """Σ_{k=1}^x k^p 的 Poly（关于 x）。p≥0 整数。"""
    B = [_bernoulli_plus(j) for j in range(p + 1)]
    acc = Poly.zero((x,))
    for j in range(p + 1):
        c = Fr(comb(p + 1, j) * B[j], p + 1)
        if c == 0:
            continue
        d = p + 1 - j
        acc = acc + Poly((x,), {(d,): c})
    return acc


def pow_sum(x, p):
    """Σ_{k=1}^x k^p 的闭式 term（Faulhaber 多项式）。"""
    return _pow_sum_poly(x, p).to_term()


# ---- 多项式不定求和（Faulhaber 幂和）----

def _indef_poly(t, x):
    """多项式不定求和（Faulhaber 幂和）。非多项式 → None。"""
    try:
        p = Poly.from_term(t, (x,))
    except PolyError:
        return None
    S_poly = Poly.zero((x,))
    for (i,), c in p.monos.items():
        S_poly = S_poly + _pow_sum_poly(x, i) * Poly.const((x,), c)
    return S_poly.to_term()


# ---- Gosper 算法组件（有理函数不定求和）----

def _shift_poly(p, x, j):
    """多项式移位：p(x) → p(x+j)。j 可正可负。"""
    if j == 0:
        return p
    t = p.to_term()
    shift = T.plus(x, T.N(Fr(j)))
    t_s = T.subst(t, {x: shift})
    return Poly.from_term(t_s, (x,))


def _shift_symrat(s, x, j):
    """有理函数移位：s(x) → s(x+j)。"""
    num = _shift_poly(s.num, x, j)
    den = _shift_poly(s.den, x, j)
    return _mk_rat(num, den)


def _term_to_symrat(t, x):
    """term → SymRat（x 的有理函数）。非有理函数 → None。"""
    from cas.ops import num_den
    num_t, den_t = num_den(t)
    try:
        num_p = Poly.from_term(num_t, (x,))
        den_p = Poly.from_term(den_t, (x,))
    except PolyError:
        return None
    return _mk_rat(num_p, den_p)


def _is_fr_poly(p):
    """Poly 系数是否全为 Fr（无参数）。"""
    return all(isinstance(v, Fr) for v in p.monos.values())


def _gauss_solve(M, rhs, n_vars):
    """高斯消元解 M*c = rhs。M: rows×n_vars (Fr), rhs: rows (Fr)。
    返回 c (n_vars 向量) 或 None（矛盾/无解）。"""
    rows = len(M)
    aug = [list(M[r]) + [rhs[r]] for r in range(rows)]
    pivots = []
    for col in range(n_vars):
        pivot = None
        for r in range(len(pivots), rows):
            if aug[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        aug[len(pivots)], aug[pivot] = aug[pivot], aug[len(pivots)]
        pr = len(pivots)
        pivots.append(col)
        pv = aug[pr][col]
        aug[pr] = [x / pv for x in aug[pr]]
        for r in range(rows):
            if r != pr and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [a - f * b for a, b in zip(aug[r], aug[pr])]
    for r in range(len(pivots), rows):
        if aug[r][-1] != 0:
            return None
    sol = [Fr(0)] * n_vars
    for i, col in enumerate(pivots):
        sol[col] = aug[i][-1]
    return sol


def _gosper_poly_z(t_sr, x):
    """简化 Gosper：假设 z 是多项式，解 P·f(k+1) - Q·f(k) = P。

    t_sr 是 SymRat（x 的有理函数）。返回 S SymRat 或 None。
    只处理 Fr 系数（参数系数留后续）。
    """
    if isinstance(t_sr, Fr):
        t_sr = SymRat(Poly.const((x,), t_sr), Poly.one((x,)))
    # r = t(k+1)/t(k) = P/Q
    t_plus = _shift_symrat(t_sr, x, 1)
    r = t_plus / t_sr
    if isinstance(r, Fr):
        r = SymRat(Poly.const((x,), r), Poly.one((x,)))
    P, Q = r.num, r.den
    # 只处理 Fr 系数（参数系数留后续）
    if not _is_fr_poly(P) or not _is_fr_poly(Q):
        return None
    # f 次数上界（Gosper 上界 + 余量）
    D = max(P.degree(x), Q.degree(x)) + 2
    # 构造 contributions: P·(k+1)^i - Q·k^i (i=0..D)
    contributions = []
    for i in range(D + 1):
        fi = Poly.mono((x,), x, i)
        fi_shift = _shift_poly(fi, x, 1)
        contrib = P * fi_shift - Q * fi
        contributions.append(contrib)
    # 矩阵 M[j][i] = contributions[i] 的 k^j 系数, rhs = P 的系数
    max_deg = max((c.degree(x) for c in contributions + [P] if not c.is_zero()), default=0)
    M = [[c.monos.get((j,), Fr(0)) for c in contributions] for j in range(max_deg + 1)]
    rhs_vec = [P.monos.get((j,), Fr(0)) for j in range(max_deg + 1)]
    sol = _gauss_solve(M, rhs_vec, D + 1)
    if sol is None:
        return None
    f = Poly.zero((x,))
    for i, ci in enumerate(sol):
        if ci != 0:
            f = f + Poly((x,), {(i,): ci})
    if f.is_zero():
        return None
    # S = t * f
    f_sr = _mk_rat(f, Poly.one((x,)))
    S = t_sr * f_sr
    if isinstance(S, Fr):
        S = SymRat(Poly.const((x,), S), Poly.one((x,)))
    return S


# ---- 不定求和（派发器）----

def indef_sum(t, x):
    """f(x) 的不定求和 S(x)：满足 S(x)-S(x-1) = f(x)。

    派发：多项式 → Faulhaber 幂和；有理函数 → Gosper（z 多项式）。
    非可求和 → None（拒答，诚实）。
    """
    # 先试多项式（Faulhaber）
    r = _indef_poly(t, x)
    if r is not None:
        return r
    # 再试 Gosper（有理函数，z 多项式）
    t_sr = _term_to_symrat(t, x)
    if t_sr is None:
        return None
    S = _gosper_poly_z(t_sr, x)
    if S is not None:
        return S.to_term()
    return None


# ---- 定界求和 ----

def finite_sum(f, x, lo, hi):
    """Σ_{k=lo}^{hi} f(k) = S(hi) - S(lo-1)，S 为不定求和原函数。

    lo/hi 是 term（整数或符号）。返回 term；不可求和 → None。
    """
    S = indef_sum(f, x)
    if S is None:
        return None
    up = T.subst(S, {x: hi})
    down = T.subst(S, {x: T.plus(lo, T.N(-1))})
    return T.plus(up, T.neg(down))


# ---- 差分回验（verify ΔS = f）----

def verify_indef(S, f, x, budget=10000):
    """验证 S(x)-S(x-1) = f(x)（后向差分，不定和定义）。

    支持多项式和有理函数 S；用 SymRat 检查 rem=0。
    """
    sm = T.subst(S, {x: T.plus(x, T.N(-1))})
    diff = T.plus(S, T.neg(sm))
    rem = T.plus(diff, T.neg(f))
    sr = _term_to_symrat(rem, x)
    if sr is None:
        try:
            return Poly.from_term(rem, (x,)).is_zero()
        except PolyError:
            return False
    if isinstance(sr, Fr):
        return sr == 0
    return sr.is_zero()
