"""求和/差分模块（M4 第一步）：幂和公式 + 不定求和 + 定界求和。

Faulhaber 公式：Σ_{k=1}^m k^p = 1/(p+1) Σ_{j=0}^p C(p+1,j) B^+_j m^{p+1-j}
其中 B^+ 是 Bernoulli 数（B_1=+1/2 约定），递推：
  B^+_0 = 1;  Σ_{k=0}^m C(m+1,k) B^+_k = m+1  (m≥1)
  ⟹  B^+_m = [m+1 - Σ_{k=0}^{m-1} C(m+1,k) B^+_k] / (m+1)

不定求和 S(x) 满足 S(x)-S(x-1) = f(x)（差分版原函数），
定界求和 Σ_{k=lo}^{hi} f(k) = S(hi) - S(lo-1)（Newton-Leibniz 的离散版）。

当前覆盖：x 的多项式（含 ℚ(params) 参数系数，复用 Poly 算术）。
超几何项 / Gosper / 常系数递推留给 M4 后续。
"""

from fractions import Fraction as Fr
from math import comb

from cas import term as T
from cas.term import S, N
from cas.poly import Poly, _coef_to_term
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


# ---- 不定求和（差分版原函数）----

def indef_sum(t, x):
    """f(x) 的不定求和 S(x)：满足 S(x)-S(x-1) = f(x)。

    当前：x 的多项式（含 ℚ(params) 参数系数）。非多项式 → None（拒答，诚实）。
    Poly 算术自动展开合并，输出规范形。
    """
    try:
        p = Poly.from_term(t, (x,))
    except PolyError:
        return None
    S_poly = Poly.zero((x,))
    for (i,), c in p.monos.items():
        S_poly = S_poly + _pow_sum_poly(x, i) * Poly.const((x,), c)
    return S_poly.to_term()


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

    对称于积分 verify D(F)=f；用 Poly.from_term 展开并归零检查（环层规范形，可靠）。
    """
    sm = T.subst(S, {x: T.plus(x, T.N(-1))})
    diff = T.plus(S, T.neg(sm))
    rem = T.plus(diff, T.neg(f))
    try:
        return Poly.from_term(rem, (x,)).is_zero()
    except PolyError:
        return False
