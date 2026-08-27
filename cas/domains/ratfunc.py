"""K(x₁..xₙ) 有理函数域：分子/分母稀疏多项式对。

标准形：分子分母各自展开收集（未必约简——多变量 GCD 通用算法就位前
不做约简，见下）。判等 = 交叉相乘精确比较（ad == bc），片段内完全
判定，不依赖约简。

诚实的分层：
· normalize 的输出对"相等但未约简"的输入不唯一（x/2 与 2x/4 展开
  形态不同）——它不是商域的完整规范形；
· equal 是完全判定（交叉相乘恒等式），这是通用算法而非权宜；
· 约简标准形 = 多变量 GCD 之后的事：单变量欧几里得 GCD 已在
  poly.p_gcd_univar 实现，届时作为快路径接入 equal 之前降低规模。

结构：K[x] ⊂ K(x)，转换先走多项式快路径（poly.from_term 直接命中），
失手再按有理复合递归——一条通路，无分支特判。
"""

from dataclasses import dataclass

from cas import term as T
from cas.term import Expr, Int
from cas.domains.base import Domain, Ring
from cas.domains.poly import (Poly, p_add, p_mul, p_neg, p_scale, _norm,
                              to_term, from_term as poly_from_term,
                              p_gcd_univar, p_divmod_field, p_deriv)


@dataclass(frozen=True, slots=True)
class RatFunc:
    """不变量：den 非零。num/den 为同变量集 Poly。"""
    num: Poly
    den: Poly


# ---------------------------------------------------------------------------
# dict 中间态算术（构造期；Poly 冻结在出口统一完成）
# ---------------------------------------------------------------------------

def _add(ring, a: dict, b: dict) -> dict:
    d = dict(a)
    for k, c in b.items():
        d[k] = ring.add(d.get(k, ring.from_int(0)), c)
        if ring.is_zero(d[k]):
            del d[k]
    return d


def _mul(ring, a: dict, b: dict) -> dict:
    d = {}
    for ka, ca in a.items():
        for kb, cb in b.items():
            k = tuple(x + y for x, y in zip(ka, kb))
            d[k] = ring.add(d.get(k, ring.from_int(0)), ring.mul(ca, cb))
    return {k: c for k, c in d.items() if not ring.is_zero(c)}


def _scale(ring, a: dict, c) -> dict:
    if ring.is_zero(c):
        return {}
    return {k: ring.mul(c, m) for k, m in a.items()}


def _pow(ring, a: dict, n: int) -> dict:
    r = {(0,) * _width(a): ring.from_int(1)}
    b = a
    while n:
        if n & 1:
            r = _mul(ring, r, b)
        n >>= 1
        if n:
            b = _mul(ring, b, b)
    return r


def _width(a: dict) -> int:
    return len(next(iter(a))) if a else 0


def _is_zero(a: dict) -> bool:
    return not a                       # 构造期不变量：零系数不驻留字典


# ---------------------------------------------------------------------------
# 项 <-> 有理函数
# ---------------------------------------------------------------------------

def rf_from_term(ring: Ring, t, vars_: tuple) -> RatFunc | None:
    """驻留项 -> RatFunc；越出 K(x) 片段返回 None。

    负整指数幂按倒数处理（b^(-k)：分母分子互换）；0^负 未定义，
    非成员。其余头（Sin 等）非成员。
    """
    w = len(vars_)
    one = {(0,) * w: ring.from_int(1)}

    def rec(u):
        # 快路径：整个子树是多项式
        p = poly_from_term(ring, u, vars_)
        if p is not None:
            return dict(p.monos), dict(one)
        if not isinstance(u, Expr):
            return None                # 非成员叶：未知符号/非环系数
        n = u.head.name
        if n == "Plus":
            acc = None
            for a in u.args:
                pa = rec(a)
                if pa is None:
                    return None
                if acc is None:
                    acc = pa
                else:
                    an, ad = acc
                    bn, bd = pa
                    acc = (_add(ring, _mul(ring, an, bd),
                                _mul(ring, bn, ad)),
                           _mul(ring, ad, bd))
            return acc
        if n == "Times":
            acc = None
            for a in u.args:
                pa = rec(a)
                if pa is None:
                    return None
                acc = pa if acc is None else \
                    (_mul(ring, acc[0], pa[0]), _mul(ring, acc[1], pa[1]))
            return acc
        if n == "Power":
            b, e = u.args
            pb = rec(b)
            if pb is None or not isinstance(e, Int):
                return None
            bn, bd_ = pb
            k = e.v
            if k >= 0:
                return _pow(ring, bn, k), _pow(ring, bd_, k)
            if _is_zero(bn):
                return None            # 0 负幂：未定义
            return _pow(ring, bd_, -k), _pow(ring, bn, -k)
        return None

    r = rec(t)
    if r is None:
        return None
    nd, dd = r
    if _is_zero(dd):
        return None                    # 分母为零：未定义
    vt = tuple(vars_)
    return RatFunc(_norm(ring, vt, nd), _norm(ring, vt, dd))


def rf_equal(ring, a: RatFunc, b: RatFunc) -> bool:
    """ad == bc，完全判定。"""
    return p_mul(ring, a.num, b.den).monos == \
        p_mul(ring, b.num, a.den).monos


def rf_reduce(ring, rf: RatFunc) -> RatFunc:
    """单变量 GCD 约简（通用算法的快路径：单变量欧几里得已实现）。
    多变量约简待多变量 GCD 就位后同样接入。"""
    if len(rf.num.vars) != 1 or rf.den.is_zero():
        return rf
    g = p_gcd_univar(ring, rf.num, rf.den)
    if g.is_zero():
        return rf
    qn, _ = p_divmod_field(ring, rf.num, g, 0)
    qd, _ = p_divmod_field(ring, rf.den, g, 0)
    if qd.is_zero():
        return rf
    lead = max(qd.monos, key=lambda kc: kc[0][0])
    inv = ring.div_exact(ring.from_int(1), lead[1])
    return RatFunc(p_scale(ring, qn, inv), p_scale(ring, qd, inv))


def rf_deriv(ring, rf: RatFunc, var_i: int) -> RatFunc:
    """域内导数（商法则）：D(n/d) = (D(n)·d − n·D(d)) / d²。

    出口经 rf_reduce 快路径约简（单变量）。系数导子经 ring.deriv。"""
    dn = p_deriv(ring, rf.num, var_i)
    dd = p_deriv(ring, rf.den, var_i)
    num = _norm(ring, rf.num.vars,
                _add(ring, _mul(ring, dict(dn.monos), dict(rf.den.monos)),
                     {k: ring.neg(c) for k, c in
                      _mul(ring, dict(rf.num.monos), dict(dd.monos)).items()}))
    den = _norm(ring, rf.den.vars,
                _mul(ring, dict(rf.den.monos), dict(rf.den.monos)))
    return rf_reduce(ring, RatFunc(num, den))


class RatFuncDomain(Domain):
    """K(x₁..xₙ)。"""

    def __init__(self, vars_, ring: Ring, name: str | None = None):
        self.vars = tuple(vars_)
        self.ring = ring
        self.name = name or "K(" + ",".join(v.name for v in self.vars) + ")"
        # 能力（架构 3.2）：K(x) 恒为域；单变量时是欧几里得整环
        self.is_field = True
        self.is_euclidean = bool(ring.is_field and len(self.vars) == 1)

    def member(self, t) -> bool:
        return rf_from_term(self.ring, t, self.vars) is not None

    def normalize(self, t):
        rf = rf_from_term(self.ring, t, self.vars)
        if rf is None:
            return None
        rf = rf_reduce(self.ring, rf)
        nt = to_term(self.ring, rf.num)
        dt = to_term(self.ring, rf.den)
        if T.is_num(dt) and T.num_val(dt) == 1:
            return nt
        return T.mk(T.S("Times"), (nt, T.pw(dt, T.N(-1))))

    def equal(self, a, b):
        ra = rf_from_term(self.ring, a, self.vars)
        rb = rf_from_term(self.ring, b, self.vars)
        if ra is None or rb is None:
            return None                  # 非成员：调用方越界
        return rf_equal(self.ring, ra, rb)


_rfx_cache = {}


def ratfunc_domain(*vars_) -> RatFuncDomain:
    key = tuple(vars_)
    d = _rfx_cache.get(key)
    if d is None:
        from cas.domains.q import Q_RING
        d = RatFuncDomain(key, Q_RING)
        _rfx_cache[key] = d
    return d
