"""代数数最小版：RootOf 表示 + Q(a) 域运算 + 迹（幂和）。"""

from fractions import Fraction as Fr

from cas.errors import PolyError
from cas.poly import Poly
from cas import term as T
from cas.term import S, N


def uexgcd(a, b):
    """扩展欧几里得：s*a + t*b = g，g = ugcd(a, b)（monic）。"""
    if a.vars != b.vars or len(a.vars) != 1:
        raise PolyError("univariate only")
    r0, r1 = a, b
    s0, t0 = Poly.one(a.vars), Poly.zero(a.vars)
    s1, t1 = Poly.zero(a.vars), Poly.one(a.vars)
    while not r1.is_zero():
        q, r = r0.udivmod(r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    if r0.is_zero():
        return Poly.zero(a.vars), Poly.zero(a.vars), Poly.zero(a.vars)
    x = a.vars[0]
    lc = r0.lc(x)
    return s0.scalar(Fr(1) / lc), t0.scalar(Fr(1) / lc), r0.scalar(Fr(1) / lc)


def inv_mod(a, m):
    """a 的逆 mod m（a 与 m 互素），返回 mod m 余数。"""
    s, _, _ = uexgcd(a, m)
    return s.udivmod(m)[1]


class RootOf:
    """不可约 monic 多项式 m 的第 idx 个根（共轭类编号）。"""

    __slots__ = ("m", "idx")

    def __init__(self, m, idx):
        self.m = m
        self.idx = idx

    def __eq__(self, o):
        if not isinstance(o, RootOf):
            return NotImplemented
        return self.m.monos == o.m.monos and self.idx == o.idx

    def __hash__(self):
        return hash((tuple(sorted((k, v) for k, v in self.m.monos.items())), self.idx))

    def __repr__(self):
        return f"root({self.m}, {self.idx})"

    def to_term(self):
        return T.mk(S("RootOf"), (self.m.to_term(), N(self.idx)))


def qa_mod(a, m):
    return a.udivmod(m)[1]


def qa_mul(a, b, m):
    return qa_mod(a * b, m)


def qa_inv(a, m):
    return inv_mod(a, m)


def qa_div(a, b, m):
    return qa_mul(a, qa_inv(b, m), m)


def tr_power_sums(m, upto):
    """monic m 的根幂和 s_1..s_upto（牛顿恒等式）。"""
    x = m.vars[0]
    n = m.degree(x)
    if n <= 0:
        return []
    cs = [Fr(0)] * (n + 1)
    for k, v in m.monos.items():
        cs[n - k[0]] = v
    s = []
    for k in range(1, upto + 1):
        if k <= n:
            acc = Fr(0)
            for j in range(1, k):
                acc += cs[j] * s[k - j - 1]
            s.append(-acc - k * cs[k])
        else:
            acc = Fr(0)
            for j in range(1, n + 1):
                acc += cs[j] * s[k - j - 1]
            s.append(-acc)
    return s


def tr_eval(m, c, t=0):
    """迹：把 Q(a) 元素 c（a = m 的根）映射到 Q：Tr(c·β^t) = Σ_j c(β_j)·β_j^t。

    t=0 即普通迹 Tr(c)；t>0 给出幂偏移迹（积分验证用）。
    """
    x = m.vars[0]
    deg = m.degree(x)
    if deg <= 0:
        return c.const_val()
    rmax = max((k[0] for k in c.monos), default=0) + t
    s = tr_power_sums(m, rmax)
    total = Fr(0)
    for k, v in c.monos.items():
        u = k[0] + t
        if u == 0:
            total += v * deg
        else:
            total += v * s[u - 1]
    return total


def coefs(p, x):
    """降幂系数列表 [lc, ..., const]（含零位）。"""
    n = p.degree(x)
    if n < 0:
        return [Fr(0)]
    out = [Fr(0)] * (n + 1)
    for k, v in p.monos.items():
        out[n - k[0]] = v
    return out