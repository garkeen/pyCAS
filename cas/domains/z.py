# -*- coding: utf-8 -*-
"""ℤ：有序欧几里得整环（不是域）。

入格两个理由（架构 3.1）：
· 因式分解必经之路——Zassenhaus 提升到 ℤ[x]（content、本原部分）
· 可判定丢番图碎片的宿主——线性丢番图（扩展欧几里得）、
  单变量整数根（有理根定理）。一般多元丢番图按希尔伯特第十
  问题归 UNDECIDABLE，那是定理，不是 TODO。

带余除法取欧几里得约定：余数与除数同号非负侧（|r| < |b| 且
b>0 时 r ≥ 0），保证 gcd 链单调下降。
"""

from fractions import Fraction as Fr

from cas.qarith import fold, eval_exact, EvalNumError
from cas.domains.base import Domain, Ring, RingError


class ZZRing(Ring):
    """整数环：原生 int 运算，零包装。"""

    is_euclidean = True

    def from_int(self, n):
        return int(n)

    def from_frac(self, f):
        if f.denominator != 1:
            raise RingError(f"ℤ 不含有理数 {f}")
        return f.numerator

    def add(self, a, b):
        return a + b

    def neg(self, a):
        return -a

    def mul(self, a, b):
        return a * b

    def equal(self, a, b):
        return a == b

    def divmod_(self, a, b):
        if b == 0:
            raise ZeroDivisionError("division by zero")
        q, r = divmod(a, b)
        if b < 0 and r > 0:              # 余数与除数同号
            q += 1
            r -= b
        return q, r

    def xgcd(self, a, b):
        """扩展欧几里得：返回 (g, s, t) 使 s*a + t*b = g = gcd(a, b)。"""
        old_r, r = a, b
        old_s, s = 1, 0
        old_t, t = 0, 1
        while r != 0:
            q, rem = self.divmod_(old_r, r)
            old_r, r = r, rem
            old_s, s = s, old_s - q * s
            old_t, t = t, old_t - q * t
        if old_r < 0:
            return -old_r, -old_s, -old_t
        return old_r, old_s, old_t


Z_RING = ZZRing()


class ZDomain(Domain):
    """整数环 ℤ（作为域阶梯的第一格：求解语义是整除，不是除法）。"""

    name = "Z"
    is_ordered = True
    is_euclidean = True

    def member(self, t) -> bool:
        try:
            v = eval_exact(t, {})
        except (EvalNumError, ZeroDivisionError):
            return False
        return isinstance(v, Fr) and v.denominator == 1

    def normalize(self, t):
        if not self.member(t):
            return None
        return fold(t)

    def equal(self, a, b):
        if not (self.member(a) and self.member(b)):
            return None
        return eval_exact(a, {}) == eval_exact(b, {})


# 单例。注册不是本模块的事：域包只声明，装配（含注册进阶梯）归
# 投影层 cas/project——见 cas/domains/__init__.py 的分工说明。
Z_DOMAIN = ZDomain()
