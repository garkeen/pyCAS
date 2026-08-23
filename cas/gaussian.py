"""Gaussian rational 常数域 ℚ(i)（M5.2.5：第一个代数常数扩张）。

元素 a + b·i，a,b ∈ ℚ，i² = −1。完整域算术（精确），供塔系数 /
RDE 链在复指数化三角积分（M5.3）中使用。

约定：
- Fr 可无痕嵌入（b=0）；Ga 与 Fr/int 混合运算自动提升。
- to_term() 输出符号 i（T.S("i")）；最终答案的实化（atan 形式回转）
  是 M5.3 的出口职责，本模块只负责域内精确性。
- 零等价精确可判定（re/im 分量比较）——非 Richardson 障碍域。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N


class Ga:
    """a + b·i（高斯有理数；分量泛型——ℚ(i,params) 混合轨道时分量
    为 SymRat，M5.6#1）。"""

    __slots__ = ("re", "im")

    def __init__(self, re, im=0):
        self.re = self._comp(re)
        self.im = self._comp(im)

    @staticmethod
    def _comp(v):
        """分量域元素化：int/Fr -> Fr；SymRat 等已是一阶域元素原样。"""
        return Fr(v) if isinstance(v, (int, Fr)) else v

    # -- 构造 --------------------------------------------------------------
    @classmethod
    def zero(cls):
        return cls(0)

    @classmethod
    def one(cls):
        return cls(1)

    @classmethod
    def imag(cls):
        return cls(0, 1)

    @classmethod
    def promote(cls, x):
        """Fr/int → Ga；Ga 原样返回。"""
        if isinstance(x, Ga):
            return x
        return cls(x)

    # -- 一元 --------------------------------------------------------------
    def __neg__(self):
        return Ga(-self.re, -self.im)

    def conjugate(self):
        return Ga(self.re, -self.im)

    def norm(self):
        """|z|² = re² + im² ∈ ℚ。"""
        return self.re * self.re + self.im * self.im

    def is_zero(self):
        return self.re == 0 and self.im == 0

    def is_real(self):
        return self.im == 0

    # -- 算术 --------------------------------------------------------------
    def __add__(self, o):
        o = Ga.promote(o)
        return Ga(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = Ga.promote(o)
        return Ga(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return Ga.promote(o) - self

    def __mul__(self, o):
        o = Ga.promote(o)
        return Ga(self.re * o.re - self.im * o.im,
                  self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = Ga.promote(o)
        n = o.norm()
        if n == 0:
            from cas.errors import PolyError
            raise PolyError("division by zero")
        d = self.re * o.re + self.im * o.im
        e = self.im * o.re - self.re * o.im
        return Ga(d / n, e / n)

    def __rtruediv__(self, o):
        return Ga.promote(o) / self

    def __pow__(self, n):
        if not isinstance(n, int):
            raise TypeError("Ga power requires int exponent")
        if n < 0:
            return Ga.one() / (self ** (-n))
        r = Ga.one()
        b = self
        while n:
            if n & 1:
                r = r * b
            b = b * b
            n >>= 1
        return r

    # -- 比较 --------------------------------------------------------------
    def __eq__(self, o):
        o = Ga.promote(o)
        return self.re == o.re and self.im == o.im

    def __hash__(self):
        return hash((self.re, self.im))

    # -- 出口 --------------------------------------------------------------
    def to_term(self):
        """a + b·i 的 term 形态（规范：去零项、系数归一；SymRat 分量
        经其自身 to_term 出口——ℚ(i,params) 混合轨道）。"""
        from cas.poly import SymRat

        def _ct(v):
            if isinstance(v, SymRat):
                return v.to_term()
            return N(v)

        parts = []
        if self.re != 0:
            parts.append(_ct(self.re))
        if self.im != 0:
            ic = T.times(_ct(self.im), T.S("i")) if self.im != 1 \
                else T.S("i")
            parts.append(ic)
        if not parts:
            return N(0)
        if len(parts) == 1:
            return parts[0]
        return T.mk(S("Plus"), tuple(parts))

    @classmethod
    def from_term_val(cls, t):
        """仅含数字与符号 i 的 term 精确求值为 Ga。"""
        import cas.term as _T

        if _T.is_num(t):
            return cls(_T.num_val(t))
        if isinstance(t, _T.Const) and getattr(t, "name", "") == "i":
            return cls(0, 1)
        if isinstance(t, _T.Sym):
            if t.name == "i":
                return cls(0, 1)
            raise ValueError("non-gaussian symbol")
        if isinstance(t, _T.Expr):
            n = t.head.name
            if n == "Plus":
                acc = cls(0)
                for a in t.args:
                    acc = acc + cls.from_term_val(a)
                return acc
            if n == "Times":
                acc = cls(1)
                for a in t.args:
                    acc = acc * cls.from_term_val(a)
                return acc
            if n == "Power" and isinstance(t.args[1], _T.Int):
                return cls.from_term_val(t.args[0]) ** t.args[1].v
        raise ValueError("not a gaussian-valued term")

    def __str__(self):
        if self.im == 0:
            return str(self.re)
        if self.re == 0:
            return f"{self.im}*i" if self.im != 1 else "i"
        im_s = f"{self.im}*i" if self.im != 1 else "i"
        op = "+" if self.im > 0 else "-"
        return f"{self.re} {op} {im_s.lstrip('+-')}"

    __repr__ = __str__
