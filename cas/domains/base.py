"""数域系统基座：三值判定、系数环协议、域协议。

层位纪律：本包只依赖 cas.term，被 decide/simplify 上层消费，
永不反向导入——域是地基，判定管线在域之上。

设计裁定（docs/cas_v3_arch.md 三）：
· 每个域自带 normalize（标准形）/ equal（完全判定判等）/ member（成员测试）；
· 域由显式声明进入，不做叶嗅探（v2 病根）；
· 三值判定 YES/NO/UNKNOWN 是域判等协议的一部分，UNKNOWN 在域片段外
  出现即调用方越界。
"""

from abc import ABC, abstractmethod
from enum import Enum
from fractions import Fraction as Fr

from cas.term import Expr, Int, Rat, Sym


class T3(Enum):
    YES = "YES"
    NO = "NO"
    UNKNOWN = "UNKNOWN"


class Ring(ABC):
    """系数环协议：多项式域对系数结构的全部要求。

    系数值本身是不透明对象；环负责其算术与判等。ℚ 环直接用
    Fraction 原生运算实现（零包装开销）。"""

    @abstractmethod
    def from_int(self, n: int):
        """整数嵌入。"""

    @abstractmethod
    def from_frac(self, f: Fr):
        """有理数嵌入（要求环含 ℚ；不含时抛 RingError）。"""

    @abstractmethod
    def add(self, a, b): ...

    @abstractmethod
    def neg(self, a): ...

    @abstractmethod
    def mul(self, a, b): ...

    @abstractmethod
    def equal(self, a, b) -> bool: ...

    def is_zero(self, a) -> bool:
        return self.equal(a, self.from_int(0))

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def pow_pos(self, a, n: int):
        """a ** n，n ≥ 0，快速幂。"""
        r = self.from_int(1)
        while n:
            if n & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            n >>= 1
        return r


class RingError(Exception):
    pass


class FracRing(Ring):
    """含 ℚ 的域系数环的公共部分：精确除法、零一常量、相等。"""

    def div_exact(self, a, b):
        """域中非零元的精确除法。"""
        if self.is_zero(b):
            raise ZeroDivisionError("division by zero")
        return a / b

    def equal(self, a, b) -> bool:
        return a == b


class Domain(ABC):
    """数域协议：规范化 / 判等 / 成员测试的三位一体。

    · normalize(t) -> Term | None：非成员返回 None；成员返回标准形
      （驻留项，内容寻址保证同形同指针）。
    · equal(a, b) -> T3：仅对成员有定义；片段内完全判定，绝不 UNKNOWN。
    """

    name: str = "?"

    @abstractmethod
    def normalize(self, t): ...

    @abstractmethod
    def equal(self, a, b) -> T3: ...


_DOMAINS = {}


def register(d: Domain) -> Domain:
    _DOMAINS[d.name] = d
    return d


def by_name(name: str) -> Domain:
    return _DOMAINS[name]


def all_domains():
    return dict(_DOMAINS)


# ---------------------------------------------------------------------------
# 公共遍历助手
# ---------------------------------------------------------------------------

def is_arith_leaf(t) -> bool:
    return isinstance(t, (Sym, Int, Rat))


def walk_heads(t):
    """产出表达式中出现的全部头名（含嵌套 Bound 体）。"""
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, Expr):
            yield u.head.name
            stack.extend(u.args)
