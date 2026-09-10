# -*- coding: utf-8 -*-
"""数域系统基座：域协议、系数环协议。

层位纪律：本包只依赖 cas.syntax.term，被 decide/simplify 上层消费，
永不反向导入——域是地基，判定管线在域之上。

设计裁定（cas_v3_arch.md 三）：
· 每个域自带 normalize（标准形）/ equal（完全判定判等）/ member（成员测试）；
· 域由显式声明进入，不做叶嗅探（v2 病根）；
· equal 仅对成员有定义，片段内完全判定——返回值是 bool，
  非成员返回 None 表示调用方越界，域内绝不产生"不知道"。
  （判定的三值性属于判定层 cas/verdict，域层不携带。）
· 导子 D 属于域协议：系数环的导子默认为零（常数域），
  扩张生长时覆写——代数扩张 D(α) = −D(m)(α)/m'(α)，
  超越扩张由生成元定义方程指定。
"""

from abc import ABC, abstractmethod
from fractions import Fraction as Fr


class Ring(ABC):
    """系数环协议：多项式域对系数结构的全部要求。

    系数值本身是不透明对象；环负责其算术与判等。ℚ 环直接用
    Fraction 原生运算实现（零包装开销）。

    能力字段（架构 3.2）：上层算法按能力分派，不按类型特判。
    · is_field：非零元可除（精确除法可用）
    · is_euclidean：带余除法可用（divmod/gcd 有实现）
    """

    is_field = False
    is_euclidean = False

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

    def divmod_(self, a, b):
        """带余除法 (q, r)。欧几里得环覆写；否则拒答。"""
        raise RingError(f"{type(self).__name__} 非欧几里得环")

    def deriv(self, c):
        """系数导子：常数域上恒为零。扩张环覆写（架构三：导子属于域协议）。"""
        return self.from_int(0)

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

    is_field = True

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
    · equal(a, b) -> bool | None：仅对成员有定义；片段内完全判定。
      非成员返回 None（调用方越界），不产生三值。

    能力字段：is_field（乘法非零元可逆）、is_ordered（有序，序判定可用）、
    is_euclidean（带余除法）。算法按能力分派。

    scoped：True 表示本域是单次计算域（代数扩张 ℚ(α)、根式参数），
    禁止 register() 常驻注册，必须经 domain_scope() 限定在单次计算的
    作用域内（架构 3.4 注册纪律）。
    """

    name: str = "?"
    is_field = False
    is_ordered = False
    is_euclidean = False
    scoped = False

    @abstractmethod
    def normalize(self, t): ...

    @abstractmethod
    def equal(self, a, b): ...


_DOMAINS = {}
_SCOPES = []


def register(d: Domain) -> Domain:
    """常驻注册：仅限系统基域（ℤ/ℚ/ℚ(i)/K[x]/K(x) 等）。

    scoped=True 的单次计算域（代数扩张/根式参数）必须经 domain_scope()
    注册——常驻注册会让它泄漏进后续一切计算（架构 3.4 注册纪律）。
    """
    if getattr(d, "scoped", False):
        raise ValueError(
            f"scoped 域必须经 domain_scope() 注册: {d.name}")
    if d.name in _DOMAINS and _DOMAINS[d.name] is not d:
        raise ValueError(f"domain redeclared: {d.name}")
    _DOMAINS[d.name] = d
    return d


class domain_scope:
    """单次计算作用域的临时域注册（架构 3.4 注册纪律的落地机制）。

    代数域（ℚ(α)）与根式参数只允许生存在本作用域内：退出（含异常
    退出）无条件注销，绝不泄漏进下一次计算——v2 全局可变注册表跨
    计算泄漏出过假 VERIFIED，本机制是那条纪律的机械保证。

    与常驻基域或外层作用域重名即拒绝：遮蔽既有域正是泄漏的前兆。

    用法：
        with domain_scope(QAlphaDomain(...)):
            ...            # 本计算内 lookup 命中临时域
        # 出作用域即注销
    """

    def __init__(self, *domains):
        self._domains = domains

    def __enter__(self):
        frame = {}
        for d in self._domains:
            if d.name in _DOMAINS or any(d.name in f for f in _SCOPES):
                raise ValueError(f"scoped 域与既有注册重名: {d.name}")
            frame[d.name] = d
        _SCOPES.append(frame)
        return self

    def __exit__(self, *exc):
        _SCOPES.pop()
        return False


def lookup(name):
    """按名查域：内层作用域优先，常驻基域兜底；查无返回 None。"""
    for frame in reversed(_SCOPES):
        hit = frame.get(name)
        if hit is not None:
            return hit
    return _DOMAINS.get(name)
