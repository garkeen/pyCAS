# -*- coding: utf-8 -*-
"""证据与 checker 注册表（v4 §6.7、§6.5）。

关键纪律：

· **证书必须对应确切命题**（§6.5）。没有 `sound=True` / `complete=False` 这类
  模糊标志——「候选正确」与「结果完备」是两条不同命题、两个不同 checker。
· **守卫不能只由算法自己声明**（§6.7）。checker 必须复核并返回使结论成立所需
  的直接条件（`Accepted.direct_requirements`）。
· checker 不导入对应搜索算法（§7.3 / 不变量 14）：注册表只按 id 取用，注册方
  自己负责独立性。
"""

from dataclasses import dataclass, field
from typing import Protocol

from cas.kernel.model import ContextReadSet
from cas.kernel.verdict import Reason


@dataclass(frozen=True, slots=True)
class Evidence:
    """证据：checker id + 该 checker 认得的载荷。

    载荷是 checker 私有格式（规则实例、原函数候选、回代证书……），内核只搬运。
    """
    checker_id: str
    payload: object = None


class CheckResult:
    """checker 返回值的封闭层次（v4 §6.7）。消费方必须穷尽三分支。"""
    __slots__ = ()

    def is_accepted(self):
        return self.__class__ is Accepted

    def is_rejected(self):
        return self.__class__ is Rejected

    def is_unknown(self):
        return self.__class__ is UnknownResult


@dataclass(frozen=True, slots=True)
class Accepted(CheckResult):
    """通过，并返回**直接条件**与读依赖。

    `direct_requirements` 是 checker 复核后认定使结论成立所需的命题——不是
    算法自称的守卫。内核负责把它们变成 Requirement。
    """
    direct_requirements: tuple = ()
    reads: ContextReadSet = field(default_factory=ContextReadSet)


@dataclass(frozen=True, slots=True)
class Rejected(CheckResult):
    """否证：结论不成立。reason 取自 verdict.Reason。"""
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


@dataclass(frozen=True, slots=True)
class UnknownResult(CheckResult):
    """未决：checker 不能断言成立也不能否证（片段外、预算耗尽……）。

    未决候选不能直接参与可信推导（v4 不变量 16）——由 GuardPolicy 决定处置。
    """
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


class Checker(Protocol):
    """checker 协议（v4 §6.7）。"""

    def check(self, proposal, context, services) -> CheckResult:
        ...


class CheckerRegistry:
    """checker 注册表：Step 无子类，分派走此处（v4 §6.6 / §十一 阶段3）。"""

    def __init__(self):
        self._checkers: dict[str, object] = {}

    def register(self, checker_id: str, checker) -> None:
        if checker_id in self._checkers:
            raise ValueError(f"checker 重复注册: {checker_id}")
        self._checkers[checker_id] = checker

    def get(self, checker_id: str):
        return self._checkers.get(checker_id)

    def ids(self):
        return tuple(self._checkers)

    def __contains__(self, checker_id):
        return checker_id in self._checkers
