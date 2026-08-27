# -*- coding: utf-8 -*-
"""判定结果 ADT（docs/cas_v3_arch.md 总纲的语言契约）。

判定结果是代数数据类型，不是字符串，不是裸枚举：

· Yes 携带证据（判定出处，供证据链与回放消费）
· No  是反驳
· Unknown 携带理由，理由决定后续动作

Unknown 理由种类。架构总纲列出三种，此处补一种内部操作理由：

· FRAGMENT    片段没覆盖——表达式含未实现的结构，扩库/扩算法可解
· GUARDED     被未确认条件挡住——条件清偿后答案自动翻转
· UNDECIDABLE 根本不可判定——Richardson/Skolem 类边界，见拒答协议表
· BUDGET      搜索预算耗尽——内部资源限制，与不可判定是两种结论，
              加大预算可能翻转（未找到 ≠ 不存在）

YES/NO 是单例，支持 `is` 比较；Unknown 按理由单例化（unknown() 工厂）。
封闭变体：消费方必须穷尽 Yes/No/Unknown 三分支，禁止字符串比较。
"""

from enum import Enum


class Reason(Enum):
    FRAGMENT = "fragment"
    GUARDED = "guarded"
    UNDECIDABLE = "undecidable"
    BUDGET = "budget"


class Verdict:
    """判定三值的封闭层次。"""
    __slots__ = ()

    def is_yes(self):
        return self is YES

    def is_no(self):
        return self is NO

    def is_unknown(self):
        return isinstance(self, Unknown)


class Yes(Verdict):
    __slots__ = ("proof",)

    def __init__(self, proof=None):
        self.proof = proof

    def __repr__(self):
        return "YES" if self.proof is None else f"YES[{self.proof}]"


class No(Verdict):
    __slots__ = ()

    def __repr__(self):
        return "NO"


class Unknown(Verdict):
    __slots__ = ("reason",)

    def __init__(self, reason):
        self.reason = reason

    def __repr__(self):
        return f"UNKNOWN[{self.reason.value}]"


YES = Yes()
NO = No()
_UNKNOWN_CACHE = {}


def unknown(reason=Reason.FRAGMENT):
    u = _UNKNOWN_CACHE.get(reason)
    if u is None:
        u = Unknown(reason)
        _UNKNOWN_CACHE[reason] = u
    return u


# ---------------------------------------------------------------------------
# 命题复合（架构总纲：逻辑层只需三值命题运算）
# ---------------------------------------------------------------------------

def _first_unknown(*vs):
    for v in vs:
        if isinstance(v, Unknown):
            return v
    return unknown()


def and3(a, b):
    if a is NO or b is NO:
        return NO
    if a is YES and b is YES:
        return YES
    return _first_unknown(a, b)


def or3(a, b):
    if a is YES or b is YES:
        return YES
    if a is NO and b is NO:
        return NO
    return _first_unknown(a, b)


def not3(a):
    if a is YES:
        return NO
    if a is NO:
        return YES
    return a
