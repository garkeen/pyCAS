# -*- coding: utf-8 -*-
"""内核服务接口（v4 §6.7 `KernelServices`、§四 依赖方向）。

内核**不导入**具体数学模块（v4 §四「严格禁止：kernel → concrete math
module」）。判定与上下文查询经此接口注入，由 runtime/bootstrap 提供实现。

`NullServices` 是诚实的缺省：一切判定返回 Unknown。它让内核可在没有数学
模块时独立构造与测试，也保证「没接判定器」不会被误当成「判定为真」。
"""

from typing import Protocol

from cas.kernel.evidence import Accepted, Rejected, UnknownResult
from cas.kernel.verdict import Reason, Verdict, unknown


class KernelServices(Protocol):
    """checker / commit 可见的能力面。"""

    def decide(self, proposition, scope_id) -> Verdict:
        """在当前 scope 下判定命题。返回 Verdict，不返回裸布尔。"""
        ...


class NullServices:
    """缺省服务：不判定任何命题（Unknown / FRAGMENT）。"""

    def decide(self, proposition, scope_id) -> Verdict:
        return unknown()

    def lookup_definition(self, scope_id, symbol):
        return None

    def assumptions(self, scope_id):
        return ()


class DecideChecker:
    """把注入的判定器包成 checker——内核自带核对器，不判定任何数学，只转发。

    有了它，「条件清偿」（v4 §6.9 第 6/7 步）就能在没有具体数学模块时按同一套
    提交协议运行：判定为 Yes 才接受，且不接受任何直接条件（递归安全）。
    """

    def check(self, proposal, context, services):
        if len(proposal.conclusions) != 1:
            return Rejected(Reason.FRAGMENT, "decide checker 只处理单结论")
        v = services.decide(proposal.conclusions[0], proposal.scope)
        if v.is_yes():
            return Accepted(reads=context.read_set())
        if v.is_no():
            return Rejected(Reason.GUARDED, "判定为否")
        return UnknownResult(v.reason, "判定未决")


def register_core_checkers(store) -> None:
    """装配内核自带 checker。**显式调用**，不在 import 期改全局状态（v4 §7.1）。"""
    if "kernel.decide" not in store.checkers:
        store.checkers.register("kernel.decide", DecideChecker())
