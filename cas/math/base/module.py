# -*- coding: utf-8 -*-
"""基础模块的装配（v4 §7.2）。

目前只有一项：`ledger_decide` —— 恒等判定的最后一个阶段，把「差值判零」交给
判定管线。原先它在 `cas/math/decide.py` 里由 **import 期自注册**
（`register_eq_stage(...)`），是 AGENTS.md §六 列的三处 import 期全局状态之一；
现在改为 `install(builder)`，只在 `bootstrap()` 时登记。

阶段是**扩展点**：域标准形/投影判零先答，答不了才落到这里；将来超越塔的规范形
归零按同一协议作为新阶段挂入，不需要改判定器。
"""

from cas.syntax import term as T
from cas.syntax.term import S


def _ledger_decide(r, a, b, assumptions):
    """把 `Eq(r, 0)` 交给判定管线；未决则返回 None（让后续阶段接手）。"""
    from cas.math.decide import decide
    d = decide(T.mk(S("Eq"), (r, T.ZERO)), assumptions)
    return None if d.is_unknown() else d


def install(builder) -> None:
    builder.register_eq_stage("ledger_decide", _ledger_decide)
