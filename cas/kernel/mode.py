# -*- coding: utf-8 -*-
"""执行模式（AGENTS.md §四.2 / §四.3）。

三种模式的**健全性等价**，差别只在可追溯性：

    模式          读依赖记录      条件清偿        Applicability 缓存   历史保留
    interactive   关              延迟至首次查询   开                  截断 N 代
    derivation    按 Step 粒度    提交时算         开                  完整
    audit         按 read 粒度    提交时算         开                  完整

**开关只允许改变记账粒度，不得改变返回值的正确性**（§四.3）。因此：

· 条件**判定**永远进行（无论模式）——否则被否证的守卫会被静默放过，那是正确性问题；
  可以推迟的只是**清偿登记**（把已证条件记成 Discharge）。
· checker 代码路径不得读取模式标志：本模块只被 commit 的记账语句消费。

未落位的一项：`Applicability 缓存` 与 `历史截断 N 代`（历史图在阶段4 才建）——
它们不影响健全性，属可追溯性层（§四.7），届时随事件历史一起实现。
"""

from enum import Enum


class ExecutionMode(Enum):
    INTERACTIVE = "interactive"   # 默认（AGENTS.md 操作底线 6）
    DERIVATION = "derivation"
    AUDIT = "audit"

    def records_reads(self) -> bool:
        """是否把上下文读取记入 Step.reads。"""
        return self is not ExecutionMode.INTERACTIVE

    def defers_discharge(self) -> bool:
        """是否推迟清偿登记（条件照样判定，只是不记 Discharge）。"""
        return self is ExecutionMode.INTERACTIVE

    def raw_reads(self) -> bool:
        """是否保留每次读取的出现（read 粒度）而非去重（Step 粒度）。"""
        return self is ExecutionMode.AUDIT


DEFAULT_MODE = ExecutionMode.INTERACTIVE
