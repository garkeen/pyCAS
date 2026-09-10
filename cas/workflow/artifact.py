# -*- coding: utf-8 -*-
"""Artifact：中性计算产物（v4 §8.2）。

**Artifact 没有真假。** 它是「算出来的式子」，是热循环的载体（AGENTS.md §四.1）。
它与 Judgment 的分工是本架构的承重墙：

    Artifact    计算产物，免费，可任意产生，**不能作为数学前提**（不变量 4）
    Judgment    已验证结论，只能是 commit 的输出，可依赖

所以「下一步能直接吃上一步的结果」靠的是 Artifact 通道（重写吃项），不是结论通道。
"""

from dataclasses import dataclass, replace

from cas.syntax import term as T
from cas.kernel.ids import ScopeId
from cas.workflow.ids import ArtifactId, EventId


@dataclass(frozen=True, slots=True)
class Artifact:
    id: ArtifactId
    scope: ScopeId
    value: T.Term
    produced_by: EventId | None = None      # 哪个操作产出的（workflow 内引用）


class ArtifactStore:
    """追加式产物存储：只增不删（与内核账本同纪律）。"""

    def __init__(self):
        self._items: dict[ArtifactId, Artifact] = {}
        self._next = 0

    def create(self, scope, value, produced_by=None) -> Artifact:
        aid = ArtifactId(self._next)
        self._next += 1
        a = Artifact(id=aid, scope=scope, value=value, produced_by=produced_by)
        self._items[aid] = a
        return a

    def get(self, aid: ArtifactId) -> Artifact:
        return self._items[aid]

    def attach(self, aid: ArtifactId, event_id) -> Artifact:
        """回填产出事件（Event 的 id 要先知道才能记事件，故两步）。"""
        a = replace(self._items[aid], produced_by=event_id)
        self._items[aid] = a
        return a

    def all(self):
        return tuple(self._items[i] for i in range(self._next))

    def __len__(self):
        return self._next
