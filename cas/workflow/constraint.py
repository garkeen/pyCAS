# -*- coding: utf-8 -*-
"""Constraint：计算构造出的方程（v4 §8.6）。

Constraint 是**算法构造**，不一定是可参与数学证明的 Judgment：

    Constraint 可能只是算法构造；如果它经过 checker 并形成确切数学命题，
    才可以转成 Judgment。

**环在这里。** §8.5 说任务/子计算图可以含循环依赖——但 `Task.parent` 是单父
指针树，永远无环；真正的环长在**候选 ↔ 约束**子图上，例如循环积分（§9.6）：

    candidate(T0) = e^x sin x − candidate(T1)
    candidate(T1) = e^x cos x + candidate(T0)

两条构造约束互为对方的定义，`sources` 各指对方的候选 —— 所以 `sources` 必须能
引用**候选**（`(TaskId, ArtifactId)`），只指 Task 表达不了这个环。

环不会被藏起来：它由 §5.4 的子项抽象把候选冻成符号后在约束系统上代数求解消化，
证明依赖图仍然无环（§9.5）。
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.kernel.ids import ScopeId
from cas.kernel.evidence import Evidence


@dataclass(frozen=True, slots=True)
class CandidateRef:
    """候选引用：`(TaskId, ArtifactId)`。约束可以指候选，不只指任务。"""
    task: object
    artifact: object


@dataclass(frozen=True, slots=True)
class Constraint:
    id: int
    scope: ScopeId
    relation: T.Term
    sources: tuple = ()                      # tuple[TaskId | CandidateRef, ...]
    proposed_evidence: Evidence | None = None    # 候选凭据，**不是**已验证的证据

    def binds(self, symbol):
        """该约束是否出现此符号（用于从约束系统里取未知量）。"""
        return symbol in T.free_vars(self.relation)


class ConstraintStore:
    """约束存储（追加式）。约束是 Artifact 级构造，不进内核账本。"""

    def __init__(self):
        self._items: dict[int, Constraint] = {}
        self._next = 0

    def add(self, scope, relation, sources=(), proposed_evidence=None):
        cid = self._next
        self._next += 1
        c = Constraint(id=cid, scope=scope, relation=relation,
                       sources=tuple(sources),
                       proposed_evidence=proposed_evidence)
        self._items[cid] = c
        return c

    def get(self, cid) -> Constraint:
        return self._items[cid]

    def all(self):
        return tuple(self._items[i] for i in range(self._next))

    def involving(self, obj):
        """哪些约束引用了该候选/任务（候选图的入边）。"""
        return tuple(c for c in self.all() if obj in c.sources)

    def dependency_edges(self):
        """候选/任务之间的依赖边 `source → constraint`。

        **允许成环**：这正是 §8.5 说的「任务图可含强连通分量」。它与内核的
        证明 DAG（premises → conclusions，必须无环）是两张不同的图。
        """
        return tuple((src, c.id) for c in self.all() for src in c.sources)

    def __len__(self):
        return self._next
