# -*- coding: utf-8 -*-
"""Task / TaskCandidate：计算问题与候选（v4 §8.3、§8.4）。

请求是**普通项**（`Simplify(expr)`、`Differentiate(expr,x)`、`Integrate(expr,x)`、
`Solve(equation,x)`…），**没有封闭的 TaskKind 枚举**——内核与工作流都不认识这些
head，它们只是被搬运的项。

状态**由数据推导**，不需要可变的 `verified=True`（§8.4）：

    validation is None                  未验证候选
    validation 有开放 requirement        已验证的条件候选
    validation 可直接应用                已验证候选

`parent` 是单父指针 —— **任务树无环**。循环积分那种环不在树上：它在
「候选 ↔ 约束」子图里（v4 §8.5，需 §8.6 Constraint，本阶段未建）。
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.kernel.ids import JudgmentId, ScopeId
from cas.workflow.ids import ArtifactId, TaskCandidateId, TaskId


@dataclass(frozen=True, slots=True)
class Task:
    id: TaskId
    scope: ScopeId
    request: T.Term
    parent: TaskId | None = None


@dataclass(frozen=True, slots=True)
class TaskCandidate:
    id: TaskCandidateId
    task: TaskId
    artifact: ArtifactId
    validation: JudgmentId | None = None

    def is_validated(self) -> bool:
        return self.validation is not None

    def state(self, store=None) -> str:
        """状态由数据推导；给了 store 才能区分「已验证」与「有条件」."""
        if self.validation is None:
            return "unverified"
        if store is not None and not store.is_applicable(self.validation):
            return "conditional"
        return "validated"


class TaskStore:
    """任务与候选存储（追加式）。"""

    def __init__(self, kernel=None):
        self.kernel = kernel                        # KernelStore，用于查适用性
        self._tasks: dict[TaskId, Task] = {}
        self._cands: dict[TaskCandidateId, TaskCandidate] = {}
        self._next_t = 0
        self._next_c = 0

    # --- 任务 ---

    def open_task(self, scope, request, parent=None) -> Task:
        if parent is not None and parent not in self._tasks:
            raise KeyError(f"父任务不存在: {parent}")
        tid = TaskId(self._next_t)
        self._next_t += 1
        t = Task(id=tid, scope=scope, request=request, parent=parent)
        self._tasks[tid] = t
        return t

    def get_task(self, tid: TaskId) -> Task:
        return self._tasks[tid]

    def subtasks(self, tid: TaskId):
        return tuple(t for t in self._tasks.values() if t.parent == tid)

    def task_tree_edges(self):
        """树边（parent → child）。任务树按构造即无环：新任务只能挂在已存在
        的父任务下（id 递增），不存在回指。"""
        return tuple((t.parent, t.id) for t in self._tasks.values()
                     if t.parent is not None)

    # --- 候选 ---

    def propose(self, task: TaskId, artifact: ArtifactId,
                validation: JudgmentId | None = None) -> TaskCandidate:
        cid = TaskCandidateId(self._next_c)
        self._next_c += 1
        c = TaskCandidate(id=cid, task=task, artifact=artifact,
                          validation=validation)
        self._cands[cid] = c
        return c

    def get_candidate(self, cid: TaskCandidateId) -> TaskCandidate:
        return self._cands[cid]

    def candidates_of(self, task: TaskId):
        return tuple(c for c in self._cands.values() if c.task == task)

    def is_applicable(self, jid: JudgmentId) -> bool:
        if self.kernel is None:
            return True
        scope = self.kernel.get_judgment(jid).scope
        return self.kernel.applicability(jid, scope).is_applicable()

    def __len__(self):
        return self._next_t
