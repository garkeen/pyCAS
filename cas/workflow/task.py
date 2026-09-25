"""Task and candidate storage for the workflow computation graph."""

from __future__ import annotations

from dataclasses import dataclass

from cas.kernel.ids import JudgmentId, ScopeId
from cas.kernel.store import KernelStore
from cas.syntax.term import Term
from cas.workflow.ids import ArtifactId, TaskCandidateId, TaskId
from cas.workflow.states import CandidateState


@dataclass(frozen=True, slots=True)
class Task:
    id: TaskId
    scope: ScopeId
    request: Term
    parent: TaskId | None = None


@dataclass(frozen=True, slots=True)
class TaskCandidate:
    id: TaskCandidateId
    task: TaskId
    artifact: ArtifactId
    validation: JudgmentId | None = None

    def is_validated(self) -> bool:
        return self.validation is not None

    def state(self, store: TaskStore, scope: ScopeId) -> CandidateState:
        """Derive the candidate state from stored validation data."""
        if self.validation is None:
            return CandidateState.UNVERIFIED
        if not store.is_applicable(self.validation, scope):
            return CandidateState.CONDITIONAL
        return CandidateState.VALIDATED


class TaskStore:
    """Append-only task and candidate storage."""

    def __init__(self, kernel: KernelStore) -> None:
        self.kernel = kernel
        self._tasks: dict[TaskId, Task] = {}
        self._candidates: dict[TaskCandidateId, TaskCandidate] = {}
        self._next_task = 0
        self._next_candidate = 0

    def open_task(
        self,
        scope: ScopeId,
        request: Term,
        parent: TaskId | None = None,
    ) -> Task:
        if parent is not None and parent not in self._tasks:
            raise KeyError(f"parent task does not exist: {parent}")
        task_id = TaskId(self._next_task)
        self._next_task += 1
        task = Task(id=task_id, scope=scope, request=request, parent=parent)
        self._tasks[task_id] = task
        return task

    def get_task(self, task_id: TaskId) -> Task:
        return self._tasks[task_id]

    def task_tree_edges(self) -> tuple[tuple[TaskId, TaskId], ...]:
        return tuple(
            (task.parent, task.id)
            for task in self._tasks.values()
            if task.parent is not None
        )

    def propose(
        self,
        task: TaskId,
        artifact: ArtifactId,
        validation: JudgmentId | None = None,
    ) -> TaskCandidate:
        candidate_id = TaskCandidateId(self._next_candidate)
        self._next_candidate += 1
        candidate = TaskCandidate(
            id=candidate_id,
            task=task,
            artifact=artifact,
            validation=validation,
        )
        self._candidates[candidate_id] = candidate
        return candidate

    def get_candidate(self, candidate_id: TaskCandidateId) -> TaskCandidate:
        return self._candidates[candidate_id]

    def candidates_of(self, task: TaskId) -> tuple[TaskCandidate, ...]:
        return tuple(
            candidate
            for candidate in self._candidates.values()
            if candidate.task == task
        )

    def is_applicable(self, judgment_id: JudgmentId, scope: ScopeId) -> bool:
        """Return whether a stored judgment is usable in a query scope."""
        judgment = self.kernel.get_judgment(judgment_id)
        return (
            self.kernel.scopes.is_visible(judgment.scope, scope)
            and self.kernel.applicability(judgment_id, scope).is_applicable()
        )

    def __len__(self) -> int:
        return self._next_task
