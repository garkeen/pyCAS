"""Task / TaskCandidate: a computation problem and a candidate.

A request is an ordinary term (`Simplify(expr)`, `Differentiate(expr, x)`,
`Integrate(expr, x)`, `Solve(equation, x)`, ...). There is no closed TaskKind
enum: neither the kernel nor the workflow knows these heads, they are just
terms being carried.

State is derived from data, so no mutable `verified=True` is needed:

    validation is None                        unverified candidate
    validation has an open requirement        verified but conditional
    validation is directly applicable         verified candidate

`parent` is a single parent pointer, so the task tree is acyclic. The cycle in
cyclic integration is not in this tree: it lives in the candidate <-> constraint
subgraph (see constraint.py).
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

    def state(self, store, scope: ScopeId) -> str:
        """Derive the state from data: unverified, verified but conditional, or
        verified.

        `store` and `scope` are both required: without them "verified" cannot be
        distinguished from "conditional", and any silent downgrade would call an
        unverified candidate verified. Applicability is computed by the kernel
        per scope; the workflow only queries it.

        `scope` is the scope the candidate would be used in, not the scope its
        validation was produced in. The two differ as soon as branches exist: a
        validation whose conditions were discharged by a branch assumption is
        applicable inside that branch and only conditional outside it.
        """
        if self.validation is None:
            return "unverified"
        if not store.is_applicable(self.validation, scope):
            return "conditional"
        return "validated"


class TaskStore:
    """Task and candidate storage (append-only)."""

    def __init__(self, kernel):
        self.kernel = kernel                        # KernelStore; the independent facility for applicability queries
        self._tasks: dict[TaskId, Task] = {}
        self._cands: dict[TaskCandidateId, TaskCandidate] = {}
        self._next_t = 0
        self._next_c = 0

    # --- tasks ---

    def open_task(self, scope, request, parent=None) -> Task:
        if parent is not None and parent not in self._tasks:
            raise KeyError(f"parent task does not exist: {parent}")
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
        """Tree edges (parent -> child). The task tree is acyclic by
        construction: a new task can only be attached to an existing parent
        (ids increase), so there is no back-reference."""
        return tuple((t.parent, t.id) for t in self._tasks.values()
                     if t.parent is not None)

    # --- candidates ---

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

    def is_applicable(self, jid: JudgmentId, scope: ScopeId) -> bool:
        """Whether the conclusion `jid` is usable in `scope`.

        `scope` is the query scope (where the conclusion is to be used), never
        the judgment's own scope: a conclusion proved under a branch assumption
        is applicable in that branch and not in the parent.

        Two questions are answered together, because usability needs both. The
        kernel's `applicability` answers the *condition* question (are the
        judgment's requirements discharged in `scope`), which does not look at
        where the conclusion was asserted: a branch-local claim that happens to
        carry no requirement would read as applicable in the parent. The kernel
        refuses to use a judgment as a premise outside its scope (`commit`'s
        premise visibility check), so the *scope* relation must gate usability
        as well: the judgment's own scope has to be visible from the query
        scope.
        """
        j = self.kernel.get_judgment(jid)
        return (self.kernel.scopes.is_visible(j.scope, scope)
                and self.kernel.applicability(jid, scope).is_applicable())

    def __len__(self):
        return self._next_t
