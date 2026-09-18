"""Constraint: an equation constructed by computation.

A Constraint is an algorithmic construction and not necessarily a Judgment that
can take part in a mathematical proof. It may be a mere algorithmic construct;
only after it passes a checker and becomes an exact mathematical proposition
can it become a Judgment.

The cycle lives here. The task/subcomputation graph may contain cyclic
dependencies, but `Task.parent` is a single-parent tree and is always acyclic;
the real cycle lives in the candidate <-> constraint subgraph, for example in
cyclic integration:

    candidate(T0) = e^x sin x - candidate(T1)
    candidate(T1) = e^x cos x + candidate(T0)

The two construction constraints define each other and their `sources` point at
each other's candidate, so `sources` must be able to reference a *candidate*
(`(TaskId, ArtifactId)`); referencing tasks alone cannot express the cycle.

The cycle is not hidden: subterm abstraction freezes the candidates into
symbols and algebraic elimination over the constraint system consumes it, while
the proof dependency graph stays acyclic.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.kernel.ids import ScopeId
from cas.kernel.evidence import Evidence


@dataclass(frozen=True, slots=True)
class CandidateRef:
    """A candidate reference: `(TaskId, ArtifactId)`. A constraint may point at
    a candidate, not only at a task."""
    task: object
    artifact: object


@dataclass(frozen=True, slots=True)
class Constraint:
    id: int
    scope: ScopeId
    relation: T.Term
    sources: tuple = ()                      # tuple[TaskId | CandidateRef, ...]
    proposed_evidence: Evidence | None = None    # candidate credentials, NOT verified evidence


class ConstraintStore:
    """Constraint storage (append-only). A constraint is an Artifact-level
    construction and never enters the kernel ledger."""

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
        """Which constraints reference this candidate/task (incoming edges of
        the candidate graph)."""
        return tuple(c for c in self.all() if obj in c.sources)

    def dependency_edges(self):
        """Dependency edges `source -> constraint` between candidates/tasks.

        Cycles are allowed here: this is the "task graph may contain strongly
        connected components" graph. It is a different graph from the kernel's
        proof DAG (premises -> conclusions), which must be acyclic.
        """
        return tuple((src, c.id) for c in self.all() for src in c.sources)

    def __len__(self):
        return self._next
