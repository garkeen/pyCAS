"""Constraint: an equation constructed by computation."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from cas.kernel.evidence import Evidence
from cas.kernel.ids import ScopeId
from cas.syntax.term import Term
from cas.workflow.ids import ArtifactId, TaskId


@dataclass(frozen=True, slots=True)
class CandidateRef:
    """A reference to one task candidate artifact."""

    task: TaskId
    artifact: ArtifactId


ConstraintSource = TaskId | CandidateRef


@dataclass(frozen=True, slots=True)
class Constraint:
    id: int
    scope: ScopeId
    relation: Term
    sources: tuple[ConstraintSource, ...] = ()
    proposed_evidence: Evidence | None = None


class ConstraintStore:
    """Append-only artifact-level constraint storage."""

    def __init__(self) -> None:
        self._items: dict[int, Constraint] = {}
        self._next = 0

    def add(
        self,
        scope: ScopeId,
        relation: Term,
        sources: Sequence[ConstraintSource] = (),
        proposed_evidence: Evidence | None = None,
    ) -> Constraint:
        constraint_id = self._next
        self._next += 1
        constraint = Constraint(
            id=constraint_id,
            scope=scope,
            relation=relation,
            sources=tuple(sources),
            proposed_evidence=proposed_evidence,
        )
        self._items[constraint_id] = constraint
        return constraint

    def get(self, constraint_id: int) -> Constraint:
        return self._items[constraint_id]

    def all(self) -> tuple[Constraint, ...]:
        return tuple(
            self._items[index] for index in range(self._next)
        )

    def involving(self, source: ConstraintSource) -> tuple[Constraint, ...]:
        return tuple(
            constraint
            for constraint in self.all()
            if source in constraint.sources
        )

    def dependency_edges(self) -> tuple[tuple[ConstraintSource, int], ...]:
        return tuple(
            (source, constraint.id)
            for constraint in self.all()
            for source in constraint.sources
        )

    def __len__(self) -> int:
        return self._next
