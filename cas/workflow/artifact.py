"""Artifact: a neutral computation product."""

from __future__ import annotations

from dataclasses import dataclass, replace

from cas.kernel.ids import ScopeId
from cas.syntax.term import Term
from cas.workflow.ids import ArtifactId, EventId


@dataclass(frozen=True, slots=True)
class Artifact:
    """A free computation result that is not a mathematical premise."""

    id: ArtifactId
    scope: ScopeId
    value: Term
    produced_by: EventId | None = None


class ArtifactStore:
    """Append-only artifact storage."""

    def __init__(self) -> None:
        self._items: dict[ArtifactId, Artifact] = {}
        self._next = 0

    def create(
        self,
        scope: ScopeId,
        value: Term,
        produced_by: EventId | None = None,
    ) -> Artifact:
        artifact_id = ArtifactId(self._next)
        self._next += 1
        artifact = Artifact(
            id=artifact_id,
            scope=scope,
            value=value,
            produced_by=produced_by,
        )
        self._items[artifact_id] = artifact
        return artifact

    def get(self, artifact_id: ArtifactId) -> Artifact:
        return self._items[artifact_id]

    def attach(self, artifact_id: ArtifactId, event_id: EventId) -> Artifact:
        artifact = replace(self._items[artifact_id], produced_by=event_id)
        self._items[artifact_id] = artifact
        return artifact

    def all(self) -> tuple[Artifact, ...]:
        return tuple(
            self._items[ArtifactId(index)] for index in range(self._next)
        )

    def __len__(self) -> int:
        return self._next
