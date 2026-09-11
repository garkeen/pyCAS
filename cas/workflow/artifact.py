"""Artifact: a neutral computation product.

An Artifact has no truth value. It is an expression that was computed, and it
is the carrier of the hot loop. Its separation from Judgment is load-bearing:

    Artifact   a computation product, free, produced at will, and it can never
               be a mathematical premise
    Judgment   a verified conclusion, only ever produced by commit, dependable

So "the next step can consume the previous result directly" goes through the
Artifact channel (a rewrite consumes a term), not the conclusion channel.
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
    produced_by: EventId | None = None      # which operation produced it


class ArtifactStore:
    """Append-only artifact store: only grows, never deletes."""

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
        """Back-fill the producing event; the event id must be known before the
        event can be recorded, hence two steps."""
        a = replace(self._items[aid], produced_by=event_id)
        self._items[aid] = a
        return a

    def all(self):
        return tuple(self._items[i] for i in range(self._next))

    def __len__(self):
        return self._next
