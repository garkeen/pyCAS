"""Stable identity types.

Every identity crossing a boundary gets its own type, so a judgment id cannot be
passed where a frame id is expected. The values are issued by the store that owns
them; this module defines only the namespaces and a monotone issuer.
"""

from __future__ import annotations

from typing import NewType

SymbolId = NewType("SymbolId", int)
ParentId = NewType("ParentId", int)
WorldId = NewType("WorldId", int)
FrameId = NewType("FrameId", int)
JudgmentId = NewType("JudgmentId", int)
ObligationId = NewType("ObligationId", int)
InferenceId = NewType("InferenceId", int)
ProblemId = NewType("ProblemId", int)
CandidateId = NewType("CandidateId", int)
ObjectId = NewType("ObjectId", int)
ObjectVersionId = NewType("ObjectVersionId", int)
RevisionId = NewType("RevisionId", int)
EventId = NewType("EventId", int)
TaskId = NewType("TaskId", int)

__all__ = [
    "CandidateId",
    "EventId",
    "FrameId",
    "IdIssuer",
    "InferenceId",
    "JudgmentId",
    "ObjectId",
    "ObjectVersionId",
    "ObligationId",
    "ParentId",
    "ProblemId",
    "RevisionId",
    "SymbolId",
    "TaskId",
    "WorldId",
]


class IdIssuer:
    """A monotone issuer; one instance per owning store."""

    __slots__ = ("_next",)

    def __init__(self, start: int = 0) -> None:
        if start < 0:
            raise ValueError("an id issuer cannot start below zero")
        self._next = start

    def issue(self) -> int:
        """Return the next value in this namespace."""
        value = self._next
        self._next += 1
        return value

    @property
    def issued(self) -> int:
        """How many values this issuer has handed out."""
        return self._next
