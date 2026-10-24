"""Workflow records: expression objects, candidates, verification and history.

An expression object is data. A candidate is a proposed answer. A verification
link records what a checker did with that candidate against an exact
specification. A revision is an immutable snapshot of what the workspace shows.

None of these carry mathematical truth; only the kernel does.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import (
    CandidateId,
    EventId,
    FrameId,
    JudgmentId,
    ObjectId,
    ObjectVersionId,
    RevisionId,
)
from cas.language.problems import ProblemSpec
from cas.language.propositions import Proposition
from cas.semantics.specialization import GenericResult
from cas.syntax import term as T


class OperationStatus(StrEnum):
    """What happened to one proposed answer."""

    VERIFIED = "verified"
    REFUTED = "refuted"
    UNSUPPORTED = "unsupported"
    INVALID = "invalid"


@dataclass(frozen=True, slots=True, eq=False)
class Expression:
    """One immutable version of an expression object."""

    id: ObjectId
    version: ObjectVersionId
    term: T.Term
    frame: FrameId
    label: str = ""


@dataclass(frozen=True, slots=True)
class Candidate:
    """A proposed answer, with no trust attached."""

    id: CandidateId
    problem: ProblemSpec
    term: T.Term
    frame: FrameId


@dataclass(frozen=True, slots=True)
class VerificationLink:
    """The result of checking one candidate against one specification."""

    candidate: CandidateId
    specification: Proposition
    judgment: JudgmentId | None
    status: OperationStatus
    detail: str = ""


@dataclass(frozen=True, slots=True)
class Event:
    """One recorded operation, by the records it produced."""

    id: EventId
    operation: str
    objects: tuple[ObjectVersionId, ...] = ()
    candidates: tuple[CandidateId, ...] = ()
    judgments: tuple[JudgmentId, ...] = ()
    note: str = ""


@dataclass(frozen=True, slots=True)
class Revision:
    """One immutable snapshot of what the workspace shows."""

    id: RevisionId
    frame: FrameId
    objects: tuple[ObjectVersionId, ...]
    links: tuple[VerificationLink, ...]
    events: tuple[EventId, ...]
    label: str


@dataclass(frozen=True, slots=True)
class DerivativeResult:
    """The outcome of one differentiation request."""

    status: OperationStatus
    candidate: Candidate | None
    verification: VerificationLink | None
    result: Expression | None
    detail: str = ""
    generic: GenericResult | None = None


class SpecializationPath(StrEnum):
    """Which computation produced a specialized candidate."""

    GENERIC_FORMULA = "generic_formula"
    RECOMPUTED = "recomputed"


@dataclass(frozen=True, slots=True)
class SpecializationResult:
    """The outcome of specializing a verified parameter family."""

    status: OperationStatus
    candidate: Candidate | None
    verification: VerificationLink | None
    result: Expression | None
    path: SpecializationPath | None
    detail: str = ""


__all__ = [
    "Candidate",
    "DerivativeResult",
    "Event",
    "Expression",
    "OperationStatus",
    "Revision",
    "SpecializationPath",
    "SpecializationResult",
    "VerificationLink",
]
