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
from cas.kernel.model import FrameConsistency, Unassessed
from cas.language.problems import ProblemSpec
from cas.language.propositions import Proposition
from cas.semantics.specialization import GenericResult
from cas.syntax import term as T


class OperationStatus(StrEnum):
    """What happened to one proposed answer."""

    VERIFIED = "verified"
    CONDITIONAL = "conditional"
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
    condition: Proposition | None = None


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
class OperationResult:
    """The generic outcome of one registered operation.

    `verifications` has one link per proposed specification; a candidate may be
    verified against more than one exact specification. `region` is the region
    on which the result is stated, and `trace` carries operation diagnostics
    such as whether a generic formula or a recomputation produced the result.
    """

    operation: str
    status: OperationStatus
    candidate: Candidate | None
    verifications: tuple[VerificationLink, ...]
    result: Expression | None
    detail: str = ""
    region: Proposition | None = None
    generic: GenericResult | None = None
    trace: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class AssumptionResult:
    """The outcome of introducing one hypothesis in a child frame."""

    status: OperationStatus
    frame: FrameId
    proposition: Proposition | None
    judgment: JudgmentId | None
    detail: str = ""
    consistency: FrameConsistency = Unassessed()


__all__ = [
    "AssumptionResult",
    "Candidate",
    "Event",
    "Expression",
    "OperationResult",
    "OperationStatus",
    "Revision",
    "VerificationLink",
]
