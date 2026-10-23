"""Kernel records: judgments, obligations, inferences, discharge, applicability.

A `Judgment` is the trusted form of a proposition:

    frame |- proposition [obligations]

The obligations are open conditions; the judgment is not an unconditional truth
because they exist. `InferenceRecord` is the single record of how the judgment
was issued: which checker, which premises, which certificate.

Records are immutable values. Later events (a discharge, a refutation, a new
frame) never rewrite them; applicability is a relation between a judgment and a
query frame, computed on demand.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import FrameId, InferenceId, JudgmentId, ObligationId
from cas.language.propositions import Proposition


class ObligationReason(StrEnum):
    """Why a condition was introduced; explanation, not truth."""

    DEFINEDNESS = "definedness"
    RULE_GUARD = "rule_guard"
    ALGORITHM_PRECONDITION = "algorithm_precondition"
    BRANCH_COVERAGE = "branch_coverage"
    MEMBERSHIP = "membership"
    REGULARITY = "regularity"


@dataclass(frozen=True, slots=True)
class Obligation:
    """A condition a judgment depends on."""

    id: ObligationId
    frame: FrameId
    proposition: Proposition
    reason: ObligationReason
    introduced_by: InferenceId


@dataclass(frozen=True, slots=True)
class Judgment:
    """A scoped conclusion with its open obligations."""

    id: JudgmentId
    frame: FrameId
    proposition: Proposition
    obligations: tuple[ObligationId, ...]
    inference: InferenceId


@dataclass(frozen=True, slots=True)
class InferenceRecord:
    """The record of one trusted inference.

    `certificate` is opaque here: only the checker that produced it interprets
    it, and only after the checker was selected by `checker_id`/version.
    """

    id: InferenceId
    frame: FrameId
    checker_id: str
    checker_version: str
    premises: tuple[JudgmentId, ...]
    conclusions: tuple[JudgmentId, ...]
    certificate: object
    reads: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True, slots=True)
class Discharge:
    """`obligation` is proved by `by_judgment` in `frame`."""

    obligation: ObligationId
    by_judgment: JudgmentId
    frame: FrameId


class Applicability:
    """Closed result of asking whether a judgment can be used in a frame."""

    __slots__ = ()

    def is_applicable(self) -> bool:
        return isinstance(self, Applicable)

    def is_conditional(self) -> bool:
        return isinstance(self, Conditional)

    def is_out_of_scope(self) -> bool:
        return isinstance(self, OutOfScope)


@dataclass(frozen=True, slots=True)
class Applicable(Applicability):
    """Every obligation is discharged in the query frame."""


@dataclass(frozen=True, slots=True)
class Conditional(Applicability):
    """Some obligation is still open in the query frame."""

    obligations: tuple[ObligationId, ...] = ()


@dataclass(frozen=True, slots=True)
class OutOfScope(Applicability):
    """The judgment's frame is not visible from the query frame."""

    origin: FrameId
    requested: FrameId


__all__ = [
    "Applicability",
    "Applicable",
    "Conditional",
    "Discharge",
    "InferenceRecord",
    "Judgment",
    "Obligation",
    "ObligationReason",
    "OutOfScope",
]
