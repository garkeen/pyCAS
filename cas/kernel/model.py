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

from cas.foundation.ids import (
    FrameId,
    InferenceId,
    JudgmentId,
    ObligationId,
    WorldId,
)
from cas.language.propositions import Proposition


class BasisKind(StrEnum):
    """What kind of trusted dependency a basis reference names."""

    STANDARD_LIBRARY = "standard_library"
    DECLARATION_FILE = "declaration_file"


@dataclass(frozen=True, slots=True)
class BasisRef:
    """An admitted trusted basis: kind, version, scope and content digest.

    A basis reference is created at assembly time from data the runtime admits
    explicitly. It is not a proof; it records which trusted dependency a checker
    used, so an inference can be audited against the world it was made in.
    """

    name: str
    kind: BasisKind
    version: str
    digest: str
    world: WorldId

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a basis reference needs a name")
        if not self.version:
            raise ValueError("a basis reference needs a version")
        if not self.digest:
            raise ValueError("a basis reference needs a content digest")


@dataclass(frozen=True, slots=True)
class CertificateSchema:
    """The certificate format a checker is admitted to interpret."""

    name: str
    version: str
    certificate_type: type

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a certificate schema needs a name")
        if not self.version:
            raise ValueError("a certificate schema needs a version")
        if not isinstance(self.certificate_type, type):
            raise TypeError("a certificate schema needs a certificate type")

    def accepts(self, certificate: object) -> bool:
        return isinstance(certificate, self.certificate_type)


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
    basis: tuple[BasisRef, ...] = ()


@dataclass(frozen=True, slots=True)
class Discharge:
    """`obligation` is proved by `by_judgment` in `frame`."""

    obligation: ObligationId
    by_judgment: JudgmentId
    frame: FrameId


class FrameConsistency:
    """Closed result of assessing whether a frame's assumptions are consistent.

    `Unassessed` is the default and does not mean consistent. A fragment claim
    must name its fragment and carry evidence; an inconsistency must carry the
    issued false judgment that closed the contradiction.
    """

    __slots__ = ()

    def is_inconsistent(self) -> bool:
        return isinstance(self, Inconsistent)


@dataclass(frozen=True, slots=True)
class Unassessed(FrameConsistency):
    """No consistency evidence has been recorded."""


@dataclass(frozen=True, slots=True)
class ConsistentForFragment(FrameConsistency):
    """Consistency is claimed for a named fragment, with explicit evidence."""

    fragment: str
    evidence: tuple[JudgmentId, ...] = ()
    basis: tuple[BasisRef, ...] = ()

    def __post_init__(self) -> None:
        if not self.fragment:
            raise ValueError("a fragment claim needs a fragment description")
        if not self.evidence and not self.basis:
            raise ValueError("a fragment claim needs evidence or a basis")


@dataclass(frozen=True, slots=True)
class Inconsistent(FrameConsistency):
    """A closed proof of false was issued in the frame or an ancestor."""

    witness: JudgmentId
    detail: str = ""


class Applicability:
    """Closed result of asking whether a judgment can be used in a frame."""

    __slots__ = ()

    def is_applicable(self) -> bool:
        return isinstance(self, Applicable)

    def is_conditional(self) -> bool:
        return isinstance(self, Conditional)

    def is_blocked(self) -> bool:
        return isinstance(self, Blocked)

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
class Blocked(Applicability):
    """A required obligation is refuted; the derivation cannot be applied.

    `Blocked` says the current use of the judgment is unavailable, not that its
    proposition is false.
    """

    refuted: tuple[ObligationId, ...]
    unresolved: tuple[ObligationId, ...] = ()
    witnesses: tuple[JudgmentId, ...] = ()

    def __post_init__(self) -> None:
        if not self.refuted:
            raise ValueError("a blocked judgment needs a refuted obligation")


@dataclass(frozen=True, slots=True)
class OutOfScope(Applicability):
    """The judgment's frame is not visible from the query frame."""

    origin: FrameId
    requested: FrameId


__all__ = [
    "Applicability",
    "Applicable",
    "BasisKind",
    "BasisRef",
    "Blocked",
    "CertificateSchema",
    "Conditional",
    "ConsistentForFragment",
    "Discharge",
    "FrameConsistency",
    "Inconsistent",
    "InferenceRecord",
    "Judgment",
    "Obligation",
    "ObligationReason",
    "OutOfScope",
    "Unassessed",
]
