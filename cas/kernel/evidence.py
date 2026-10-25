"""Checker protocol and the closed set of check outcomes.

A checker receives exactly what the kernel resolved — the submission frame, the
requested conclusions, the premise propositions — plus the certificate. It must
return the specifications it actually verified. The kernel compares them with
the request; a checker may not verify one thing while the caller claims another.

`InvalidEvidence` marks a malformed certificate, which is not a refutation.
"""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Mapping, Protocol

from cas.foundation.ids import FrameId, WorldId
from cas.kernel.model import ObligationReason
from cas.kernel.trust import BasisRef, CertificateSchema
from cas.language.decisions import Reason
from cas.language.propositions import Proposition
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class CheckRequest:
    """What a checker is asked to verify."""

    frame: FrameId
    conclusions: tuple[Proposition, ...]
    premises: tuple[Proposition, ...]
    certificate: object

    def __post_init__(self) -> None:
        for proposition in self.premises + self.conclusions:
            if not isinstance(proposition, Proposition):
                raise TypeError("a check request carries propositions")


@dataclass(frozen=True, slots=True)
class ObligationReport:
    """A condition the checker declares; the reason is explanation only."""

    proposition: Proposition
    reason: ObligationReason

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("an obligation report carries a proposition")
        if not isinstance(self.reason, ObligationReason):
            raise TypeError("an obligation report needs a reason")


class CheckOutcome:
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Verified(CheckOutcome):
    """The checker verified `checked`, which must equal the request.

    `used_premises` are indices into the request's premises that the checker
    actually used. The kernel records only those; a premise the caller supplied
    but the checker ignored does not become claimed support.
    """

    checked: tuple[Proposition, ...]
    obligations: tuple[ObligationReport, ...] = ()
    reads: tuple[tuple[str, str], ...] = ()
    used_premises: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if any(not isinstance(item, Proposition) for item in self.checked):
            raise TypeError("a verified outcome carries propositions")
        if any(
            not isinstance(item, ObligationReport)
            for item in self.obligations
        ):
            raise TypeError("a verified outcome carries obligation reports")
        if any(
            not isinstance(index, int) or isinstance(index, bool)
            for index in self.used_premises
        ):
            raise TypeError("used premise indices must be integers")


@dataclass(frozen=True, slots=True)
class Refuted(CheckOutcome):
    """The requested specification is false, with witnesses."""

    proposition: Proposition
    witnesses: tuple[T.Term, ...]
    detail: str

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("a refutation carries a proposition")
        if not self.witnesses:
            raise ValueError("a refutation needs at least one witness")
        if any(not isinstance(item, T.Term) for item in self.witnesses):
            raise TypeError("refutation witnesses must be terms")
        if not self.detail:
            raise ValueError("a refutation needs an explanation")


@dataclass(frozen=True, slots=True)
class Unverified(CheckOutcome):
    """The checker could not decide; this is not a refutation."""

    reason: Reason
    detail: str = ""

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("an unverified outcome needs a Reason")


@dataclass(frozen=True, slots=True)
class InvalidEvidence(CheckOutcome):
    """The certificate is malformed or belongs to another request."""

    detail: str


class Checker(Protocol):
    """A registered verification procedure."""

    id: str
    version: str

    def check(self, request: CheckRequest) -> CheckOutcome:
        """Re-verify the request and report exactly what was verified."""


@dataclass(frozen=True, slots=True)
class CheckerSpec:
    """Everything the kernel admits about one checker.

    The certificate schema, accepted kinds and trusted dependencies belong to
    the registration, not to a proposal. A proposal names a checker and a kind;
    it cannot supply its own trust metadata.
    """

    checker: Checker
    certificate_schema: CertificateSchema
    accepted_problem_kinds: frozenset[str]
    accepted_specification_kinds: frozenset[str]
    world: WorldId
    trusted_dependencies: tuple[BasisRef, ...] = ()

    def __post_init__(self) -> None:
        if not self.checker.id:
            raise ValueError("a checker specification needs a checker id")
        if not self.checker.version:
            raise ValueError(
                f"checker {self.checker.id!r} has no version"
            )
        for label, kinds in (
            ("problem", self.accepted_problem_kinds),
            ("specification", self.accepted_specification_kinds),
        ):
            if not isinstance(kinds, frozenset) or any(
                not isinstance(kind, str) or not kind for kind in kinds
            ):
                raise TypeError(
                    f"checker {self.checker.id!r} needs string {label} kinds"
                )
            if not kinds:
                raise ValueError(
                    f"checker {self.checker.id!r} accepts no {label} kind"
                )
        if not isinstance(self.trusted_dependencies, tuple):
            raise TypeError(
                f"checker {self.checker.id!r} trusted dependencies "
                "must be a tuple"
            )
        if any(
            not isinstance(basis, BasisRef)
            for basis in self.trusted_dependencies
        ):
            raise TypeError(
                f"checker {self.checker.id!r} has a non-basis dependency"
            )
        keys = [
            (basis.name, basis.kind, basis.version, basis.digest, basis.world)
            for basis in self.trusted_dependencies
        ]
        if len(set(keys)) != len(keys):
            raise ValueError(
                f"checker {self.checker.id!r} repeats a trusted dependency"
            )
        for basis in self.trusted_dependencies:
            if basis.world != self.world:
                raise ValueError(
                    f"checker {self.checker.id!r} trusts a basis from "
                    "another world"
                )


class CheckerRegistry:
    """A frozen checker table built during assembly."""

    __slots__ = ("_specs",)

    def __init__(self, specs: Mapping[str, CheckerSpec]) -> None:
        table = dict(specs)
        for key, spec in table.items():
            if not isinstance(spec, CheckerSpec):
                raise TypeError(
                    "a checker registry holds CheckerSpec values, "
                    f"got {type(spec).__name__}"
                )
            if spec.checker.id != key:
                raise ValueError(
                    f"checker registered as {key!r} reports id "
                    f"{spec.checker.id!r}"
                )
        self._specs = MappingProxyType(table)

    def get(self, checker_id: str) -> Checker | None:
        spec = self._specs.get(checker_id)
        return None if spec is None else spec.checker

    def spec(self, checker_id: str) -> CheckerSpec | None:
        return self._specs.get(checker_id)

    def __len__(self) -> int:
        return len(self._specs)


__all__ = [
    "CheckOutcome",
    "CheckRequest",
    "Checker",
    "CheckerRegistry",
    "CheckerSpec",
    "InvalidEvidence",
    "ObligationReport",
    "Refuted",
    "Unverified",
    "Verified",
]
