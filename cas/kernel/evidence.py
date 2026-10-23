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

from cas.foundation.ids import FrameId
from cas.kernel.model import ObligationReason
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


@dataclass(frozen=True, slots=True)
class ObligationReport:
    """A condition the checker declares; the reason is explanation only."""

    proposition: Proposition
    reason: ObligationReason


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


@dataclass(frozen=True, slots=True)
class Refuted(CheckOutcome):
    """The requested specification is false, with witnesses."""

    proposition: Proposition
    witnesses: tuple[T.Term, ...]
    detail: str

    def __post_init__(self) -> None:
        if not self.witnesses:
            raise ValueError("a refutation needs at least one witness")
        if not self.detail:
            raise ValueError("a refutation needs an explanation")


@dataclass(frozen=True, slots=True)
class Unverified(CheckOutcome):
    """The checker could not decide; this is not a refutation."""

    reason: Reason
    detail: str = ""


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


class CheckerRegistry:
    """A frozen checker table built during assembly."""

    __slots__ = ("_checkers",)

    def __init__(self, checkers: Mapping[str, Checker]) -> None:
        table = dict(checkers)
        for key, checker in table.items():
            if checker.id != key:
                raise ValueError(
                    f"checker registered as {key!r} reports id {checker.id!r}"
                )
            if not checker.version:
                raise ValueError(f"checker {key!r} has no version")
        self._checkers = MappingProxyType(table)

    def get(self, checker_id: str) -> Checker | None:
        return self._checkers.get(checker_id)

    def __len__(self) -> int:
        return len(self._checkers)


__all__ = [
    "CheckOutcome",
    "CheckRequest",
    "Checker",
    "CheckerRegistry",
    "InvalidEvidence",
    "ObligationReport",
    "Refuted",
    "Unverified",
    "Verified",
]
