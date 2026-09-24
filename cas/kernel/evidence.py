"""Typed evidence values and the checker registry."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Protocol, TypeAlias

from cas.kernel.model import ContextReadSet
from cas.kernel.verdict import Reason, Refutation
from cas.syntax.term import Term

if TYPE_CHECKING:
    from cas.kernel.commit import ResolvedProposal
    from cas.kernel.context import TrackedContext
    from cas.kernel.services import KernelServices

EvidencePayload: TypeAlias = object


@dataclass(frozen=True, slots=True)
class Evidence:
    """Checker identity plus an opaque payload decoded only by that checker."""

    checker_id: str
    payload: EvidencePayload = None


class CheckResult:
    """Closed checker-result hierarchy."""

    __slots__ = ()

    def is_accepted(self) -> bool:
        return isinstance(self, Accepted)

    def is_rejected(self) -> bool:
        return isinstance(self, (Rejected, RefutationRejected))

    def is_refutation_rejected(self) -> bool:
        return isinstance(self, RefutationRejected)

    def is_unknown(self) -> bool:
        return isinstance(self, UnknownResult)


@dataclass(frozen=True, slots=True)
class Accepted(CheckResult):
    """Accepted with the conditions and context reads established by a checker."""

    direct_requirements: tuple[Term, ...] = ()
    reads: ContextReadSet = field(default_factory=ContextReadSet)


@dataclass(frozen=True, slots=True)
class Rejected(CheckResult):
    """Malformed or operationally unsupported checker input."""

    reason: Reason = Reason.FRAGMENT
    detail: str = ""


@dataclass(frozen=True, slots=True)
class RefutationRejected(CheckResult):
    """A checker has a mathematical refutation with its evidence intact."""

    refutation: Refutation

    @property
    def reason(self) -> Reason:
        """Mathematical refutations are inapplicable, hence guarded at commit."""

        return Reason.GUARDED

    @property
    def detail(self) -> str:
        """Expose the explanation without replacing the structured evidence."""

        return self.refutation.detail


@dataclass(frozen=True, slots=True)
class UnknownResult(CheckResult):
    """Neither assertion nor refutation is currently justified."""

    reason: Reason = Reason.FRAGMENT
    detail: str = ""


class Checker(Protocol):
    """Context-bound candidate verifier."""

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        ...


class CheckerRegistry:
    """ID-to-checker registry with duplicate rejection."""

    def __init__(self) -> None:
        self._checkers: dict[str, Checker] = {}

    def register(self, checker_id: str, checker: Checker) -> None:
        if checker_id in self._checkers:
            raise ValueError(f"checker already registered: {checker_id}")
        self._checkers[checker_id] = checker

    def get(self, checker_id: str) -> Checker | None:
        return self._checkers.get(checker_id)

    def ids(self) -> tuple[str, ...]:
        return tuple(self._checkers)

    def __contains__(self, checker_id: str) -> bool:
        return checker_id in self._checkers
