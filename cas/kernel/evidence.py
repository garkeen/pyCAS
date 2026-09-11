"""Evidence and the checker registry.

Two rules:

· A certificate must match an exact proposition. There is no fuzzy
  `sound=True` / `complete=False` flag: "the candidate is correct" and "the
  result is complete" are two different propositions with two different
  checkers.
· A guard cannot be declared by the algorithm alone. A checker must re-check
  the conclusion and return the direct conditions under which it holds
  (`Accepted.direct_requirements`).

A checker does not import the search algorithm it verifies: the registry only
looks up by id, and independence is the registrant's responsibility.
"""

from dataclasses import dataclass, field
from typing import Protocol

from cas.kernel.model import ContextReadSet
from cas.kernel.verdict import Reason


@dataclass(frozen=True, slots=True)
class Evidence:
    """Evidence: a checker id plus a payload that checker understands.

    The payload is private to the checker (a rule instance, an antiderivative
    candidate, a back-substitution certificate, ...); the kernel only carries
    it.
    """
    checker_id: str
    payload: object = None


class CheckResult:
    """Closed hierarchy returned by a checker. Consumers must exhaust all three
    branches."""
    __slots__ = ()

    def is_accepted(self):
        return self.__class__ is Accepted

    def is_rejected(self):
        return self.__class__ is Rejected

    def is_unknown(self):
        return self.__class__ is UnknownResult


@dataclass(frozen=True, slots=True)
class Accepted(CheckResult):
    """Accepted, reporting the direct conditions and the read dependencies.

    `direct_requirements` are the propositions the checker established as
    necessary for the conclusion, not guards the algorithm claimed for itself.
    The kernel turns them into Requirements.
    """
    direct_requirements: tuple = ()
    reads: ContextReadSet = field(default_factory=ContextReadSet)


@dataclass(frozen=True, slots=True)
class Rejected(CheckResult):
    """Refuted: the conclusion does not hold. `reason` comes from verdict.Reason."""
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


@dataclass(frozen=True, slots=True)
class UnknownResult(CheckResult):
    """Undecided: the checker can neither assert nor refute (outside the
    fragment, budget exhausted, ...).

    An undecided candidate cannot enter trusted reasoning; GuardPolicy decides
    how to handle it.
    """
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


class Checker(Protocol):
    """The checker protocol."""

    def check(self, proposal, context, services) -> CheckResult:
        ...


class CheckerRegistry:
    """Checker registry. A Step has no subclasses, so dispatch goes through
    this table instead."""

    def __init__(self):
        self._checkers: dict[str, object] = {}

    def register(self, checker_id: str, checker) -> None:
        if checker_id in self._checkers:
            raise ValueError(f"checker already registered: {checker_id}")
        self._checkers[checker_id] = checker

    def get(self, checker_id: str):
        return self._checkers.get(checker_id)

    def ids(self):
        return tuple(self._checkers)

    def __contains__(self, checker_id):
        return checker_id in self._checkers
