"""Three-valued decisions with explicit evidence.

`Yes` means the current frame entails the proposition. `No` means the frame
entails its negation and must carry witnesses — "I could not prove it" is not a
refutation. `Unknown` means neither direction was established and names one of
four reasons.

A verdict never converts to `bool`: callers must handle all three cases.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.syntax import term as T


class Reason(StrEnum):
    """Why a decision remains undecided."""

    FRAGMENT = "fragment"
    GUARDED = "guarded"
    UNDECIDABLE = "undecidable"
    BUDGET = "budget"


class Verdict:
    """Closed three-valued hierarchy."""

    __slots__ = ()

    def __bool__(self) -> bool:
        raise TypeError("handle Yes, No and Unknown explicitly")

    def is_yes(self) -> bool:
        return isinstance(self, Yes)

    def is_no(self) -> bool:
        return isinstance(self, No)

    def is_unknown(self) -> bool:
        return isinstance(self, Unknown)


@dataclass(frozen=True, slots=True)
class Yes(Verdict):
    """The proposition is entailed."""


@dataclass(frozen=True, slots=True)
class No(Verdict):
    """The negation is entailed; witnesses are the inspected terms."""

    witnesses: tuple[T.Term, ...]
    detail: str

    def __post_init__(self) -> None:
        if not self.witnesses:
            raise ValueError("a refutation needs at least one witness")
        if not self.detail:
            raise ValueError("a refutation needs an explanation")


@dataclass(frozen=True, slots=True)
class Unknown(Verdict):
    """Neither direction was established."""

    reason: Reason
    detail: str = ""


YES = Yes()


__all__ = ["No", "Reason", "Unknown", "Verdict", "YES", "Yes"]
