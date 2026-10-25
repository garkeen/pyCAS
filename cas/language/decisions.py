"""The closed vocabulary of reasons a decision stays undecided.

The three-valued `Verdict` family is introduced together with a `decide`
service; no such service exists yet, so only the reason vocabulary is kept. It
is consumed by checker outcomes and candidate refusals, and it is one closed
set: a reason outside these four classes is not an honest blocker.
"""

from __future__ import annotations

from enum import StrEnum


class Reason(StrEnum):
    """Why a decision remains undecided."""

    FRAGMENT = "fragment"
    GUARDED = "guarded"
    UNDECIDABLE = "undecidable"
    BUDGET = "budget"


__all__ = ["Reason"]
