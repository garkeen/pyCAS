"""The closed vocabulary of reasons a decision stays undecided.

The three-valued `Verdict` family is introduced together with a `decide`
service; no such service exists yet, so only the reason vocabulary is kept. It
is consumed by checker outcomes and candidate refusals, and it is one closed
set: a reason outside these four classes is not an honest blocker.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.language.execution import ExecutionBudget
from cas.language.propositions import Proposition


class Reason(StrEnum):
    """Why a decision remains undecided."""

    FRAGMENT = "fragment"
    GUARDED = "guarded"
    UNDECIDABLE = "undecidable"
    BUDGET = "budget"


@dataclass(frozen=True, slots=True)
class Blocker:
    """A structured reason why a request did not reach a verified answer.

    `detail` is explanation, not proof.  `missing` names the capabilities the
    current implementation lacks; `conditions` are the obligations that remain
    open; `attempted` names the fragments already tried.  `target` is the exact
    proposition or subproblem the blocker is about when one is fixed, and
    `budget` is the structural budget of the execution attempt that was blocked
    when that attempt had one.  The workspace records this value instead of
    collapsing every refusal into a string.
    """

    reason: Reason
    detail: str
    missing: frozenset[str] = frozenset()
    conditions: tuple[Proposition, ...] = ()
    attempted: tuple[str, ...] = ()
    target: Proposition | None = None
    budget: ExecutionBudget | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("a blocker needs a Reason")
        if not isinstance(self.detail, str):
            raise TypeError("a blocker detail must be a string")
        if not self.detail:
            raise ValueError("a blocker needs a detail")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError("blocker capabilities must be non-empty strings")
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError("blocker conditions must be propositions")
        attempted = tuple(self.attempted)
        if any(not isinstance(item, str) or not item for item in attempted):
            raise TypeError("blocker attempts must be non-empty strings")
        if self.target is not None and not isinstance(
            self.target, Proposition
        ):
            raise TypeError("a blocker target must be a proposition or None")
        if self.budget is not None and not isinstance(
            self.budget, ExecutionBudget
        ):
            raise TypeError(
                "a blocker budget must be an ExecutionBudget or None"
            )
        object.__setattr__(self, "missing", missing)
        object.__setattr__(self, "conditions", conditions)
        object.__setattr__(self, "attempted", attempted)


__all__ = ["Blocker", "Reason"]
