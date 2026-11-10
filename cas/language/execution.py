"""Execution strategy and structural budget.

A problem fixes what is requested; an execution request fixes how one attempt
may answer it.  The condition policy says whether open obligations are allowed
to remain in the published result, and the budget bounds the certificate the
attempt may submit.  Neither changes the mathematical problem: retrying the
same problem with a larger budget keeps the same meaning.

The budget's `None` fields defer to the certificate schema registered for the
checker.  A concrete field can only tighten that schema's limit; it never
widens it.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum


class ConditionPolicy(StrEnum):
    """How open obligations are handled at the submission boundary."""

    REQUIRE_PROVED = "require_proved"
    ALLOW_CONDITIONAL = "allow_conditional"
    REQUEST_CASES = "request_cases"


@dataclass(frozen=True, slots=True)
class ExecutionBudget:
    """The structural limits one execution attempt may spend.

    `None` means the checker's certificate schema supplies the limit.  A
    concrete value must be a positive integer and is applied as an additional
    upper bound, never as a replacement that could admit a larger certificate.
    """

    max_nodes: int | None = None
    max_depth: int | None = None

    def __post_init__(self) -> None:
        for label, value in (
            ("max_nodes", self.max_nodes),
            ("max_depth", self.max_depth),
        ):
            if value is None:
                continue
            if isinstance(value, bool) or not isinstance(value, int):
                raise TypeError(
                    f"an execution budget {label} must be an int or None"
                )
            if value <= 0:
                raise ValueError(
                    f"an execution budget {label} must be positive"
                )


@dataclass(frozen=True, slots=True)
class BudgetTicket:
    """One immutable budget snapshot with the consumption charged so far.

    A ticket is shared between a top-level request, its subtasks and the
    checker: spending never mutates the ticket, it returns a new ticket whose
    counters include the charge.  A charge that would exceed either concrete
    limit returns `None`, so the caller reports `BUDGET` instead of receiving a
    ticket that has silently exceeded its bounds.  A `None` limit defers to the
    certificate schema and is not enforced here.
    """

    budget: ExecutionBudget
    consumed_nodes: int = 0
    consumed_depth: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.budget, ExecutionBudget):
            raise TypeError("a budget ticket needs an ExecutionBudget")
        for label, value in (
            ("consumed nodes", self.consumed_nodes),
            ("consumed depth", self.consumed_depth),
        ):
            if isinstance(value, bool) or not isinstance(value, int):
                raise TypeError(f"a budget ticket {label} must be an int")
            if value < 0:
                raise ValueError(
                    f"a budget ticket {label} must be nonnegative"
                )

    def spend(self, nodes: int, depth: int) -> BudgetTicket | None:
        """Charge `nodes` and `depth`, or return `None` when over budget."""
        for label, value in (("nodes", nodes), ("depth", depth)):
            if isinstance(value, bool) or not isinstance(value, int):
                raise TypeError(f"a budget charge {label} must be an int")
            if value < 0:
                raise ValueError(
                    f"a budget charge {label} must be nonnegative"
                )
        consumed_nodes = self.consumed_nodes + nodes
        consumed_depth = self.consumed_depth + depth
        if (
            self.budget.max_nodes is not None
            and consumed_nodes > self.budget.max_nodes
        ):
            return None
        if (
            self.budget.max_depth is not None
            and consumed_depth > self.budget.max_depth
        ):
            return None
        return BudgetTicket(self.budget, consumed_nodes, consumed_depth)


__all__ = ["BudgetTicket", "ConditionPolicy", "ExecutionBudget"]
