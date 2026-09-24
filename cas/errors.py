"""Shared typed exception hierarchy."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from cas.kernel.verdict import Reason


class BudgetExceeded(Exception):
    def __init__(self, spent: int = 0, message: str = "evaluation budget exceeded") -> None:
        self.spent = spent
        super().__init__(message)


class ParseError(Exception):
    """Surface text cannot be decoded by the syntax parser."""


class ScopeError(Exception):
    """A declaration or definition violates the scope contract."""


class BranchError(Exception):
    """A branch operation violates coverage, lineage, or namespace rules."""


class TacticsError(Exception):
    """A solving tactic cannot complete inside its admitted fragment."""


class DiffError(Exception):
    """Differentiation is unsupported for the requested expression."""


class CadError(Exception):
    """A CAD partition request is outside the implemented fragment."""

    def __init__(self, message: str, reason: Reason | None = None) -> None:
        super().__init__(message)
        self.reason = reason


class PiecewiseError(Exception):
    """A Piecewise container is structurally invalid."""


class IntegrateError(Exception):
    """Integration is unsupported for the requested expression."""

    def __init__(self, message: str, reason: Reason | None = None) -> None:
        super().__init__(message)
        self.reason = reason
