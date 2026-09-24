"""The typed math algorithm facade injected into the workflow."""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING

from cas.syntax import term as T
from cas.syntax.term import Sym, Term

if TYPE_CHECKING:
    from cas.math.context import MathContext


class Algorithms:
    """Math capabilities exposed to the workflow without a math import."""

    def __init__(self, math: MathContext) -> None:
        self._math = math

    def domain_of(self, term: Term) -> str:
        """Return the projected domain name, or an empty string on a miss."""
        from cas.math.project import project
        from cas.syntax.term import Expr

        candidate = term
        if (
            isinstance(term, Expr)
            and isinstance(term.head, Sym)
            and term.head.name == "Eq"
        ):
            left, right = term.args
            candidate = T.plus(left, T.neg(right))
        hit = project(self._math, candidate)
        return hit.name if hit is not None else ""

    def solve_linear_constraints(
        self,
        relations: tuple[Term, ...],
        unknowns: tuple[Sym, ...],
    ) -> tuple[dict[Sym, Term], bool] | None:
        """Return a linear valuation and completeness flag, or ``None``."""
        from cas.math.constraints import solve_linear_constraints

        return solve_linear_constraints(self._math, relations, unknowns)

    def expand_definitions(
        self,
        definitions: Mapping[Term, Term],
        term: Term,
    ) -> Term:
        """Expand the scope's definitions through the automatic channel."""
        from cas.math.definitions import expand

        return expand(definitions.get, term)
