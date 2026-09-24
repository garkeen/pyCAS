"""Constraint solving over the shared linear-form channel."""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction
from typing import TYPE_CHECKING

from cas.math.domains.base import DomainElement, Ring
from cas.math.domains.linalg import solve_system
from cas.math.linearform import normalized, relation
from cas.math.project import zero_of
from cas.syntax import term as T
from cas.syntax.term import Sym, Term

if TYPE_CHECKING:
    from cas.math.context import MathContext


class TermField(Ring):
    """Adapt syntax terms to the explicit algebraic elimination interface."""

    is_field = True

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    @staticmethod
    def _term(value: DomainElement) -> Term:
        if not isinstance(value, Term):
            raise TypeError("TermField expected a syntax term")
        return value

    def from_int(self, value: int) -> DomainElement:
        return T.N(value)

    def from_frac(self, value: Fraction) -> DomainElement:
        return T.N(value)

    def is_zero(self, value: DomainElement) -> bool:
        return zero_of(self.ctx, self._term(value)) is True

    def add(self, left: DomainElement, right: DomainElement) -> DomainElement:
        return normalized(
            self.ctx,
            T.plus(self._term(left), self._term(right)),
        )

    def mul(self, left: DomainElement, right: DomainElement) -> DomainElement:
        return normalized(
            self.ctx,
            T.times(self._term(left), self._term(right)),
        )

    def neg(self, value: DomainElement) -> DomainElement:
        return normalized(self.ctx, T.neg(self._term(value)))

    def equal(self, left: DomainElement, right: DomainElement) -> bool:
        return zero_of(
            self.ctx,
            T.plus(self._term(left), T.neg(self._term(right))),
        ) is True

    def div_exact(self, left: DomainElement, right: DomainElement) -> DomainElement:
        return normalized(
            self.ctx,
            T.times(self._term(left), T.pw(self._term(right), T.MONE)),
        )


def solve_linear_constraints(
    ctx: MathContext,
    relation_terms: Sequence[Term],
    unknowns: Sequence[Sym],
) -> tuple[dict[Sym, Term], bool] | None:
    """Return a linear valuation and completeness flag, or ``None``."""
    unknown_tuple = tuple(unknowns)
    rows: list[list[Term]] = []
    rhs_values: list[Term] = []
    for relation_term in relation_terms:
        converted = relation(ctx, relation_term, unknown_tuple)
        if converted is None:
            return None
        row, rhs = converted
        rows.append(row)
        rhs_values.append(rhs)

    solution = solve_system(TermField(ctx), rows, rhs_values)
    if solution is None:
        return None
    particular, homogeneous = solution
    valuation: dict[Sym, Term] = {}
    for index, unknown in enumerate(unknown_tuple):
        value = particular[index]
        if not isinstance(value, Term):
            raise TypeError("linear solver returned a non-term value")
        valuation[unknown] = value
    return valuation, not homogeneous
