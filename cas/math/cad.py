"""One-dimensional cylindrical algebraic decomposition, the simplest CAD.

Decompose a set of univariate polynomial conditions in x into ordered, pairwise
disjoint cells (open intervals plus points) that cover the whole line, and decide
each condition's truth value on each cell. This is the shared foundation of
piecewise differentiation/integration and equation solving.

Decision channels, all exact, no approximation:
· open cell: take a root-free rational sample point and sign the boundary
  polynomial exactly;
· point cell (a root): if the condition's boundary polynomial vanishes there
  the value is 0; otherwise the sign is constant in a small neighbourhood and
  is read from the midpoint of the isolating interval.

Honest boundary: a condition that is not a univariate polynomial is refused;
multivariate partitioning is FRAGMENT, and transcendental root comparison is
UNDECIDABLE.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass, field
from fractions import Fraction as Fr
from typing import TYPE_CHECKING, Literal, TypeAlias

from cas.errors import CadError
from cas.kernel.verdict import Reason
from cas.math.domains.base import Ring, RingError
from cas.math.domains.poly import Poly, from_term, p_mul
from cas.math.domains.polytools import p_deg
from cas.math.domains.qarith import fold
from cas.math.realroot import (
    RootInterval,
    coef_sign,
    count_roots_open,
    p_eval_at,
    real_roots_intervals,
    squarefree_part,
    sturm_sequence,
)
from cas.syntax import term as T
from cas.syntax.term import Expr, Sym, Term
from cas.syntax.termpath import free_vars

if TYPE_CHECKING:
    from cas.math.context import MathContext

_COMPARISONS = frozenset({"Lt", "Le", "Gt", "Ge", "Eq", "Ne"})


def _coeff_ring(ctx: MathContext) -> Ring:
    """Select the unique ordered field with explicit rational real evaluation."""
    try:
        domain = ctx.domains.require_unique(
            lambda candidate: (
                candidate.is_field
                and candidate.is_ordered
                and candidate.ring is not None
                and candidate.ring.supports_rational_evaluation
            ),
            "CAD rational coefficient ring",
        )
    except RingError as error:
        raise CadError(str(error), Reason.FRAGMENT) from error
    if domain.ring is None or not domain.ring.supports_rational_evaluation:
        raise CadError("selected CAD domain cannot evaluate rational coefficients",
                       Reason.FRAGMENT)
    return domain.ring


@dataclass(frozen=True, slots=True)
class OpenCell:
    """An open interval with a root-free rational sample point."""

    sample: Fr
    lo: RootInterval | None = None
    hi: RootInterval | None = None
    kind: Literal["open"] = field(init=False, default="open")


@dataclass(frozen=True, slots=True)
class PointCell:
    """A point cell represented by an exact or isolating rational interval."""

    iso: RootInterval
    kind: Literal["point"] = field(init=False, default="point")

    @property
    def lo(self) -> RootInterval:
        return self.iso

    @property
    def hi(self) -> RootInterval:
        return self.iso


Cell: TypeAlias = OpenCell | PointCell


# ---------------------------------------------------------------------------
# Condition to boundary polynomial
# ---------------------------------------------------------------------------


def _refusal_reason(difference: Term, variable: Sym) -> Reason:
    variables = free_vars(difference)
    if any(symbol is not variable for symbol in variables):
        return Reason.FRAGMENT
    return Reason.UNDECIDABLE


def _boundary(ctx: MathContext, condition: Expr, variable: Sym) -> Poly:
    """Return the two sides' difference as a univariate polynomial."""
    left, right = condition.args
    difference = fold(T.plus(left, T.neg(right)))
    polynomial = from_term(_coeff_ring(ctx), difference, (variable,))
    if polynomial is None:
        raise CadError(
            f"condition is not a univariate polynomial partition: {condition!r}",
            _refusal_reason(difference, variable),
        )
    return polynomial


def extract_boundary_polys(
    ctx: MathContext,
    condition: Term,
    variable: Sym,
) -> list[Poly]:
    """Recursively collect nonconstant boundary polynomials of a condition."""
    if condition is T.TRUE or condition is T.FALSE or isinstance(condition, T.BVal):
        return []
    if isinstance(condition, Expr):
        head = condition.head.name
        if head in ("And", "Or"):
            output: list[Poly] = []
            for argument in condition.args:
                output.extend(extract_boundary_polys(ctx, argument, variable))
            return output
        if head == "Not":
            return extract_boundary_polys(ctx, condition.args[0], variable)
        if head in _COMPARISONS:
            polynomial = _boundary(ctx, condition, variable)
            return [polynomial] if p_deg(polynomial, 0) > 0 else []
    raise CadError(f"not a propositional condition: {condition!r}", Reason.FRAGMENT)


# ---------------------------------------------------------------------------
# Cell construction
# ---------------------------------------------------------------------------


def cells(ctx: MathContext, polynomials: Sequence[Poly]) -> list[Cell]:
    """Produce ordered cells covering the whole real line."""
    if not polynomials:
        return [OpenCell(sample=Fr(0))]
    ring = _coeff_ring(ctx)
    product = polynomials[0]
    for polynomial in polynomials[1:]:
        product = p_mul(ring, product, polynomial)
    intervals = real_roots_intervals(ring, product)
    if not intervals:
        return [OpenCell(sample=Fr(0))]
    output: list[Cell] = []
    first_lower, _ = intervals[0]
    output.append(OpenCell(sample=first_lower - 1, hi=intervals[0]))
    for index, (lower, upper) in enumerate(intervals):
        output.append(PointCell(iso=(lower, upper)))
        if index + 1 < len(intervals):
            next_lower, next_upper = intervals[index + 1]
            output.append(
                OpenCell(
                    sample=(upper + next_lower) / 2,
                    lo=(lower, upper),
                    hi=(next_lower, next_upper),
                )
            )
    _, last_upper = intervals[-1]
    output.append(OpenCell(sample=last_upper + 1, lo=intervals[-1]))
    return output


# ---------------------------------------------------------------------------
# Sign determination on a cell
# ---------------------------------------------------------------------------


def sign_at_cell(ctx: MathContext, polynomial: Poly, cell: Cell) -> int:
    """Return the exact sign of a boundary polynomial on one cell."""
    if polynomial.is_zero():
        return 0
    if isinstance(cell, OpenCell):
        return coef_sign(p_eval_at(_coeff_ring(ctx), polynomial, cell.sample))
    lower, upper = cell.iso
    if lower == upper:
        return coef_sign(p_eval_at(_coeff_ring(ctx), polynomial, lower))
    ring = _coeff_ring(ctx)
    squarefree = squarefree_part(ring, polynomial)
    sequence = sturm_sequence(ring, squarefree)
    if count_roots_open(ring, sequence, squarefree, lower, upper) >= 1:
        return 0
    return coef_sign(
        p_eval_at(ring, polynomial, (lower + upper) / 2)
    )


def _apply_cmp(operator: str, sign: int) -> bool:
    if operator == "Lt":
        return sign < 0
    if operator == "Le":
        return sign <= 0
    if operator == "Gt":
        return sign > 0
    if operator == "Ge":
        return sign >= 0
    if operator == "Eq":
        return sign == 0
    return sign != 0


def cond_holds(
    ctx: MathContext,
    condition: Term,
    cell: Cell,
    variable: Sym,
) -> bool:
    """Return the constant truth value of a condition on one cell."""
    if condition is T.TRUE:
        return True
    if condition is T.FALSE:
        return False
    if not isinstance(condition, Expr):
        raise CadError(f"not a propositional condition: {condition!r}", Reason.FRAGMENT)
    head = condition.head.name
    if head == "And":
        return all(cond_holds(ctx, argument, cell, variable) for argument in condition.args)
    if head == "Or":
        return any(cond_holds(ctx, argument, cell, variable) for argument in condition.args)
    if head == "Not":
        return not cond_holds(ctx, condition.args[0], cell, variable)
    if head in _COMPARISONS:
        polynomial = _boundary(ctx, condition, variable)
        return _apply_cmp(head, sign_at_cell(ctx, polynomial, cell))
    raise CadError(f"not a propositional condition: {condition!r}", Reason.FRAGMENT)


# ---------------------------------------------------------------------------
# Partition resolution (public entry point)
# ---------------------------------------------------------------------------


def resolve_partition(
    ctx: MathContext,
    conditions: Sequence[Term],
    variable: Sym,
) -> list[tuple[Cell, list[bool]]]:
    """Resolve conditions into ordered cells and constant truth labels."""
    polynomials: list[Poly] = []
    for condition in conditions:
        polynomials.extend(extract_boundary_polys(ctx, condition, variable))
    return [
        (cell, [cond_holds(ctx, condition, cell, variable) for condition in conditions])
        for cell in cells(ctx, polynomials)
    ]
