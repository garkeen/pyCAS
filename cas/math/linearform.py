"""Linear-form decomposition over explicit syntactic and semantic channels."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal, TypeAlias

from cas.math.domains.base import DomainElement, Monomial, Ring
from cas.math.domains.poly import MonomialKey, _norm, to_term
from cas.math.project import is_zero, project
from cas.math.project import normalize as project_normalize
from cas.syntax import term as T
from cas.syntax.term import Sym, Term
from cas.syntax.termpath import free_vars

if TYPE_CHECKING:
    from cas.math.context import MathContext

Decomposition: TypeAlias = tuple[dict[Sym, Term], Term]
LinearFormKind: TypeAlias = Literal[
    "outside", "constant", "no_view", "zero", "independent", "degree", "linear"
]
LinearFormPayload: TypeAlias = str | bool | int | tuple[Term, Term] | None


def decompose(term: Term, unknowns: Sequence[Sym]) -> Decomposition | None:
    """Return syntactic coefficients and a constant, or ``None``."""
    unknown_tuple = tuple(unknowns)
    unknown_set = set(unknown_tuple)
    if isinstance(term, T.Sym) and term in unknown_set:
        return {term: T.ONE}, T.ZERO
    if not (free_vars(term) & unknown_set):
        return {}, term
    if not isinstance(term, T.Expr):
        return None
    name = term.head.name
    if name == "Plus":
        coefficients: dict[Sym, Term] = {}
        constant: Term = T.ZERO
        for argument in term.args:
            part = decompose(argument, unknown_tuple)
            if part is None:
                return None
            for symbol, value in part[0].items():
                coefficients[symbol] = T.plus(
                    coefficients.get(symbol, T.ZERO), value
                )
            constant = T.plus(constant, part[1])
        return coefficients, constant
    if name == "Times":
        parts: list[Decomposition] = []
        for argument in term.args:
            part = decompose(argument, unknown_tuple)
            if part is None:
                return None
            parts.append(part)
        unknown_indices = [
            index for index, part in enumerate(parts) if part[0]
        ]
        if len(unknown_indices) > 1:
            return None
        if not unknown_indices:
            product: Term = T.ONE
            for _coefficients, constant in parts:
                product = T.times(product, constant)
            return {}, product
        unknown_index = unknown_indices[0]
        factor: Term = T.ONE
        for index, (_coefficients, constant) in enumerate(parts):
            if index != unknown_index:
                factor = T.times(factor, constant)
        coefficients, constant = parts[unknown_index]
        return (
            {
                symbol: T.times(value, factor)
                for symbol, value in coefficients.items()
            },
            T.times(constant, factor),
        )
    if name == "Power" and len(term.args) == 2 and term.args[1] is T.ONE:
        return decompose(term.args[0], unknown_tuple)
    return None


def is_linear(term: Term, unknowns: Sequence[Sym]) -> bool:
    """Return whether a term is linear in the supplied unknowns."""
    return decompose(term, unknowns) is not None


def normalized(ctx: MathContext, term: Term) -> Term:
    """Normalize a coefficient through projection, or fold literal arithmetic."""
    hit = project(ctx, term)
    if hit is not None:
        return project_normalize(hit)
    from cas.math.domains.qarith import fold

    return fold(term)


def relation(
    ctx: MathContext,
    relation_term: Term,
    unknowns: Sequence[Sym],
) -> tuple[list[Term], Term] | None:
    """Convert an equation into a coefficient row and right-hand side."""
    if not (
        isinstance(relation_term, T.Expr)
        and isinstance(relation_term.head, Sym)
        and relation_term.head.name == "Eq"
    ):
        return None
    left, right = relation_term.args
    left_form = decompose(left, unknowns)
    right_form = decompose(right, unknowns)
    if left_form is None or right_form is None:
        return None
    left_coefficients, left_constant = left_form
    right_coefficients, right_constant = right_form
    row = [
        normalized(
            ctx,
            T.plus(
                left_coefficients.get(unknown, T.ZERO),
                T.neg(right_coefficients.get(unknown, T.ZERO)),
            ),
        )
        for unknown in unknowns
    ]
    right_value = normalized(
        ctx,
        T.plus(right_constant, T.neg(left_constant)),
    )
    return row, right_value


@dataclass(frozen=True, slots=True)
class LinearForm:
    """A semantic classification of a term relative to one variable."""

    kind: LinearFormKind
    payload: LinearFormPayload = None


def _coefficient(
    ring: Ring,
    monomials: tuple[Monomial, ...],
    variable_index: int,
    power: int,
    remaining_variables: tuple[Sym, ...],
) -> Term:
    coefficients: dict[MonomialKey, DomainElement] = {}
    for exponents, value in monomials:
        if exponents[variable_index] == power:
            coefficients[
                tuple(
                    exponent
                    for index, exponent in enumerate(exponents)
                    if index != variable_index
                )
            ] = value
    return to_term(ring, _norm(ring, remaining_variables, coefficients))


def linear_form(ctx: MathContext, term: Term, variable: Sym) -> LinearForm:
    """Classify a term as a linear form in one variable."""
    hit = project(ctx, term)
    if hit is None:
        return LinearForm("outside", "outside the declared projection domains")
    if hit.element is None:
        return LinearForm("constant", is_zero(hit))
    element = hit.domain.element_poly(hit.element)
    if element is None:
        return LinearForm("no_view", "the projected domain exposes no polynomial view")
    if element.is_zero():
        return LinearForm("zero")
    if variable not in element.vars:
        return LinearForm("independent")
    index = element.vars.index(variable)
    powers = {monomial[index] for monomial, _value in element.monos}
    degree = max(powers)
    if degree == 0:
        return LinearForm("independent")
    if degree != 1:
        return LinearForm("degree", degree)
    ring = hit.domain.ring
    if ring is None:
        return LinearForm("no_view", "the projected domain has no coefficient ring")
    remaining = tuple(
        symbol for position, symbol in enumerate(element.vars) if position != index
    )
    return LinearForm(
        "linear",
        (
            _coefficient(ring, element.monos, index, 1, remaining),
            _coefficient(ring, element.monos, index, 0, remaining),
        ),
    )


def nonzero_condition(coefficient: Term) -> Term:
    """Return the condition required to divide by a linear coefficient."""
    return T.mk(T.S("Ne"), (coefficient, T.ZERO))
