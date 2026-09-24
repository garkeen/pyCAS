"""Exact polynomial integration and cautious piecewise definite integration.

The search implementation lives here; the independent antiderivative checker
lives under ``calculus/integration``.  Proper rational and transcendental
fragments refuse honestly until their required mathematical layers exist.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

from cas.errors import IntegrateError
from cas.kernel.verdict import Reason
from cas.math.cad import OpenCell, PointCell
from cas.math.domains.base import DomainElement, PolynomialView, Ring
from cas.math.domains.poly import MonomialKey, Poly, _norm, to_term
from cas.math.domains.qarith import fold
from cas.math.project import project
from cas.math.realroot import RootInterval
from cas.syntax import term as T
from cas.syntax.term import Sym, Term
from cas.syntax.termpath import subst

if TYPE_CHECKING:
    from cas.math.context import MathContext

_UNDEF = T.SP("Undefined")


def poly_antideriv(
    ring: Ring,
    polynomial: PolynomialView,
    variable_index: int,
) -> Poly:
    """Integrate a polynomial view by exact monomialwise powers."""
    coefficients: dict[MonomialKey, DomainElement] = {}
    for exponents, coefficient in polynomial.monos:
        shifted = tuple(
            exponent + (1 if index == variable_index else 0)
            for index, exponent in enumerate(exponents)
        )
        coefficients[shifted] = ring.div_exact(
            coefficient,
            ring.from_int(exponents[variable_index] + 1),
        )
    return _norm(ring, polynomial.vars, coefficients)


def integrate_term(
    ctx: MathContext,
    integrand: Term,
    variable: Sym,
) -> Term:
    """Integrate one term or a piecewise integrand branch by branch."""
    from cas.math.piecewise import is_piecewise

    if is_piecewise(integrand):
        return integrate_piecewise_indefinite(ctx, integrand, variable)
    hit = project(ctx, integrand)
    if hit is None:
        raise IntegrateError(
            "integrand is outside the rational/polynomial/rational-function domains",
            Reason.FRAGMENT,
        )
    if hit.element is None:
        return T.times(integrand, variable)
    element = hit.element
    variables = hit.domain.vars
    if variables is None:
        raise IntegrateError(
            f"integration is unavailable for the element view of {hit.domain.name}",
            Reason.FRAGMENT,
        )
    if variable not in variables:
        return T.times(integrand, variable)
    polynomial = hit.domain.element_as_poly(element)
    if polynomial is not None:
        ring = hit.domain.ring
        if ring is None:
            raise IntegrateError(
                f"integration requires a coefficient ring from {hit.domain.name}",
                Reason.FRAGMENT,
            )
        antiderivative = poly_antideriv(
            ring,
            polynomial,
            variables.index(variable),
        )
        return to_term(ring, antiderivative)
    raise IntegrateError(
        "proper rational integration needs Hermite reduction, not built",
        Reason.FRAGMENT,
    )


def integrate_piecewise_indefinite(
    ctx: MathContext,
    integrand: Term,
    variable: Sym,
) -> Term:
    """Integrate each branch while leaving its condition unchanged."""
    from cas.math.piecewise import branches, fold_nested, piecewise

    flattened = fold_nested(integrand)
    return piecewise(
        [
            (integrate_term(ctx, value, variable), condition)
            for value, condition in branches(flattened)
        ]
    )


def _require_rational(term: Term, role: str) -> Fraction:
    folded = fold(term)
    if not T.is_num(folded):
        raise IntegrateError(
            f"the {role} of integration must be rational",
            Reason.FRAGMENT,
        )
    return T.num_val(folded)


def _ftc(
    antiderivative: Term,
    variable: Sym,
    lower: Fraction,
    upper: Fraction,
) -> Term:
    at_lower = fold(subst(antiderivative, {variable: T.N(lower)}))
    at_upper = fold(subst(antiderivative, {variable: T.N(upper)}))
    return fold(T.plus(at_upper, T.neg(at_lower)))


def _rat_iso(
    interval: RootInterval | None,
    role: str,
) -> Fraction | None:
    """Decode an exact rational root isolator; None means unbounded."""
    if interval is None:
        return None
    lower, upper = interval
    if lower == upper:
        return lower
    raise IntegrateError(
        f"breakpoint at an irrational root needs exact location in an "
        f"algebraic extension ({role})",
        Reason.FRAGMENT,
    )


def definite_integrate(
    ctx: MathContext,
    integrand: Term,
    variable: Sym,
    lower: Term,
    upper: Term,
) -> Term:
    """Integrate exactly over a rational interval without crossing gaps."""
    lower_value = _require_rational(lower, "lower limit")
    upper_value = _require_rational(upper, "upper limit")
    if lower_value > upper_value:
        raise IntegrateError("lower limit is greater than upper limit")
    if lower_value == upper_value:
        return T.ZERO
    from cas.math.piecewise import is_piecewise

    if is_piecewise(integrand):
        return _definite_piecewise(
            ctx,
            integrand,
            variable,
            lower_value,
            upper_value,
        )
    antiderivative = integrate_term(ctx, integrand, variable)
    return _ftc(antiderivative, variable, lower_value, upper_value)


def _definite_piecewise(
    ctx: MathContext,
    integrand: Term,
    variable: Sym,
    lower: Fraction,
    upper: Fraction,
) -> Term:
    """Sum Newton-Leibniz contributions over defined open cells."""
    from cas.math.piecewise import domain_cells

    total: Term | None = None
    for cell, value in domain_cells(ctx, integrand, variable):
        if isinstance(cell, PointCell):
            point = _rat_iso(cell.iso, "point cell")
            if point is None:
                continue
            if lower <= point <= upper and value is _UNDEF:
                raise IntegrateError(
                    "integrand has an undefined point hole in [a, b]; improper "
                    "integration needs a limit layer, not built",
                    Reason.FRAGMENT,
                )
            continue
        if not isinstance(cell, OpenCell):
            raise TypeError("CAD returned a non-cell domain value")
        cell_lower = _rat_iso(cell.lo, "lower bound")
        cell_upper = _rat_iso(cell.hi, "upper bound")
        interval_lower = lower if cell_lower is None else max(lower, cell_lower)
        interval_upper = upper if cell_upper is None else min(upper, cell_upper)
        if interval_lower >= interval_upper:
            continue
        if value is _UNDEF:
            raise IntegrateError(
                "integrand has a gap in [a, b]; refusing to integrate across it",
                Reason.FRAGMENT,
            )
        contribution = _ftc(
            integrate_term(ctx, value, variable),
            variable,
            interval_lower,
            interval_upper,
        )
        total = (
            contribution
            if total is None
            else fold(T.plus(total, contribution))
        )
    if total is None:
        raise IntegrateError(
            "integration interval does not meet the domain: undefined rather than 0",
            Reason.FRAGMENT,
        )
    return total
