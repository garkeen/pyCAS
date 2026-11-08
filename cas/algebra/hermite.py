"""Hermite reduction of a rational function.

For `f = a/b` over a characteristic-zero field, Hermite reduction returns

    f = D(v) + r

where `r` has a squarefree denominator.  The repeated part of the denominator
is absorbed into the derivative of a rational function `v`; the remainder keeps
its true denominator and is not presented as a complete integral.

The algorithm is the classical Hermite reduction as presented in Bronstein,
*Symbolic Integration I*, §4.4, and Geddes--Czapor--Labahn, *Algorithms for
Computer Algebra*, §11.2.  The linear equation for each squarefree factor is
solved by exact Gaussian elimination over the coefficient field.  The local
reference implementation is FriCAS `src/algebra/intrf.spad:208-276`
(`TranscendentalHermiteIntegration`, `normalHermiteIntegrate`); this module
uses the per-factor repeated reduction rather than FriCAS's parallel pass, but
the contract `f = D(v) + r` with squarefree denominator is the same.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Generic, TypeVar

from cas.algebra.linear import AffineSolution, Inconsistent, MatrixSpace
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunction, RationalFunctionField

E = TypeVar("E")


class HermiteError(ValueError):
    """The reduction could not be completed inside the declared fragment."""


@dataclass(frozen=True, slots=True)
class HermiteReduction(Generic[E]):
    """`value == D(polynomial_part) + remainder` with squarefree remainder."""

    polynomial_part: RationalFunction[E]
    remainder: RationalFunction[E]


def hermite_reduce(
    field: RationalFunctionField[E],
    value: RationalFunction[E],
) -> HermiteReduction[E]:
    """Reduce the repeated part of `value`'s denominator."""
    polynomials = field.polynomials
    _require_characteristic_zero(polynomials)
    numerator = value.numerator
    denominator = value.denominator
    if polynomials.degree(denominator, 0) == 0:
        return HermiteReduction(field.zero(), value)
    unit, factors = polynomials.squarefree_decomposition(denominator)
    if not polynomials.coefficients.is_one(unit):
        raise AssertionError("a reduced denominator must be monic")
    polynomial_part = field.zero()
    for factor, multiplicity in factors:
        for current in range(multiplicity, 1, -1):
            power = polynomials.pow(factor, current)
            rest = polynomials.exact_div(denominator, power)
            gcd, inverse, _ = polynomials.xgcd(rest, factor)
            if not polynomials.is_one(gcd):
                raise HermiteError(
                    "a squarefree denominator factor is not coprime to its rest"
                )
            right_hand_side = polynomials.divmod(
                polynomials.mul(numerator, inverse), factor
            )[1]
            coefficient = _solve_reduction_equation(
                polynomials, factor, current, right_hand_side
            )
            derivative = polynomials.sub(
                polynomials.mul(
                    factor, polynomials.derivative(coefficient, 0)
                ),
                polynomials.mul_int(
                    polynomials.mul(
                        polynomials.derivative(factor, 0), coefficient
                    ),
                    current - 1,
                ),
            )
            adjusted = polynomials.sub(
                numerator, polynomials.mul(rest, derivative)
            )
            numerator = polynomials.exact_div(adjusted, factor)
            denominator = polynomials.exact_div(denominator, factor)
            polynomial_part = field.add(
                polynomial_part,
                field.fraction(
                    coefficient,
                    polynomials.pow(factor, current - 1),
                ),
            )
    return HermiteReduction(
        polynomial_part, field.fraction(numerator, denominator)
    )


def _solve_reduction_equation(
    polynomials: UnivariatePolynomialRing[E],
    factor: Polynomial[E],
    multiplicity: int,
    right_hand_side: Polynomial[E],
) -> Polynomial[E]:
    """Solve `factor*c' - (m-1)*factor'*c == rhs (mod factor)`."""
    coefficients = polynomials.coefficients
    degree = polynomials.degree(factor, 0)
    if degree <= 0:
        raise HermiteError("a reduction factor must be nonconstant")
    derivative_factor = polynomials.derivative(factor, 0)
    columns: list[list[E]] = []
    for index in range(degree):
        basis = polynomials.monomial((index,), coefficients.one())
        image = polynomials.sub(
            polynomials.mul(factor, polynomials.derivative(basis, 0)),
            polynomials.mul_int(
                polynomials.mul(derivative_factor, basis),
                multiplicity - 1,
            ),
        )
        remainder = polynomials.divmod(image, factor)[1]
        columns.append(
            [
                polynomials.coefficient(remainder, (row,))
                for row in range(degree)
            ]
        )
    rows = [
        [columns[column][row] for column in range(degree)]
        for row in range(degree)
    ]
    right = [
        polynomials.coefficient(right_hand_side, (row,))
        for row in range(degree)
    ]
    space = MatrixSpace(coefficients, degree, degree)
    solution = space.solve(space.matrix(rows), right)
    if isinstance(solution, Inconsistent):
        raise HermiteError(
            "the Hermite reduction equation has no solution"
        )
    assert isinstance(solution, AffineSolution)
    return polynomials.sum(
        polynomials.monomial((index,), coefficient)
        for index, coefficient in enumerate(solution.particular)
    )


def _require_characteristic_zero(
    polynomials: UnivariatePolynomialRing[Any],
) -> None:
    if polynomials.coefficients.characteristic != 0:
        raise HermiteError(
            "Hermite reduction needs a characteristic-zero coefficient field"
        )


__all__ = ["HermiteError", "HermiteReduction", "hermite_reduce"]
