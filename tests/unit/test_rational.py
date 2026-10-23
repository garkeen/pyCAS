"""K(x): canonical fractions, field operations and the formal derivative."""

from fractions import Fraction

import pytest

from cas.algebra.polynomial import (
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.protocols import Euclidean, Field
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)
UX = UnivariatePolynomialRing(X, RationalField())
F = RationalFunctionField(UX)


def up(*coefficients: int | Fraction) -> Polynomial[Fraction]:
    """A univariate polynomial from low-to-high coefficients."""
    value = UX.zero()
    for power, coefficient in enumerate(coefficients):
        value = UX.add(
            value, UX.monomial((power,), Fraction(coefficient))
        )
    return value


def x() -> Polynomial[Fraction]:
    return up(0, 1)


def test_k_x_is_a_field_with_a_polynomial_ring():
    assert isinstance(F, Field)
    assert not isinstance(F, Euclidean)
    assert F.polynomials is UX


def test_zero_is_stored_as_zero_over_one():
    zero = F.zero()
    assert zero.numerator.is_zero()
    assert UX.is_one(zero.denominator)
    assert F.equal(F.fraction(UX.zero(), up(1, 1)), zero)


def test_construction_reduces_to_coprime_terms():
    reduced = F.fraction(up(-1, 0, 1), up(-1, 1))
    assert UX.equal(reduced.numerator, up(1, 1))
    assert UX.is_one(reduced.denominator)


def test_construction_makes_the_denominator_monic():
    value = F.fraction(up(1, 1), up(0, 2))
    assert UX.equal(value.denominator, x())
    assert UX.equal(
        value.numerator, up(Fraction(1, 2), Fraction(1, 2))
    )


def test_a_common_scalar_factor_is_cancelled():
    value = F.fraction(up(2, 2), up(2))
    assert F.equal(value, F.of_polynomial(up(1, 1)))


def test_field_operations_on_canonical_fractions():
    a = F.fraction(up(1), up(1, 1))
    b = F.fraction(up(0, 1), up(1, 1))
    assert F.equal(F.add(a, b), F.one())
    assert F.equal(F.sub(a, a), F.zero())
    assert F.equal(F.add(a, F.neg(a)), F.zero())
    assert F.equal(
        F.mul(a, b), F.fraction(up(0, 1), up(1, 2, 1))
    )
    assert F.equal(F.div(a, b), F.fraction(up(1), up(0, 1)))
    assert F.equal(F.inv(b), F.fraction(up(1, 1), up(0, 1)))
    assert F.equal(F.pow(a, 0), F.one())
    assert F.equal(F.pow(a, 2), F.mul(a, a))
    assert F.equal(F.mul_int(a, 2), F.add(a, a))


def test_equality_compares_canonical_representatives():
    assert F.equal(F.fraction(up(2, 2), up(2)), F.of_polynomial(up(1, 1)))
    assert F.equal(F.fraction(x(), up(2)), F.of_polynomial(UX.monomial((1,), Fraction(1, 2))))
    assert not F.equal(F.one(), F.zero())


def test_inversion_and_division_refuse_zero():
    with pytest.raises(ZeroDivisionError):
        F.inv(F.zero())
    with pytest.raises(ZeroDivisionError):
        F.div(F.one(), F.zero())


def test_denominator_must_be_nonzero():
    with pytest.raises(ZeroDivisionError):
        F.fraction(up(1), UX.zero())


def test_ownership_is_enforced():
    other = RationalFunctionField(UX)
    foreign = other.one()
    assert not F.contains(foreign)
    with pytest.raises(ValueError):
        F.add(F.one(), foreign)
    with pytest.raises(ValueError):
        F.equal(F.one(), foreign)
    other_ring = UnivariatePolynomialRing(X, RationalField())
    with pytest.raises(ValueError):
        F.fraction(other_ring.one(), UX.one())


def test_formal_derivative():
    assert F.equal(F.derivative(F.of_polynomial(x())), F.one())
    assert F.equal(
        F.derivative(F.fraction(up(1), up(0, 1))),
        F.fraction(up(-1), up(0, 0, 1)),
    )
    quotient = F.fraction(up(1, 0, 1), up(-1, 1))
    assert F.equal(
        F.derivative(quotient),
        F.fraction(up(-1, -2, 1), up(1, -2, 1)),
    )
    assert F.equal(F.derivative(F.zero()), F.zero())
    with pytest.raises(IndexError):
        F.derivative(F.one(), 1)


def test_derivative_obeys_the_product_rule():
    a = F.fraction(up(1, 2), up(1, 1))
    b = F.fraction(up(-1, 0, 1), up(0, 1))
    assert F.equal(
        F.derivative(F.mul(a, b)),
        F.add(F.mul(F.derivative(a), b), F.mul(a, F.derivative(b))),
    )


def test_k_x_requires_a_univariate_polynomial_ring():
    with pytest.raises(TypeError):
        RationalFunctionField(PolynomialRing((X,), RationalField()))


def test_elements_cannot_be_built_by_hand():
    with pytest.raises(ValueError):
        RationalFunction(F, UX.zero(), UX.one(), object())
