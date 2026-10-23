"""The independent coefficient-level derivative verifier."""

from fractions import Fraction

import pytest

from cas.algebra.polynomial import PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId
from cas.math.calculus.differentiation.verify import verify_derivative

X, Y = SymbolId(1), SymbolId(2)
Q = RationalField()
UX = UnivariatePolynomialRing(X, Q)
R = PolynomialRing((X, Y), Q)


class RingWithoutDerivative:
    """A proxy that fails loudly if the verifier asks for the ring's derivative."""

    def __init__(self, ring):
        self._ring = ring

    def __getattr__(self, name):
        if name == "derivative":
            raise AssertionError("the verifier called the ring derivative")
        return getattr(self._ring, name)


def x():
    return UX.generator(0)


def test_constants_have_derivative_zero():
    assert verify_derivative(UX, UX.constant(Fraction(7)), UX.zero(), 0)
    assert verify_derivative(UX, UX.zero(), UX.zero(), 0)


def test_the_generator_has_derivative_one():
    assert verify_derivative(UX, x(), UX.one(), 0)


def test_a_power_uses_the_integer_coefficient_rule():
    square = UX.pow(x(), 2)
    assert verify_derivative(UX, square, UX.mul_int(x(), 2), 0)
    cube = UX.pow(x(), 3)
    assert verify_derivative(UX, cube, UX.mul_int(UX.pow(x(), 2), 3), 0)
    assert not verify_derivative(UX, cube, UX.mul_int(UX.pow(x(), 2), 2), 0)


def test_a_sum_differentiates_termwise():
    source = UX.add(UX.pow(x(), 3), UX.mul_int(x(), 4))
    candidate = UX.add(UX.mul_int(UX.pow(x(), 2), 3), UX.constant(Fraction(4)))
    assert verify_derivative(UX, source, candidate, 0)
    assert not verify_derivative(
        UX, source, UX.add(candidate, UX.one()), 0
    )


def test_multivariate_derivatives_select_the_index():
    source = R.add(R.monomial((2, 1), Fraction(1)), R.monomial((0, 2), Fraction(1)))
    in_x = R.monomial((1, 1), Fraction(2))
    in_y = R.add(R.monomial((2, 0), Fraction(1)), R.monomial((0, 1), Fraction(2)))
    assert verify_derivative(R, source, in_x, 0)
    assert verify_derivative(R, source, in_y, 1)
    assert not verify_derivative(R, source, in_y, 0)


def test_ownership_is_checked():
    other = UnivariatePolynomialRing(X, Q)
    with pytest.raises(ValueError):
        verify_derivative(UX, other.zero(), UX.zero(), 0)
    with pytest.raises(ValueError):
        verify_derivative(UX, UX.zero(), other.zero(), 0)


def test_verification_never_calls_the_ring_derivative():
    source = UX.add(UX.pow(x(), 3), UX.mul_int(x(), 2))
    candidate = UX.add(UX.mul_int(UX.pow(x(), 2), 3), UX.constant(Fraction(2)))
    assert verify_derivative(RingWithoutDerivative(UX), source, candidate, 0)
