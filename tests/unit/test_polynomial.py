"""Polynomial rings: canonical storage, ownership, division and derivation."""

from fractions import Fraction

import pytest

from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import (
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.protocols import Euclidean
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)
Y = SymbolId(2)

Q = RationalField()
R = PolynomialRing((X, Y), Q)
UX = UnivariatePolynomialRing(X, Q)


def test_a_ring_needs_a_ring_of_coefficients_and_a_monomial_order():
    with pytest.raises(TypeError):
        PolynomialRing((X,), object())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        PolynomialRing((X,), Q, "lex")  # type: ignore[arg-type]


def test_constructors_produce_canonical_storage():
    assert R.zero().terms == ()
    assert R.zero().is_zero()
    assert R.one().terms == (((0, 0), Fraction(1)),)
    assert R.constant(Fraction(5)).terms == (((0, 0), Fraction(5)),)
    assert R.monomial((1, 2), Fraction(3)).terms == (
        ((1, 2), Fraction(3)),
    )
    assert R.generator(0).terms == (((1, 0), Fraction(1)),)
    assert R.generator(1).terms == (((0, 1), Fraction(1)),)


def test_storage_order_is_canonical():
    total = R.add(
        R.monomial((0, 1), Fraction(2)), R.monomial((1, 0), Fraction(1))
    )
    assert [exponents for exponents, _ in total.terms] == [(0, 1), (1, 0)]


def test_zero_coefficients_are_dropped():
    assert R.monomial((1, 0), Fraction(0)).is_zero()
    assert R.constant(Fraction(0)).is_zero()
    x = R.generator(0)
    assert R.add(x, R.neg(x)).is_zero()


def test_additive_and_multiplicative_operations():
    x, y = R.generator(0), R.generator(1)
    assert R.equal(R.add(x, y), R.add(y, x))
    assert R.equal(R.sub(R.add(x, y), y), x)
    assert R.equal(R.neg(R.neg(x)), x)
    assert R.equal(R.mul(x, y), R.monomial((1, 1), Fraction(1)))
    assert R.equal(R.mul_int(x, 3), R.monomial((1, 0), Fraction(3)))
    assert R.equal(R.pow(R.add(x, y), 0), R.one())


def test_expansion_of_a_product_and_a_power():
    x, y = R.generator(0), R.generator(1)
    square = R.pow(R.add(x, y), 2)
    assert R.coefficient(square, (2, 0)) == Fraction(1)
    assert R.coefficient(square, (1, 1)) == Fraction(2)
    assert R.coefficient(square, (0, 2)) == Fraction(1)
    assert len(square.terms) == 3
    assert R.equal(R.pow(R.add(x, y), 3), R.mul(square, R.add(x, y)))


def test_equality_is_structural():
    assert R.equal(
        R.monomial((1, 1), Fraction(2)),
        R.add(
            R.monomial((1, 1), Fraction(1)),
            R.monomial((1, 1), Fraction(1)),
        ),
    )
    assert not R.equal(R.generator(0), R.generator(1))


def test_ownership_is_enforced():
    other = PolynomialRing((X, Y), Q)
    foreign = other.one()
    assert not R.contains(foreign)
    assert R.contains(R.one())
    with pytest.raises(ValueError):
        R.add(R.one(), foreign)
    with pytest.raises(ValueError):
        R.equal(R.one(), foreign)
    with pytest.raises(ValueError):
        R.degree(foreign, 0)


def test_degree_and_coefficient():
    polynomial = R.add(
        R.monomial((2, 1), Fraction(3)),
        R.monomial((0, 1), Fraction(5)),
    )
    assert R.degree(polynomial, 0) == 2
    assert R.degree(polynomial, 1) == 1
    assert R.degree(R.zero(), 0) == -1
    assert R.coefficient(polynomial, (2, 1)) == Fraction(3)
    assert R.coefficient(polynomial, (5, 5)) == Fraction(0)
    with pytest.raises(ValueError):
        R.coefficient(polynomial, (1,))
    with pytest.raises(IndexError):
        R.degree(polynomial, 2)


def test_formal_derivative():
    polynomial = R.add(
        R.monomial((2, 1), Fraction(3)),
        R.monomial((0, 1), Fraction(1)),
    )
    assert R.equal(
        R.derivative(polynomial, 0), R.monomial((1, 1), Fraction(6))
    )
    assert R.equal(
        R.derivative(polynomial, 1),
        R.add(R.monomial((2, 0), Fraction(3)), R.constant(Fraction(1))),
    )
    assert R.derivative(R.constant(Fraction(7)), 0).is_zero()
    with pytest.raises(IndexError):
        R.derivative(polynomial, 2)


def test_ring_construction_validates_generators_and_monomials():
    with pytest.raises(ValueError):
        PolynomialRing((), Q)
    with pytest.raises(ValueError):
        PolynomialRing((X, X), Q)
    with pytest.raises(ValueError):
        R.monomial((1,), Q.one())
    with pytest.raises(ValueError):
        R.monomial((-1, 0), Q.one())
    with pytest.raises(IndexError):
        R.generator(2)


def test_univariate_division():
    x = UX.generator(0)
    square_minus_one = UX.sub(UX.pow(x, 2), UX.one())
    x_minus_one = UX.sub(x, UX.one())
    quotient, remainder = UX.divmod(square_minus_one, x_minus_one)
    assert UX.equal(quotient, UX.add(x, UX.one()))
    assert remainder.is_zero()

    quotient, remainder = UX.divmod(UX.pow(x, 2), UX.add(x, UX.one()))
    assert UX.equal(quotient, UX.sub(x, UX.one()))
    assert UX.equal(remainder, UX.one())

    dividend = UX.add(UX.mul(UX.pow(x, 3), UX.constant(Fraction(5))), UX.sub(x, UX.one()))
    divisor = UX.add(UX.constant(Fraction(1)), UX.mul_int(x, 2))
    quotient, remainder = UX.divmod(dividend, divisor)
    assert UX.equal(UX.add(UX.mul(divisor, quotient), remainder), dividend)
    assert UX.degree(remainder, 0) < UX.degree(divisor, 0)
    with pytest.raises(ZeroDivisionError):
        UX.divmod(dividend, UX.zero())


def test_gcd_rejects_elements_of_another_ring():
    other = UnivariatePolynomialRing(Y, Q)
    with pytest.raises(ValueError):
        UX.gcd(UX.zero(), other.zero())


def test_univariate_gcd_is_monic():
    x = UX.generator(0)
    x_minus_one = UX.sub(x, UX.one())
    square_minus_one = UX.sub(UX.pow(x, 2), UX.one())
    assert UX.equal(UX.gcd(square_minus_one, x_minus_one), x_minus_one)
    scaled = UX.mul(UX.constant(Fraction(2)), UX.add(x, UX.one()))
    assert UX.equal(UX.gcd(scaled, UX.zero()), UX.add(x, UX.one()))
    assert UX.gcd(UX.zero(), UX.zero()).is_zero()


def test_euclidean_capability_is_univariate_only():
    assert isinstance(UX, Euclidean)
    assert not isinstance(R, Euclidean)
    with pytest.raises(TypeError):
        UnivariatePolynomialRing(X, IntegerRing())


def test_elements_cannot_be_built_by_hand():
    with pytest.raises(ValueError):
        Polynomial(R, (), object())


def test_the_declared_monomial_order_controls_storage_order():
    from cas.algebra.polynomial import MonomialOrder

    lex = PolynomialRing((X, Y), Q, MonomialOrder.LEX)
    grlex = PolynomialRing((X, Y), Q, MonomialOrder.GRLEX)
    x_cubed = lex.monomial((3, 0), Fraction(1))
    y_fifth = lex.monomial((0, 5), Fraction(1))
    lex_sum = lex.add(x_cubed, y_fifth)
    assert [exponents for exponents, _ in lex_sum.terms] == [(0, 5), (3, 0)]

    x_cubed_g = grlex.monomial((3, 0), Fraction(1))
    y_fifth_g = grlex.monomial((0, 5), Fraction(1))
    grlex_sum = grlex.add(x_cubed_g, y_fifth_g)
    assert [exponents for exponents, _ in grlex_sum.terms] == [(3, 0), (0, 5)]

    grevlex = PolynomialRing((X, Y, SymbolId(3)), Q, MonomialOrder.GREVLEX)
    first = grevlex.monomial((1, 2, 0), Fraction(1))
    second = grevlex.monomial((2, 1, 0), Fraction(1))
    combined = grevlex.add(first, second)
    assert [exponents for exponents, _ in combined.terms] == [
        (1, 2, 0),
        (2, 1, 0),
    ]


def test_parent_options_must_match_the_ring_representation():
    from cas.algebra.parents import ParentRegistry, ParentSpec
    from cas.algebra.polynomial import MonomialOrder

    registry = ParentRegistry()
    grlex = PolynomialRing((X, Y), Q, MonomialOrder.GRLEX)
    spec = ParentSpec(
        "polynomial",
        base=ParentSpec("Q"),
        generators=(X, Y),
        options=(("monomial_order", "grlex"),),
    )
    parent = registry.intern(spec, grlex)
    assert parent.ring is grlex

    other = ParentRegistry()
    lex = PolynomialRing((X, Y), Q, MonomialOrder.LEX)
    with pytest.raises(ValueError, match="option"):
        other.intern(spec, lex)
