"""Public algebra: pseudo-division, gcd/xgcd, content, squarefree, resultants."""

from fractions import Fraction

import pytest

from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import (
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.protocols import Field
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)
Y = SymbolId(2)
Q = RationalField()
Z = IntegerRing()
QX = UnivariatePolynomialRing(X, Q)
ZX = PolynomialRing((X,), Z)


def test_xgcd_over_a_field_returns_a_monic_gcd_and_bezout_coefficients():
    x = QX.generator(0)
    left = QX.sub(QX.pow(x, 2), QX.one())
    right = QX.sub(x, QX.one())
    gcd, left_coefficient, right_coefficient = QX.xgcd(left, right)
    assert QX.equal(gcd, right)
    assert QX.equal(
        QX.add(
            QX.mul(left_coefficient, left),
            QX.mul(right_coefficient, right),
        ),
        gcd,
    )


def test_xgcd_over_the_integers_is_normalised_nonnegative():
    gcd, left_coefficient, right_coefficient = Z.xgcd(12, 18)
    assert gcd == 6
    assert 12 * left_coefficient + 18 * right_coefficient == 6
    assert Z.xgcd(-12, 18)[0] == 6


def test_pseudo_division_over_z_uses_an_explicit_multiplier():
    x = ZX.generator(0)
    left = ZX.add(ZX.mul_int(ZX.pow(x, 2), 2), ZX.one())
    right = ZX.add(ZX.mul_int(x, 2), ZX.one())
    quotient, remainder, multiplier = ZX.pseudo_divmod(left, right)
    assert ZX.equal(
        ZX.mul(ZX.constant(multiplier), left),
        ZX.add(ZX.mul(quotient, right), remainder),
    )
    assert ZX.degree(remainder, 0) < ZX.degree(right, 0)
    with pytest.raises(ZeroDivisionError):
        ZX.pseudo_divmod(left, ZX.zero())


def test_pseudo_division_is_univariate_only():
    multivariate = PolynomialRing((X, Y), Q)
    with pytest.raises(ValueError):
        multivariate.pseudo_divmod(
            multivariate.generator(0), multivariate.generator(1)
        )


def test_exact_division_refuses_a_remainder():
    x = QX.generator(0)
    quotient = QX.exact_div(
        QX.sub(QX.pow(x, 2), QX.one()), QX.sub(x, QX.one())
    )
    assert QX.equal(quotient, QX.add(x, QX.one()))
    with pytest.raises(ValueError):
        QX.exact_div(QX.add(QX.pow(x, 2), QX.one()), QX.add(x, QX.one()))


def test_content_and_primitive_part_over_z():
    x = ZX.generator(0)
    value = ZX.add(
        ZX.mul_int(ZX.pow(x, 2), 6),
        ZX.add(ZX.mul_int(x, 9), ZX.constant(15)),
    )
    assert ZX.content(value) == 3
    primitive = ZX.primitive_part(value)
    assert ZX.equal(
        primitive,
        ZX.add(
            ZX.mul_int(ZX.pow(x, 2), 2),
            ZX.add(ZX.mul_int(x, 3), ZX.constant(5)),
        ),
    )
    assert ZX.content(ZX.zero()) == 0


def test_content_refuses_an_unsupported_coefficient_structure():
    inner = PolynomialRing((X,), Z)
    outer = PolynomialRing((Y,), inner)
    value = outer.constant(inner.generator(0))
    with pytest.raises(TypeError):
        outer.content(value)


def test_content_and_primitive_part_over_a_polynomial_coefficient_ring():
    from cas.algebra.protocols import ExactDivision

    assert isinstance(QX, ExactDivision)
    outer = PolynomialRing((Y,), QX)
    x = QX.generator(0)
    coefficient = QX.add(x, QX.one())
    value = outer.add(
        outer.mul(outer.constant(coefficient), outer.generator(0)),
        outer.constant(QX.mul_int(coefficient, 2)),
    )
    content = outer.content(value)
    assert QX.equal(content, coefficient)
    assert outer.equal(
        outer.primitive_part(value),
        outer.add(
            outer.generator(0),
            outer.constant(QX.constant(Fraction(2))),
        ),
    )


def test_squarefree_part_and_decomposition():
    x = QX.generator(0)
    value = QX.mul(
        QX.pow(QX.add(x, QX.one()), 2),
        QX.pow(QX.sub(x, QX.one()), 3),
    )
    part = QX.squarefree_part(value)
    assert QX.equal(
        part,
        QX.mul(QX.add(x, QX.one()), QX.sub(x, QX.one())),
    )
    unit, factors = QX.squarefree_decomposition(value)
    assert unit == 1
    assert {multiplicity for _, multiplicity in factors} == {2, 3}
    rebuilt = QX.constant(unit)
    for factor, multiplicity in factors:
        rebuilt = QX.mul(rebuilt, QX.pow(factor, multiplicity))
    assert QX.equal(rebuilt, value)
    for factor, _ in factors:
        assert QX.equal(
            QX.gcd(factor, QX.derivative(factor, 0)), QX.one()
        )


def test_resultant_and_discriminant():
    x = QX.generator(0)
    square_minus_one = QX.sub(QX.pow(x, 2), QX.one())
    x_minus_one = QX.sub(x, QX.one())
    assert QX.resultant(square_minus_one, x_minus_one) == 0
    circle = QX.add(QX.pow(x, 2), QX.one())
    line = QX.add(x, QX.one())
    assert QX.resultant(circle, line) == 2
    assert QX.discriminant(square_minus_one) == 4
    assert QX.discriminant(circle) == -4
    assert QX.resultant(QX.zero(), line) == 0


def test_subresultant_chain_ends_in_an_associate_of_the_gcd():
    x = QX.generator(0)
    circle = QX.add(QX.pow(x, 2), QX.one())
    line = QX.add(x, QX.one())
    chain = QX.subresultant_chain(circle, line)
    assert len(chain) == 3
    assert QX.equal(chain[0], circle)
    assert QX.equal(chain[1], line)
    assert QX.degree(chain[-1], 0) == 0
    repeated = QX.mul(
        QX.pow(QX.sub(x, QX.one()), 2), QX.add(x, QX.constant(Fraction(2)))
    )
    factor = QX.mul(QX.sub(x, QX.one()), QX.add(x, QX.constant(Fraction(2))))
    chain = QX.subresultant_chain(repeated, factor)
    assert QX.equal(QX.monic(chain[-1]), QX.gcd(repeated, factor))
    for previous, following in zip(chain, chain[1:]):
        assert QX.degree(previous, 0) > QX.degree(following, 0)


def test_subresultant_chain_allows_equal_degree_inputs():
    x = QX.generator(0)
    first = QX.add(
        QX.pow(x, 2),
        QX.add(QX.mul_int(x, 2), QX.constant(Fraction(3))),
    )
    second = QX.add(
        QX.mul_int(QX.pow(x, 2), 2),
        QX.add(x, QX.constant(Fraction(4))),
    )
    chain = QX.subresultant_chain(first, second)
    assert QX.degree(chain[0], 0) == QX.degree(chain[1], 0) == 2
    for previous, following in zip(chain[1:], chain[2:]):
        assert QX.degree(previous, 0) > QX.degree(following, 0)
    assert QX.equal(QX.monic(chain[-1]), QX.gcd(first, second))


def test_subresultant_chain_orders_inputs_and_handles_zero():
    x = QX.generator(0)
    line = QX.add(x, QX.one())
    quadratic = QX.add(QX.pow(x, 2), QX.one())
    chain = QX.subresultant_chain(line, quadratic)
    assert QX.equal(chain[0], quadratic)
    assert QX.equal(chain[1], line)
    assert QX.subresultant_chain(QX.zero(), line) == (line,)
    assert QX.subresultant_chain(line, QX.zero()) == (line,)


def test_polynomial_antiderivative_is_checked_by_differentiation():
    x = QX.generator(0)
    value = QX.add(
        QX.mul_int(QX.pow(x, 2), 3),
        QX.add(QX.mul_int(x, 2), QX.one()),
    )
    antiderivative = QX.antiderivative(value, 0)
    assert QX.equal(QX.derivative(antiderivative, 0), value)
    assert QX.coefficient(antiderivative, (0,)) == 0


class PrimeField(Field[int]):
    """A small prime field, used only to test characteristic dispatch."""

    def __init__(self, prime: int) -> None:
        self.prime = prime

    def zero(self) -> int:
        return 0

    def one(self) -> int:
        return 1

    def add(self, left: int, right: int) -> int:
        return (left + right) % self.prime

    def neg(self, value: int) -> int:
        return (-value) % self.prime

    def mul(self, left: int, right: int) -> int:
        return (left * right) % self.prime

    def contains(self, value: object) -> bool:
        return (
            isinstance(value, int)
            and not isinstance(value, bool)
            and 0 <= value < self.prime
        )

    def equal(self, left: int, right: int) -> bool:
        return left == right

    def inv(self, value: int) -> int:
        if value % self.prime == 0:
            raise ZeroDivisionError("zero has no inverse")
        return pow(value, -1, self.prime)

    @property
    def characteristic(self) -> int:
        return self.prime


def test_an_undeclared_characteristic_is_unknown_not_zero():
    base = UnivariatePolynomialRing(X, Q)
    coefficients = RationalFunctionField(base)
    ring = UnivariatePolynomialRing(X, coefficients)
    assert ring.characteristic == -1
    with pytest.raises(ValueError, match="characteristic-zero"):
        ring.squarefree_part(ring.generator(0))


def test_squarefree_operations_refuse_positive_characteristic():
    ring = UnivariatePolynomialRing(X, PrimeField(5))
    x = ring.generator(0)
    value = ring.add(ring.pow(x, 5), x)
    with pytest.raises(ValueError, match="characteristic-zero"):
        ring.squarefree_part(value)
    with pytest.raises(ValueError, match="characteristic-zero"):
        ring.squarefree_decomposition(value)
