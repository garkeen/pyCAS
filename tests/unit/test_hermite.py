"""Hermite reduction: the repeated denominator becomes a derivative."""

from fractions import Fraction

import pytest

from cas.algebra.hermite import HermiteError, hermite_reduce
from cas.algebra.polynomial import UnivariatePolynomialRing
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)
Q = RationalField()
QX = UnivariatePolynomialRing(X, Q)
FIELD = RationalFunctionField(QX)


def x_polynomial(*coefficients: Fraction):
    return QX.sum(
        QX.monomial((index,), coefficient)
        for index, coefficient in enumerate(coefficients)
    )


def test_a_simple_repeated_pole_is_reduced():
    denominator = QX.pow(QX.generator(0), 2)
    value = FIELD.fraction(QX.one(), denominator)
    reduction = hermite_reduce(FIELD, value)
    expected = FIELD.fraction(
        QX.neg(QX.one()), QX.generator(0)
    )
    assert FIELD.equal(reduction.polynomial_part, expected)
    assert reduction.remainder.numerator.is_zero()
    assert FIELD.equal(
        FIELD.add(
            FIELD.derivative(reduction.polynomial_part),
            reduction.remainder,
        ),
        value,
    )


def test_a_mixed_squarefree_denominator_keeps_the_remainder():
    x = QX.generator(0)
    denominator = QX.mul(x, QX.pow(QX.add(x, QX.one()), 2))
    value = FIELD.fraction(QX.one(), denominator)
    reduction = hermite_reduce(FIELD, value)
    assert FIELD.equal(
        FIELD.add(
            FIELD.derivative(reduction.polynomial_part),
            reduction.remainder,
        ),
        value,
    )
    remainder_denominator = reduction.remainder.denominator
    assert QX.equal(
        QX.gcd(
            remainder_denominator,
            QX.derivative(remainder_denominator, 0),
        ),
        QX.one(),
    )


def test_a_squarefree_denominator_needs_no_reduction():
    x = QX.generator(0)
    denominator = QX.mul(x, QX.add(x, QX.one()))
    value = FIELD.fraction(QX.add(x, QX.one()), denominator)
    reduction = hermite_reduce(FIELD, value)
    assert reduction.polynomial_part.numerator.is_zero()
    assert FIELD.equal(reduction.remainder, value)


def test_random_reductions_preserve_the_original_fraction():
    import random

    rng = random.Random(20261105)
    for _ in range(30):
        numerator = x_polynomial(
            *[Fraction(rng.randint(-3, 3)) for _ in range(rng.randint(1, 4))]
        )
        factor = QX.add(QX.generator(0), QX.constant(Fraction(rng.randint(1, 3))))
        denominator = QX.mul(
            factor,
            QX.mul(
                QX.pow(
                    QX.add(QX.generator(0), QX.constant(Fraction(1))),
                    2,
                ),
                QX.add(QX.generator(0), QX.constant(Fraction(2))),
            ),
        )
        value = FIELD.fraction(numerator, denominator)
        reduction = hermite_reduce(FIELD, value)
        assert FIELD.equal(
            FIELD.add(
                FIELD.derivative(reduction.polynomial_part),
                reduction.remainder,
            ),
            value,
        )
        remainder_denominator = reduction.remainder.denominator
        assert QX.equal(
            QX.gcd(
                remainder_denominator,
                QX.derivative(remainder_denominator, 0),
            ),
            QX.one(),
        )


def test_positive_characteristic_is_refused():
    from cas.algebra.protocols import Field

    class PrimeField(Field[int]):
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
            return isinstance(value, int) and 0 <= value < self.prime

        def equal(self, left: int, right: int) -> bool:
            return left == right

        def inv(self, value: int) -> int:
            return pow(value, -1, self.prime)

        @property
        def characteristic(self) -> int:
            return self.prime

    ring = UnivariatePolynomialRing(X, PrimeField(5))
    field = RationalFunctionField(ring)
    value = field.fraction(ring.one(), ring.pow(ring.generator(0), 2))
    with pytest.raises(HermiteError, match="characteristic-zero"):
        hermite_reduce(field, value)
