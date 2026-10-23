"""Q as an ordered field with explicit embeddings and a zero derivation."""

from fractions import Fraction

import pytest

from cas.algebra.protocols import (
    Derivation,
    Field,
    IntegerEmbedding,
    Ordered,
    RationalEmbedding,
    Ring,
)
from cas.algebra.rationals import RationalField

FIELD = RationalField()


def test_q_advertises_its_capabilities():
    assert isinstance(FIELD, Ring)
    assert isinstance(FIELD, Field)
    assert isinstance(FIELD, Ordered)
    assert isinstance(FIELD, IntegerEmbedding)
    assert isinstance(FIELD, RationalEmbedding)
    assert isinstance(FIELD, Derivation)


def test_ring_laws_on_sample_rationals():
    samples = [Fraction(-3, 2), Fraction(0), Fraction(2), Fraction(5, 3)]
    for left in samples:
        assert FIELD.equal(FIELD.add(left, FIELD.zero()), left)
        assert FIELD.equal(FIELD.mul(left, FIELD.one()), left)
        assert FIELD.equal(FIELD.add(left, FIELD.neg(left)), FIELD.zero())
        for right in samples:
            assert FIELD.equal(
                FIELD.add(left, right), FIELD.add(right, left)
            )
            assert FIELD.equal(
                FIELD.mul(left, right), FIELD.mul(right, left)
            )


def test_subtraction_and_powers():
    two_thirds = Fraction(2, 3)
    assert FIELD.sub(Fraction(1), two_thirds) == Fraction(1, 3)
    assert FIELD.pow(two_thirds, 0) == Fraction(1)
    assert FIELD.pow(two_thirds, 3) == Fraction(8, 27)
    with pytest.raises(ValueError):
        FIELD.pow(two_thirds, -1)


def test_integer_multiples_do_not_require_an_embedding():
    assert FIELD.mul_int(Fraction(2, 3), 3) == Fraction(2)
    assert FIELD.mul_int(Fraction(1, 2), -2) == Fraction(-1)
    assert FIELD.mul_int(Fraction(7, 5), 0) == Fraction(0)


def test_inverse_and_division():
    assert FIELD.equal(
        FIELD.mul(Fraction(3, 4), FIELD.inv(Fraction(3, 4))), FIELD.one()
    )
    assert FIELD.div(Fraction(1, 2), Fraction(3, 4)) == Fraction(2, 3)
    with pytest.raises(ZeroDivisionError):
        FIELD.inv(Fraction(0))
    with pytest.raises(ZeroDivisionError):
        FIELD.div(Fraction(1), Fraction(0))


def test_equality_and_zero_one_tests():
    assert FIELD.equal(Fraction(2, 4), Fraction(1, 2))
    assert FIELD.is_zero(Fraction(0))
    assert not FIELD.is_zero(Fraction(1, 3))
    assert FIELD.is_one(Fraction(5, 5))
    assert not FIELD.is_one(Fraction(2))


def test_order_is_exposed_through_sign():
    assert FIELD.sign(Fraction(-2)) == -1
    assert FIELD.sign(Fraction(0)) == 0
    assert FIELD.sign(Fraction(1, 7)) == 1
    assert FIELD.compare(Fraction(1, 2), Fraction(2, 3)) == -1
    assert FIELD.less(Fraction(1, 2), Fraction(2, 3))
    assert FIELD.less_equal(Fraction(2, 3), Fraction(2, 3))
    assert not FIELD.less(Fraction(2, 3), Fraction(2, 3))


def test_embeddings():
    assert FIELD.of_int(-3) == Fraction(-3)
    assert FIELD.of_rational(2, -4) == Fraction(-1, 2)
    assert FIELD.of_fraction(Fraction(3, 5)) == Fraction(3, 5)
    with pytest.raises(ZeroDivisionError):
        FIELD.of_rational(1, 0)


def test_q_is_a_constant_structure_for_the_chosen_derivation():
    assert FIELD.deriv(Fraction(7, 3)) == Fraction(0)
