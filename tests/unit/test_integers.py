"""Z as a Euclidean ordered ring, explicitly not a field."""

import pytest

from cas.algebra.integers import IntegerRing
from cas.algebra.protocols import (
    Derivation,
    Euclidean,
    Field,
    IntegerEmbedding,
    Ordered,
)
from cas.algebra.rationals import RationalField

RING = IntegerRing()


def test_z_advertises_euclidean_order_but_not_field():
    assert isinstance(RING, Euclidean)
    assert isinstance(RING, Ordered)
    assert isinstance(RING, IntegerEmbedding)
    assert isinstance(RING, Derivation)
    assert not isinstance(RING, Field)
    assert not isinstance(RationalField(), Euclidean)


def test_arithmetic_and_powers():
    assert RING.add(2, -5) == -3
    assert RING.mul(-4, 3) == -12
    assert RING.pow(2, 10) == 1024
    assert RING.pow(0, 0) == 1
    with pytest.raises(ValueError):
        RING.pow(2, -1)


def test_division_identity_for_all_signs():
    for left in (-7, -1, 0, 1, 7):
        for right in (3, -3):
            quotient, remainder = RING.divmod(left, right)
            assert right * quotient + remainder == left
            assert abs(remainder) < abs(right)
    with pytest.raises(ZeroDivisionError):
        RING.divmod(1, 0)


def test_gcd_is_nonnegative_and_handles_zero():
    assert RING.gcd(-12, 8) == 4
    assert RING.gcd(12, -8) == 4
    assert RING.gcd(0, -5) == 5
    assert RING.gcd(0, 0) == 0


def test_order_and_embedding():
    assert RING.sign(-2) == -1
    assert RING.sign(0) == 0
    assert RING.sign(9) == 1
    assert RING.compare(3, 8) == -1
    assert RING.less(8, 3) is False
    assert RING.less_equal(3, 3) is True
    assert RING.of_int(4) == 4


def test_z_carries_the_zero_derivation_explicitly():
    assert RING.deriv(123) == 0
