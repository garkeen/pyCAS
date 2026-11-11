"""Prime fields and deterministic 64-bit Miller--Rabin primality."""

import itertools
import random

import pytest

from cas.algebra.finite_field import PrimeField, is_prime64
from cas.algebra.protocols import (
    DescribedRing,
    IntegerEmbedding,
    Ordered,
    RationalEmbedding,
)


def assert_field_laws(field: PrimeField, left: int, right: int, third: int) -> None:
    zero = field.zero()
    one = field.one()
    assert field.equal(field.add(left, right), field.add(right, left))
    assert field.equal(field.mul(left, right), field.mul(right, left))
    assert field.equal(
        field.add(field.add(left, right), third),
        field.add(left, field.add(right, third)),
    )
    assert field.equal(
        field.mul(field.mul(left, right), third),
        field.mul(left, field.mul(right, third)),
    )
    assert field.equal(
        field.mul(left, field.add(right, third)),
        field.add(field.mul(left, right), field.mul(left, third)),
    )
    assert field.equal(field.add(left, zero), left)
    assert field.equal(field.mul(left, one), left)
    assert field.equal(field.add(left, field.neg(left)), zero)
    assert field.equal(field.sub(left, right), field.add(left, field.neg(right)))
    if left != 0:
        assert field.equal(field.mul(left, field.inv(left)), one)


def test_prime_field_axioms_for_small_and_large_moduli():
    for modulus in (2, 3, 5):
        field = PrimeField(modulus)
        for left, right, third in itertools.product(range(modulus), repeat=3):
            assert_field_laws(field, left, right, third)
    field = PrimeField(65537)
    rng = random.Random(20261111)
    for _ in range(200):
        assert_field_laws(
            field,
            rng.randrange(65537),
            rng.randrange(65537),
            rng.randrange(65537),
        )
    assert_field_laws(field, 0, 1, 65536)
    assert_field_laws(field, 65536, 65536, 65536)


def test_prime_field_identities_and_inverse():
    field = PrimeField(65537)
    assert field.characteristic == 65537
    assert field.modulus == 65537
    assert field.zero() == 0
    assert field.one() == 1
    assert field.inv(1) == 1
    assert field.inv(65536) == 65536
    assert field.mul(12345, field.inv(12345)) == 1
    with pytest.raises(ZeroDivisionError):
        field.inv(0)
    assert PrimeField(2).inv(1) == 1
    large = PrimeField(2**61 - 1)
    assert large.characteristic == 2**61 - 1
    assert large.mul(2, large.inv(2)) == 1


def test_prime_field_contains_rejects_booleans_and_out_of_range_values():
    field = PrimeField(5)
    assert field.contains(0)
    assert field.contains(4)
    assert not field.contains(5)
    assert not field.contains(-1)
    assert not field.contains(True)
    assert not field.contains(False)
    assert not field.contains(1.0)
    assert not field.contains("1")
    with pytest.raises(ValueError):
        field.add(0, True)
    with pytest.raises(ValueError):
        field.equal(1, 5)


def test_prime_field_has_no_order_or_embedding_or_description():
    field = PrimeField(5)
    assert not isinstance(field, Ordered)
    assert not isinstance(field, IntegerEmbedding)
    assert not isinstance(field, RationalEmbedding)
    assert not isinstance(field, DescribedRing)


def test_prime_field_rejects_non_prime_moduli_and_bad_types():
    for modulus in (0, 1, 4, 9, 561, 2**64 - 1, 2**64):
        with pytest.raises(ValueError):
            PrimeField(modulus)
    with pytest.raises(TypeError):
        PrimeField(True)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        PrimeField(5.0)  # type: ignore[arg-type]


def test_is_prime64_accepts_known_primes():
    for value in (2, 3, 65537, 2**61 - 1, 18446744073709551557):
        assert is_prime64(value)


def test_is_prime64_rejects_known_composites_and_pseudoprimes():
    for value in (
        0,
        1,
        4,
        561,
        1105,
        1729,
        25326001,
        3215031751,
        2152302898747,
        3474749660383,
        341550071728321,
        3825123056546413051,
        2**64 - 1,
    ):
        assert not is_prime64(value)


def test_is_prime64_boundary_and_type_contract():
    with pytest.raises(ValueError):
        is_prime64(2**64)
    with pytest.raises(ValueError):
        is_prime64(2**64 + 1)
    with pytest.raises(TypeError):
        is_prime64(True)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        is_prime64(3.0)  # type: ignore[arg-type]
    assert not is_prime64(-17)
