"""Modular exponentiation, coefficient reduction, squarefree and Rabin tests."""

import random

import pytest

from cas.algebra.finite_field import PrimeField
from cas.algebra.integers import IntegerRing
from cas.algebra.modular_polynomial import (
    ModularPolynomialError,
    is_irreducible_mod_prime,
    is_squarefree_mod_prime,
    pow_mod,
    reduce_mod_prime,
)
from cas.algebra.polynomial import Polynomial, PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)
Y = SymbolId(2)


def prime_ring(modulus: int) -> UnivariatePolynomialRing[int]:
    return UnivariatePolynomialRing(X, PrimeField(modulus))


def prime_polynomial(
    ring: UnivariatePolynomialRing[int],
    coefficients: list[int],
) -> Polynomial[int]:
    modulus = ring.coefficients.modulus
    return ring.sum(
        ring.monomial((index,), coefficient % modulus)
        for index, coefficient in enumerate(coefficients)
    )


def integer_ring() -> PolynomialRing[int]:
    return PolynomialRing((X,), IntegerRing())


def naive_power(
    ring: UnivariatePolynomialRing[int],
    base: Polynomial[int],
    exponent: int,
    modulus: Polynomial[int],
) -> Polynomial[int]:
    result = ring.one()
    for _ in range(exponent):
        result = ring.divmod(ring.mul(result, base), modulus)[1]
    return result


def random_monic(
    rng: random.Random,
    ring: UnivariatePolynomialRing[int],
    degree: int,
) -> Polynomial[int]:
    modulus = ring.coefficients.modulus
    coefficients = [rng.randrange(modulus) for _ in range(degree)]
    coefficients.append(1)
    return prime_polynomial(ring, coefficients)


def test_pow_mod_matches_naive_repeated_multiplication():
    for modulus in (2, 3, 5, 7):
        ring = prime_ring(modulus)
        rng = random.Random(20261111 + modulus)
        for _ in range(20):
            degree = rng.randint(2, 4)
            divisor = random_monic(rng, ring, degree)
            base = prime_polynomial(
                ring,
                [rng.randrange(modulus) for _ in range(rng.randint(0, 3))],
            )
            for exponent in range(8):
                assert ring.equal(
                    pow_mod(ring, base, exponent, divisor),
                    naive_power(ring, base, exponent, divisor),
                )


def test_pow_mod_zero_exponent_and_constant_one_modulus():
    ring = prime_ring(5)
    x = ring.generator(0)
    assert ring.equal(pow_mod(ring, x, 0, ring.sub(ring.pow(x, 2), ring.one())), ring.one())
    assert ring.is_zero(pow_mod(ring, x, 5, ring.one()))


def test_pow_mod_structured_refusals():
    ring = prime_ring(5)
    x = ring.generator(0)
    with pytest.raises(ModularPolynomialError) as negative:
        pow_mod(ring, x, -1, ring.sub(ring.pow(x, 2), ring.one()))
    assert "nonnegative_exponent" in negative.value.missing
    with pytest.raises(ModularPolynomialError) as zero_modulus:
        pow_mod(ring, x, 2, ring.zero())
    assert "nonzero_modulus" in zero_modulus.value.missing
    with pytest.raises(ModularPolynomialError) as nonmonic:
        pow_mod(
            ring,
            x,
            2,
            ring.add(ring.mul(ring.constant(2), ring.pow(x, 2)), ring.one()),
        )
    assert "monic_modulus" in nonmonic.value.missing
    with pytest.raises(ModularPolynomialError) as foreign:
        pow_mod(ring, prime_ring(5).generator(0), 2, ring.sub(ring.pow(x, 2), ring.one()))
    assert "ring_ownership" in foreign.value.missing
    with pytest.raises(TypeError):
        pow_mod(ring, x, True, ring.sub(ring.pow(x, 2), ring.one()))  # type: ignore[arg-type]
    plain_ring = PolynomialRing((X,), PrimeField(5))
    with pytest.raises(ModularPolynomialError) as not_univariate:
        pow_mod(
            plain_ring,  # type: ignore[arg-type]
            plain_ring.generator(0),
            2,
            plain_ring.sub(plain_ring.pow(plain_ring.generator(0), 2), plain_ring.one()),
        )
    assert "univariate_polynomial_ring" in not_univariate.value.missing
    with pytest.raises(ModularPolynomialError) as rational:
        pow_mod(
            UnivariatePolynomialRing(X, RationalField()),
            UnivariatePolynomialRing(X, RationalField()).generator(0),
            2,
            UnivariatePolynomialRing(X, RationalField()).one(),
        )
    assert "prime_field_coefficients" in rational.value.missing


def test_reduce_mod_prime_reduces_integer_coefficients():
    target = prime_ring(5)
    source = integer_ring()
    value = source.sum(
        source.monomial((index,), coefficient)
        for index, coefficient in enumerate((-1, 7, 12))
    )
    reduced = reduce_mod_prime(target, value)
    assert reduced.terms == (((0,), 4), ((1,), 2), ((2,), 2))
    assert reduce_mod_prime(target, target.zero()).is_zero()
    already_reduced = target.generator(0)
    assert reduce_mod_prime(target, already_reduced) is already_reduced


def test_reduce_mod_prime_structured_refusals():
    target = prime_ring(5)
    with pytest.raises(ModularPolynomialError) as mismatch:
        reduce_mod_prime(
            UnivariatePolynomialRing(Y, PrimeField(5)),
            integer_ring().generator(0),
        )
    assert "matching_generators" in mismatch.value.missing
    rational_source = UnivariatePolynomialRing(X, RationalField())
    with pytest.raises(ModularPolynomialError) as noninteger:
        reduce_mod_prime(target, rational_source.one())
    assert "integer_coefficients" in noninteger.value.missing
    with pytest.raises(ModularPolynomialError) as rational_target:
        reduce_mod_prime(
            UnivariatePolynomialRing(X, RationalField()),
            integer_ring().one(),
        )
    assert "prime_field_coefficients" in rational_target.value.missing


def test_squarefree_predicate_over_several_prime_fields():
    ring = prime_ring(2)
    assert is_squarefree_mod_prime(ring, prime_polynomial(ring, [0, 1, 1]))
    assert not is_squarefree_mod_prime(ring, prime_polynomial(ring, [1, 0, 1]))
    assert not is_squarefree_mod_prime(ring, prime_polynomial(ring, [0, 0, 1]))
    ring = prime_ring(3)
    assert is_squarefree_mod_prime(ring, prime_polynomial(ring, [2, 0, 1]))
    assert not is_squarefree_mod_prime(ring, prime_polynomial(ring, [1, 2, 1]))
    ring = prime_ring(5)
    assert is_squarefree_mod_prime(
        ring,
        prime_polynomial(ring, [4, 1, 4, 3, 1]),
    )
    assert not is_squarefree_mod_prime(
        ring,
        prime_polynomial(ring, [1, 2, 1]),
    )


def test_squarefree_predicate_structured_refusals():
    ring = prime_ring(5)
    with pytest.raises(ModularPolynomialError) as zero:
        is_squarefree_mod_prime(ring, ring.zero())
    assert "nonzero_polynomial" in zero.value.missing
    with pytest.raises(ModularPolynomialError) as constant:
        is_squarefree_mod_prime(ring, ring.one())
    assert "nonconstant_polynomial" in constant.value.missing
    with pytest.raises(ModularPolynomialError) as nonmonic:
        is_squarefree_mod_prime(ring, prime_polynomial(ring, [1, 0, 2]))
    assert "monic_polynomial" in nonmonic.value.missing
    with pytest.raises(ModularPolynomialError) as foreign:
        is_squarefree_mod_prime(ring, prime_ring(5).generator(0))
    assert "ring_ownership" in foreign.value.missing


@pytest.mark.parametrize(
    ("coefficients", "expected"),
    [
        ([0, 1], True),
        ([1, 1], True),
        ([1, 1, 1], True),
        ([1, 0, 1], False),
        ([1, 1, 0, 1], True),
        ([1, 0, 1, 1], True),
        ([1, 1, 1, 1], False),
        ([1, 1, 0, 0, 1], True),
        ([1, 1, 1, 1, 1], True),
        ([1, 0, 1, 0, 1], False),
    ],
)
def test_rabin_irreducibility_over_f2(coefficients, expected):
    ring = prime_ring(2)
    assert is_irreducible_mod_prime(ring, prime_polynomial(ring, coefficients)) is expected


@pytest.mark.parametrize(
    ("coefficients", "expected"),
    [
        ([1, 0, 1], True),
        ([2, 1, 1], True),
        ([2, 0, 1], False),
        ([1, 2, 1], False),
        ([1, 2, 0, 1], True),
        ([1, 1, 0, 1], False),
        ([1, 0, 0, 0, 1], False),
    ],
)
def test_rabin_irreducibility_over_f3(coefficients, expected):
    ring = prime_ring(3)
    assert is_irreducible_mod_prime(ring, prime_polynomial(ring, coefficients)) is expected


@pytest.mark.parametrize(
    ("coefficients", "expected"),
    [
        ([3, 0, 1], True),
        ([1, 0, 1], False),
        ([1, 1, 1], True),
        ([1, 0, 0, 0, 1], False),
        ([1, 1, 0, 1], True),
        ([2, 0, 0, 1], False),
    ],
)
def test_rabin_irreducibility_over_f5(coefficients, expected):
    ring = prime_ring(5)
    assert is_irreducible_mod_prime(ring, prime_polynomial(ring, coefficients)) is expected


def test_rabin_non_squarefree_is_reducible_and_structural_refusals():
    ring = prime_ring(3)
    assert not is_irreducible_mod_prime(ring, prime_polynomial(ring, [1, 2, 1]))
    for characteristics in (
        lambda: is_irreducible_mod_prime(ring, ring.zero()),
        lambda: is_irreducible_mod_prime(ring, ring.one()),
        lambda: is_irreducible_mod_prime(
            ring, prime_polynomial(ring, [1, 0, 2])
        ),
        lambda: is_irreducible_mod_prime(ring, prime_ring(3).generator(0)),
    ):
        with pytest.raises(ModularPolynomialError) as refusal:
            characteristics()
        assert refusal.value.detail
        assert refusal.value.missing
    rational = UnivariatePolynomialRing(X, RationalField())
    with pytest.raises(ModularPolynomialError) as wrong_field:
        is_irreducible_mod_prime(rational, rational.generator(0))
    assert "prime_field_coefficients" in wrong_field.value.missing
