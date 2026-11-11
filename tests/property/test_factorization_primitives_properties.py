"""Fixed-seed properties of finite fields and factorization primitives."""

import itertools
import random
from fractions import Fraction
from math import isqrt

from cas.algebra.finite_field import PrimeField
from cas.algebra.integer_polynomial import (
    coefficient_bound,
    integer_primitive_form,
    rational_polynomial_form,
)
from cas.algebra.integers import IntegerRing
from cas.algebra.modular_factorization import (
    ModularFactorizationError,
    factor_squarefree_mod_prime,
)
from cas.algebra.modular_polynomial import (
    is_irreducible_mod_prime,
    is_squarefree_mod_prime,
)
from cas.algebra.polynomial import Polynomial, PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

SEED = 20261111
X = SymbolId(1)


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


def random_monic(
    rng: random.Random,
    ring: UnivariatePolynomialRing[int],
    degree: int,
) -> Polynomial[int]:
    modulus = ring.coefficients.modulus
    return prime_polynomial(
        ring,
        [rng.randrange(modulus) for _ in range(degree)] + [1],
    )


def product(
    ring: UnivariatePolynomialRing[int],
    values: tuple[Polynomial[int], ...],
) -> Polynomial[int]:
    result = ring.one()
    for value in values:
        result = ring.mul(result, value)
    return result


def factor_key(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> tuple[int, tuple[int, ...]]:
    degree = ring.degree(value, 0)
    return (
        degree,
        tuple(ring.coefficient(value, (index,)) for index in range(degree + 1)),
    )


IRREDUCIBLES = {
    2: (
        [0, 1],
        [1, 1],
        [1, 1, 1],
        [1, 1, 0, 1],
        [1, 1, 0, 0, 1],
    ),
    3: (
        [0, 1],
        [1, 1],
        [2, 1],
        [1, 0, 1],
        [2, 1, 1],
        [1, 2, 0, 1],
    ),
    5: (
        [0, 1],
        [1, 1],
        [2, 1],
        [3, 0, 1],
        [1, 1, 1],
        [1, 1, 0, 1],
    ),
    7: (
        [0, 1],
        [1, 1],
        [2, 1],
        [1, 0, 1],
        [2, 0, 1],
        [1, 1, 0, 1],
    ),
}


def test_prime_field_laws():
    rng = random.Random(SEED)
    for modulus in (2, 3, 5, 7, 65537):
        field = PrimeField(modulus)
        for _ in range(60):
            left = rng.randrange(modulus)
            right = rng.randrange(modulus)
            third = rng.randrange(modulus)
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
            assert field.equal(field.add(left, field.zero()), left)
            assert field.equal(field.mul(left, field.one()), left)
            assert field.equal(field.add(left, field.neg(left)), field.zero())
            if left != 0:
                assert field.equal(field.mul(left, field.inv(left)), field.one())


def monic_polynomials(
    ring: UnivariatePolynomialRing[int],
    degree: int,
):
    modulus = ring.coefficients.modulus
    for coefficients in itertools.product(range(modulus), repeat=degree):
        yield prime_polynomial(ring, list(coefficients) + [1])


def naively_irreducible(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> bool:
    degree = ring.degree(value, 0)
    if degree <= 1:
        return True
    for divisor_degree in range(1, degree // 2 + 1):
        for divisor in monic_polynomials(ring, divisor_degree):
            _, remainder = ring.divmod(value, divisor)
            if remainder.is_zero():
                return False
    return True


def test_rabin_matches_naive_irreducibility_exhaustively_for_small_degrees():
    for modulus, maximum_degree in ((2, 6), (3, 5), (5, 4)):
        ring = prime_ring(modulus)
        for degree in range(2, maximum_degree + 1):
            for value in monic_polynomials(ring, degree):
                assert is_irreducible_mod_prime(ring, value) is naively_irreducible(
                    ring, value
                )


def naive_factorization(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> tuple[Polynomial[int], ...]:
    degree = ring.degree(value, 0)
    if degree <= 1:
        return (value,)
    for divisor_degree in range(1, degree):
        for divisor in monic_polynomials(ring, divisor_degree):
            quotient, remainder = ring.divmod(value, divisor)
            if remainder.is_zero():
                return tuple(
                    sorted(
                        naive_factorization(ring, divisor)
                        + naive_factorization(ring, quotient),
                        key=lambda item: factor_key(ring, item),
                    )
                )
    return (value,)


def test_berlekamp_matches_naive_factorization_exhaustively_for_small_degrees():
    for modulus, maximum_degree in ((2, 5), (3, 4), (5, 3)):
        ring = prime_ring(modulus)
        for degree in range(2, maximum_degree + 1):
            for value in monic_polynomials(ring, degree):
                if not is_squarefree_mod_prime(ring, value):
                    try:
                        factor_squarefree_mod_prime(ring, value)
                    except ModularFactorizationError:
                        continue
                    raise AssertionError("a non-squarefree value was factored")
                factors = factor_squarefree_mod_prime(ring, value)
                expected = naive_factorization(ring, value)
                assert len(factors) == len(expected)
                for actual, wanted in zip(factors, expected):
                    assert ring.equal(actual, wanted)


def test_berlekamp_factors_products_of_known_irreducibles():
    rng = random.Random(SEED + 1)
    for modulus, known in IRREDUCIBLES.items():
        ring = prime_ring(modulus)
        for _ in range(20):
            count = rng.randint(1, len(known))
            chosen = tuple(
                prime_polynomial(ring, coefficients)
                for coefficients in rng.sample(known, count)
            )
            value = product(ring, chosen)
            assert is_squarefree_mod_prime(ring, value)
            factors = factor_squarefree_mod_prime(ring, value)
            assert len(factors) == count
            assert ring.equal(product(ring, factors), value)
            assert list(factors) == sorted(
                factors, key=lambda item: factor_key(ring, item)
            )
            for factor in factors:
                assert is_irreducible_mod_prime(ring, factor)
            for index, factor in enumerate(factors):
                for other in factors[index + 1 :]:
                    assert not ring.equal(factor, other)


def test_berlekamp_factors_or_refuses_random_monic_polynomials():
    rng = random.Random(SEED + 2)
    for modulus in (2, 3, 5, 7):
        ring = prime_ring(modulus)
        for _ in range(12):
            value = random_monic(rng, ring, rng.randint(2, 5))
            if not is_squarefree_mod_prime(ring, value):
                try:
                    factor_squarefree_mod_prime(ring, value)
                except ModularFactorizationError as error:
                    assert "squarefree_polynomial" in error.missing
                else:
                    raise AssertionError("a non-squarefree value was factored")
                continue
            factors = factor_squarefree_mod_prime(ring, value)
            assert ring.equal(product(ring, factors), value)
            assert len(factors) >= 1
            for factor in factors:
                assert is_irreducible_mod_prime(ring, factor)
            assert list(factors) == sorted(
                factors, key=lambda item: factor_key(ring, item)
            )


def test_primitive_form_reconstructs_random_rational_polynomials():
    rng = random.Random(SEED + 3)
    ring_q = UnivariatePolynomialRing(X, RationalField())
    for _ in range(80):
        coefficients = [
            Fraction(rng.randint(-6, 6), rng.randint(1, 6))
            for _ in range(rng.randint(1, 6))
        ]
        value = ring_q.sum(
            ring_q.monomial((index,), coefficient)
            for index, coefficient in enumerate(coefficients)
        )
        if value.is_zero():
            continue
        form = integer_primitive_form(ring_q, value)
        owner = form.primitive.owner
        assert not form.primitive.is_zero()
        assert owner.coefficients.is_one(owner.content(form.primitive))
        assert owner.coefficient(
            form.primitive, (owner.degree(form.primitive, 0),)
        ) > 0
        embedded = rational_polynomial_form(ring_q, form.primitive)
        assert ring_q.equal(
            ring_q.mul(ring_q.constant(form.unit), embedded),
            value,
        )
        repeated = integer_primitive_form(ring_q, value)
        assert repeated == form


def test_coefficient_bound_dominates_random_known_factor_coefficients():
    rng = random.Random(SEED + 4)
    ring_z = PolynomialRing((X,), IntegerRing())
    for _ in range(80):
        size = rng.choice((100, 10**4, 10**6))
        left = ring_z.sum(
            ring_z.monomial((index,), rng.randint(-size, size))
            for index in range(rng.randint(1, 5))
        )
        right = ring_z.sum(
            ring_z.monomial((index,), rng.randint(-size, size))
            for index in range(rng.randint(1, 5))
        )
        if left.is_zero() or right.is_zero():
            continue
        value = ring_z.mul(left, right)
        bound = coefficient_bound(value)
        assert bound > 0
        for factor in (left, right):
            for _, coefficient in factor.terms:
                assert abs(coefficient) < bound
        assert bound == (1 << ring_z.degree(value, 0)) * (
            isqrt(
                sum(coefficient * coefficient for _, coefficient in value.terms)
            )
            + 1
        )
