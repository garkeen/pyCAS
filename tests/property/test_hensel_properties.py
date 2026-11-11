"""Fixed-seed properties of Hensel lifting and witness construction."""

import random
from fractions import Fraction

from cas.algebra.factorization import (
    FactorizationBudget,
    hensel_lift_factorization,
    hensel_witness_for_radical,
)
from cas.algebra.finite_field import PrimeField, is_prime64
from cas.algebra.integer_polynomial import (
    coefficient_bound,
    congruent_mod,
    integer_primitive_form,
    rational_polynomial_form,
)
from cas.algebra.integers import IntegerRing
from cas.algebra.modular_factorization import factor_squarefree_mod_prime
from cas.algebra.modular_polynomial import (
    is_squarefree_mod_prime,
    reduce_mod_prime,
)
from cas.algebra.polynomial import (
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

SEED = 20261111
X = SymbolId(1)

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
PRIMITIVE_FACTORS = (
    (-1, 1),
    (1, 2),
    (-3, 1),
    (4, 1),
    (2, 1),
    (3, 2),
    (1, 0, 1),
    (2, 0, 1),
    (1, 1, 1),
)
MONIC_FACTORS = (
    (-1, 1),
    (2, 1),
    (-3, 1),
    (4, 1),
    (1, 0, 1),
    (2, 0, 1),
    (1, 1, 1),
)


def integer_ring() -> PolynomialRing[int]:
    return PolynomialRing((X,), IntegerRing())


def rational_ring() -> UnivariatePolynomialRing[Fraction]:
    return UnivariatePolynomialRing(X, RationalField())


def integer_polynomial(
    ring: PolynomialRing[int],
    coefficients: tuple[int, ...],
) -> Polynomial[int]:
    return ring.sum(
        ring.monomial((index,), coefficient)
        for index, coefficient in enumerate(coefficients)
    )


def build_product(
    ring: PolynomialRing[int],
    chosen: tuple[tuple[int, ...], ...],
) -> Polynomial[int]:
    result = ring.one()
    for coefficients in chosen:
        result = ring.mul(result, integer_polynomial(ring, coefficients))
    return result


def least_precision(prime: int, value: Polynomial[int]) -> int:
    bound = 2 * coefficient_bound(value)
    precision = 1
    while prime**precision <= bound:
        precision += 1
    return precision


def good_prime_and_factors(
    value: Polynomial[int],
    prime: int,
) -> tuple[UnivariatePolynomialRing[int], tuple[Polynomial[int], ...]]:
    ring = UnivariatePolynomialRing(X, PrimeField(prime))
    reduced = reduce_mod_prime(ring, value)
    degree = value.owner.degree(value, 0)
    assert ring.degree(reduced, 0) == degree
    leading = ring.coefficient(reduced, (degree,))
    normalized = ring.mul(
        ring.constant(ring.coefficients.inv(leading)), reduced
    )
    assert is_squarefree_mod_prime(ring, normalized)
    return ring, factor_squarefree_mod_prime(ring, normalized)


def select_prime(value: Polynomial[int]) -> int:
    degree = value.owner.degree(value, 0)
    leading = value.owner.coefficient(value, (degree,))
    for prime in PRIMES:
        if leading % prime == 0:
            continue
        ring = UnivariatePolynomialRing(X, PrimeField(prime))
        reduced = reduce_mod_prime(ring, value)
        if ring.degree(reduced, 0) != degree:
            continue
        lead = ring.coefficient(reduced, (degree,))
        normalized = ring.mul(
            ring.constant(ring.coefficients.inv(lead)), reduced
        )
        if is_squarefree_mod_prime(ring, normalized):
            return prime
    raise AssertionError("the sample range needs another good prime")


def assert_lift(
    value: Polynomial[int],
    prime: int,
    precision: int,
    lifted: tuple[Polynomial[int], ...],
) -> None:
    modulus = prime**precision
    source_owner = value.owner
    degree = source_owner.degree(value, 0)
    leading = source_owner.coefficient(value, (degree,))
    assert lifted
    owner = lifted[0].owner
    embedded = owner.sum(
        owner.monomial(exponents, coefficient)
        for exponents, coefficient in value.terms
    )
    product = owner.one()
    total_degree = 0
    for factor in lifted:
        assert factor.owner is owner
        factor_degree = owner.degree(factor, 0)
        assert factor_degree >= 1
        assert owner.coefficients.is_one(
            owner.coefficient(factor, (factor_degree,))
        )
        for _, coefficient in factor.terms:
            assert 0 <= coefficient < modulus
        product = owner.mul(product, factor)
        total_degree += factor_degree
    assert total_degree == degree
    assert congruent_mod(
        owner.mul(owner.constant(leading), product),
        embedded,
        modulus,
    )


def test_lift_reconstructs_random_products_of_coprime_factors():
    rng = random.Random(SEED)
    ring = integer_ring()
    for _ in range(20):
        count = rng.randint(2, 4)
        chosen = tuple(rng.sample(PRIMITIVE_FACTORS, count))
        value = build_product(ring, chosen)
        assert not value.is_zero()
        prime = select_prime(value)
        _, factors = good_prime_and_factors(value, prime)
        precision = least_precision(prime, value)
        lifted = hensel_lift_factorization(
            ring, value, prime, factors, precision
        )
        assert_lift(value, prime, precision, lifted)


def test_lift_precision_is_consistent_and_order_independent():
    rng = random.Random(SEED + 1)
    ring = integer_ring()
    for _ in range(8):
        chosen = tuple(rng.sample(PRIMITIVE_FACTORS, rng.randint(2, 3)))
        value = build_product(ring, chosen)
        prime = select_prime(value)
        _, factors = good_prime_and_factors(value, prime)
        precision = least_precision(prime, value)
        lower = hensel_lift_factorization(
            ring, value, prime, factors, precision
        )
        higher = hensel_lift_factorization(
            ring, value, prime, factors, precision + 1
        )
        assert_lift(value, prime, precision + 1, higher)
        for low, high in zip(lower, higher):
            assert congruent_mod(
                low,
                high,
                prime**precision,
            )
        reversed_lift = hensel_lift_factorization(
            ring, value, prime, factors[::-1], precision
        )
        assert {
            factor.terms for factor in reversed_lift
        } == {factor.terms for factor in lower}


def test_witness_reconstructs_random_monic_products():
    rng = random.Random(SEED + 2)
    integer = integer_ring()
    rational = rational_ring()
    budget = FactorizationBudget()
    for _ in range(16):
        count = rng.randint(2, 4)
        chosen = tuple(rng.sample(MONIC_FACTORS, count))
        radical_integer = build_product(integer, chosen)
        radical = rational_polynomial_form(rational, radical_integer)
        witness = hensel_witness_for_radical(rational, radical, budget)
        assert is_prime64(witness.prime)
        assert witness.precision >= 1
        form = integer_primitive_form(rational, radical)
        value = form.primitive
        assert_lift(
            value,
            witness.prime,
            witness.precision,
            witness.lifted,
        )
        bound = 2 * coefficient_bound(value)
        assert witness.prime**witness.precision > bound
        if witness.precision > 1:
            assert witness.prime ** (witness.precision - 1) <= bound
        assert witness.precision <= budget.max_hensel_precision
