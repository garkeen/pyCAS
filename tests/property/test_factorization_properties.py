"""Fixed-seed properties of Zassenhaus recombination and ``Q[x]`` factorization."""

import random
from fractions import Fraction

import pytest

from cas.algebra.factorization import (
    FactorizationBudget,
    FactorizationBudgetError,
    factor_polynomial_over_q,
    factor_primitive_integer,
    factorization_key,
)
from cas.algebra.integer_polynomial import (
    monic_rational_form,
    rational_polynomial_form,
)
from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import (
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

SEED = 20261112
X = SymbolId(1)

# Primitive positive-leading integer polynomials that are irreducible over Q.
# The quartic x^4 + x + 1 is irreducible modulo 2 and therefore over Q.
IRREDUCIBLE_FACTORS = (
    (1, 1),
    (-1, 1),
    (2, 1),
    (1, 2),
    (1, 0, 1),
    (2, 0, 1),
    (1, 1, 1),
    (1, 0, 2),
    (1, 0, 1, 1),
    (1, 1, 0, 0, 1),
)
SMALL_IRREDUCIBLE_FACTORS = IRREDUCIBLE_FACTORS[:8]


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


def rational_polynomial(
    ring: UnivariatePolynomialRing[Fraction],
    coefficients: tuple[Fraction, ...],
) -> Polynomial[Fraction]:
    return ring.sum(
        ring.monomial((index,), coefficient)
        for index, coefficient in enumerate(coefficients)
    )


def integer_product(
    ring: PolynomialRing[int],
    factors: tuple[Polynomial[int], ...],
) -> Polynomial[int]:
    product = ring.one()
    for factor in factors:
        product = ring.mul(product, factor)
    return product


def monic_integer_factor(
    ring_q: UnivariatePolynomialRing[Fraction],
    factor: Polynomial[int],
) -> Polynomial[Fraction]:
    embedded = rational_polynomial_form(ring_q, factor)
    return monic_rational_form(ring_q, embedded)


def assert_primitive_positive(
    ring: PolynomialRing[int],
    factor: Polynomial[int],
) -> None:
    assert factor.owner is ring
    assert not factor.is_zero()
    degree = ring.degree(factor, 0)
    assert degree >= 1
    assert ring.coefficients.is_one(ring.content(factor))
    assert ring.coefficient(factor, (degree,)) > 0


def assert_q_product(
    ring: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> None:
    result = factor_polynomial_over_q(ring, value)
    product = ring.one()
    keys: list[tuple[int, tuple[Fraction, ...]]] = []
    for factor, multiplicity in result.factors:
        assert factor.owner is ring
        degree = ring.degree(factor, 0)
        assert degree >= 1
        assert ring.coefficients.is_one(
            ring.coefficient(factor, (degree,))
        )
        keys.append(factorization_key(factor))
        product = ring.mul(product, ring.pow(factor, multiplicity))
    assert keys == sorted(keys)
    assert ring.equal(
        ring.mul(ring.constant(result.unit), product),
        value,
    )


def build_random_integer_value(
    rng: random.Random,
    ring: PolynomialRing[int],
    *,
    pool: tuple[tuple[int, ...], ...],
    max_degree: int,
    max_multiplicity: int = 2,
) -> tuple[
    Polynomial[int],
    tuple[tuple[int, ...], ...],
    tuple[int, ...],
]:
    while True:
        count = rng.randint(2, 3)
        chosen = tuple(rng.sample(pool, count))
        multiplicities = tuple(
            rng.randint(1, max_multiplicity) for _ in chosen
        )
        total_degree = sum(
            (len(coefficients) - 1) * multiplicity
            for coefficients, multiplicity in zip(
                chosen, multiplicities
            )
        )
        if total_degree <= max_degree:
            break
    value = ring.one()
    for coefficients, multiplicity in zip(chosen, multiplicities):
        factor = integer_polynomial(ring, coefficients)
        value = ring.mul(value, ring.pow(factor, multiplicity))
    return value, chosen, multiplicities


def test_known_irreducible_products_factor_completely():
    rng = random.Random(SEED)
    integer = integer_ring()
    rational = rational_ring()
    for _ in range(12):
        integer_value, chosen, multiplicities = build_random_integer_value(
            rng,
            integer,
            pool=IRREDUCIBLE_FACTORS,
            max_degree=10,
        )
        expected_unit = 1
        expected: dict[tuple[tuple[tuple[int, ...], Fraction], ...], int] = {}
        for coefficients, multiplicity in zip(chosen, multiplicities):
            factor = integer_polynomial(integer, coefficients)
            expected_unit *= (
                integer.coefficient(
                    factor, (len(coefficients) - 1,)
                )
                ** multiplicity
            )
            monic = monic_integer_factor(rational, factor)
            expected[monic.terms] = expected.get(monic.terms, 0) + multiplicity
        scale = Fraction(rng.randint(-4, 4), rng.randint(1, 4))
        if scale == 0:
            scale = Fraction(1)
        embedded = rational_polynomial_form(rational, integer_value)
        value = rational.mul(rational.constant(scale), embedded)
        result = factor_polynomial_over_q(rational, value)
        assert result.unit == scale * expected_unit
        actual = {
            factor.terms: multiplicity
            for factor, multiplicity in result.factors
        }
        assert actual == expected
        assert len(result.factors) == len(expected)
        assert_q_product(rational, value)
        for factor, _ in result.factors:
            repeated = factor_polynomial_over_q(rational, factor)
            assert repeated.unit == Fraction(1)
            assert len(repeated.factors) == 1
            assert repeated.factors[0][0].terms == factor.terms
            assert repeated.factors[0][1] == 1


def test_primitive_integer_products_reconstruct_and_refactor_to_themselves():
    rng = random.Random(SEED + 1)
    integer = integer_ring()
    for _ in range(14):
        value, chosen, _ = build_random_integer_value(
            rng,
            integer,
            pool=SMALL_IRREDUCIBLE_FACTORS,
            max_degree=6,
            max_multiplicity=1,
        )
        factors = factor_primitive_integer(integer, value)
        assert integer.equal(integer_product(integer, factors), value)
        assert len(factors) == len(chosen)
        keys = [factorization_key(factor) for factor in factors]
        assert keys == sorted(keys)
        for factor in factors:
            assert_primitive_positive(integer, factor)
            repeated = factor_primitive_integer(integer, factor)
            assert len(repeated) == 1
            assert repeated[0].terms == factor.terms


def test_q_factorization_is_scaling_invariant():
    rng = random.Random(SEED + 2)
    rational = rational_ring()
    for _ in range(8):
        integer_value, _, _ = build_random_integer_value(
            rng,
            integer_ring(),
            pool=IRREDUCIBLE_FACTORS,
            max_degree=8,
        )
        value = rational_polynomial_form(rational, integer_value)
        base = factor_polynomial_over_q(rational, value)
        for scale in (
            Fraction(-3, 5),
            Fraction(7, 2),
            Fraction(rng.randint(1, 5), 1),
        ):
            scaled = rational.mul(rational.constant(scale), value)
            result = factor_polynomial_over_q(rational, scaled)
            assert result.unit == scale * base.unit
            assert [
                (factor.terms, multiplicity)
                for factor, multiplicity in result.factors
            ] == [
                (factor.terms, multiplicity)
                for factor, multiplicity in base.factors
            ]
            assert_q_product(rational, scaled)


def test_zassenhaus_budget_exhaustion_has_no_partial_result():
    integer = integer_ring()
    integer_value = integer_polynomial(integer, (-1, 0, 1))
    for budget in (
        FactorizationBudget(max_recombination_tests=0),
        FactorizationBudget(max_prime_trials=0),
    ):
        with pytest.raises(FactorizationBudgetError):
            factor_primitive_integer(integer, integer_value, budget)
    rational = rational_ring()
    rational_value = rational_polynomial(
        rational, (Fraction(-1), Fraction(0), Fraction(1))
    )
    with pytest.raises(FactorizationBudgetError):
        factor_polynomial_over_q(
            rational,
            rational_value,
            FactorizationBudget(max_recombination_tests=0),
        )
