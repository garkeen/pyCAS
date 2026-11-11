"""Deterministic Berlekamp factorization over prime fields."""

import pytest

from cas.algebra.finite_field import PrimeField
from cas.algebra.modular_factorization import (
    ModularBudget,
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


def factor_key(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> tuple[int, tuple[int, ...]]:
    degree = ring.degree(value, 0)
    return (
        degree,
        tuple(ring.coefficient(value, (index,)) for index in range(degree + 1)),
    )


def assert_complete_factorization(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
    expected_count: int,
    budget: ModularBudget = ModularBudget(),
) -> tuple[Polynomial[int], ...]:
    factors = factor_squarefree_mod_prime(ring, value, budget)
    assert len(factors) == expected_count
    product = ring.one()
    for factor in factors:
        assert not factor.is_zero()
        assert ring.degree(factor, 0) >= 1
        assert ring.coefficients.is_one(
            ring.coefficient(factor, (ring.degree(factor, 0),))
        )
        assert is_squarefree_mod_prime(ring, factor)
        assert is_irreducible_mod_prime(ring, factor)
        product = ring.mul(product, factor)
    assert ring.equal(product, value)
    assert list(factors) == sorted(factors, key=lambda item: factor_key(ring, item))
    return factors


def test_x_squared_minus_one_over_odd_primes():
    for modulus in (3, 5, 7):
        ring = prime_ring(modulus)
        value = prime_polynomial(ring, [-1, 0, 1])
        factors = assert_complete_factorization(ring, value, 2)
        assert [ring.degree(factor, 0) for factor in factors] == [1, 1]


def test_x_fourth_plus_one_over_odd_primes():
    for modulus in (3, 5, 7):
        ring = prime_ring(modulus)
        value = prime_polynomial(ring, [1, 0, 0, 0, 1])
        factors = assert_complete_factorization(ring, value, 2)
        assert [ring.degree(factor, 0) for factor in factors] == [2, 2]


def test_x_cubed_plus_x_plus_one():
    ring = prime_ring(2)
    value = prime_polynomial(ring, [1, 1, 0, 1])
    assert_complete_factorization(ring, value, 1)
    ring = prime_ring(3)
    value = prime_polynomial(ring, [1, 1, 0, 1])
    factors = assert_complete_factorization(ring, value, 2)
    assert sorted(ring.degree(factor, 0) for factor in factors) == [1, 2]
    for modulus in (5, 7):
        ring = prime_ring(modulus)
        value = prime_polynomial(ring, [1, 1, 0, 1])
        assert_complete_factorization(ring, value, 1)


@pytest.mark.parametrize(
    ("modulus", "coefficients", "count"),
    [
        (2, [0, 1, 0, 0, 1], 3),
        (3, [2, 0, 0, 0, 1], 3),
        (3, [2, 1, 0, 1, 1], 2),
        (5, [4, 1, 4, 3, 1], 3),
        (7, [2, 3, 3, 3, 1], 3),
    ],
)
def test_products_of_linear_and_quadratic_factors(modulus, coefficients, count):
    ring = prime_ring(modulus)
    value = prime_polynomial(ring, coefficients)
    assert_complete_factorization(ring, value, count)


def test_p2_is_fully_supported():
    ring = prime_ring(2)
    irreducible = prime_polynomial(ring, [1, 1, 1])
    factors = assert_complete_factorization(ring, irreducible, 1)
    assert ring.equal(factors[0], irreducible)
    squarefree_reducible = prime_polynomial(ring, [0, 1, 1])
    factors = assert_complete_factorization(ring, squarefree_reducible, 2)
    assert [factor_key(ring, factor)[1] for factor in factors] == [(0, 1), (1, 1)]
    with pytest.raises(ModularFactorizationError) as nonsquarefree:
        factor_squarefree_mod_prime(ring, prime_polynomial(ring, [1, 0, 1]))
    assert "squarefree_polynomial" in nonsquarefree.value.missing


def test_repeated_runs_have_the_same_deterministic_order():
    ring = prime_ring(5)
    value = prime_polynomial(ring, [1, 0, 0, 0, 1])
    first = factor_squarefree_mod_prime(ring, value)
    second = factor_squarefree_mod_prime(ring, value)
    assert len(first) == len(second)
    for left, right in zip(first, second):
        assert ring.equal(left, right)
    assert first == tuple(sorted(first, key=lambda item: factor_key(ring, item)))


def test_factor_order_is_degree_then_coefficients():
    ring = prime_ring(5)
    value = prime_polynomial(ring, [-1, 0, 1])
    factors = factor_squarefree_mod_prime(ring, value)
    assert factors[0].terms == (((0,), 1), ((1,), 1))
    assert factors[1].terms == (((0,), 4), ((1,), 1))


def test_budget_exhaustion_never_returns_partial_factors():
    ring = prime_ring(3)
    value = prime_polynomial(ring, [1, 0, 0, 0, 1])
    for budget in (
        ModularBudget(splitting=0, gcd=1000),
        ModularBudget(splitting=1000, gcd=0),
    ):
        with pytest.raises(ModularFactorizationError) as exhausted:
            factor_squarefree_mod_prime(ring, value, budget)
        assert "modular_factorization_budget" in exhausted.value.missing
        assert exhausted.value.detail
    ring = prime_ring(5)
    three_factors = prime_polynomial(ring, [4, 1, 4, 3, 1])
    with pytest.raises(ModularFactorizationError) as split_exhausted:
        factor_squarefree_mod_prime(
            ring,
            three_factors,
            ModularBudget(splitting=1, gcd=1000),
        )
    assert "modular_factorization_budget" in split_exhausted.value.missing


def test_modular_budget_validation():
    assert ModularBudget().splitting > 0
    assert ModularBudget().gcd > 0
    with pytest.raises(ValueError):
        ModularBudget(splitting=-1)
    with pytest.raises(ValueError):
        ModularBudget(gcd=-1)
    with pytest.raises(TypeError):
        ModularBudget(splitting=True)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        ModularBudget(gcd=2.0)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        factor_squarefree_mod_prime(
            prime_ring(3),
            prime_polynomial(prime_ring(3), [1, 0, 1]),
            None,  # type: ignore[arg-type]
        )


def test_structural_refusals():
    ring = prime_ring(3)
    with pytest.raises(ModularFactorizationError) as nonsquarefree:
        factor_squarefree_mod_prime(ring, prime_polynomial(ring, [1, 2, 1]))
    assert "squarefree_polynomial" in nonsquarefree.value.missing
    with pytest.raises(ModularFactorizationError) as nonmonic:
        factor_squarefree_mod_prime(ring, prime_polynomial(ring, [2, 2]))
    assert "monic_polynomial" in nonmonic.value.missing
    with pytest.raises(ModularFactorizationError) as zero:
        factor_squarefree_mod_prime(ring, ring.zero())
    assert "nonzero_polynomial" in zero.value.missing
    with pytest.raises(ModularFactorizationError) as constant:
        factor_squarefree_mod_prime(ring, ring.one())
    assert "nonconstant_polynomial" in constant.value.missing
    with pytest.raises(ModularFactorizationError) as foreign:
        factor_squarefree_mod_prime(ring, prime_ring(3).generator(0))
    assert "ring_ownership" in foreign.value.missing
    rational = UnivariatePolynomialRing(X, RationalField())
    with pytest.raises(ModularFactorizationError) as wrong_field:
        factor_squarefree_mod_prime(rational, rational.generator(0))
    assert "prime_field_coefficients" in wrong_field.value.missing
    with pytest.raises(ModularFactorizationError) as not_univariate:
        factor_squarefree_mod_prime(
            PolynomialRing((X,), PrimeField(3)),  # type: ignore[arg-type]
            PolynomialRing((X,), PrimeField(3)).generator(0),  # type: ignore[arg-type]
        )
    assert "univariate_polynomial_ring" in not_univariate.value.missing
