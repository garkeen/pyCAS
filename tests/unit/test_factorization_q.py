"""Zassenhaus recombination and low-level ``Q[x]`` factorization."""

from fractions import Fraction

import pytest

from cas.algebra.factorization import (
    Factorization,
    FactorizationBudget,
    FactorizationBudgetError,
    FactorizationFragmentError,
    factor_polynomial_over_q,
    factor_primitive_integer,
    factorization_key,
)
from cas.algebra.finite_field import PrimeField
from cas.algebra.integers import IntegerRing
from cas.algebra.modular_factorization import (
    ModularBudget,
    factor_squarefree_mod_prime,
)
from cas.algebra.modular_polynomial import reduce_mod_prime
from cas.algebra.polynomial import (
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)


def integer_ring() -> PolynomialRing[int]:
    return PolynomialRing((X,), IntegerRing())


def rational_ring() -> UnivariatePolynomialRing[Fraction]:
    return UnivariatePolynomialRing(X, RationalField())


def integer_polynomial(
    ring: PolynomialRing[int],
    coefficients: list[int],
) -> Polynomial[int]:
    return ring.sum(
        ring.monomial((index,), coefficient)
        for index, coefficient in enumerate(coefficients)
    )


def rational_polynomial(
    ring: UnivariatePolynomialRing[Fraction],
    coefficients: list[Fraction],
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


def assert_primitive_positive(
    ring: PolynomialRing[int],
    factor: Polynomial[int],
) -> None:
    assert factor.owner is ring
    assert not factor.is_zero()
    assert ring.degree(factor, 0) >= 1
    assert ring.coefficients.is_one(ring.content(factor))
    degree = ring.degree(factor, 0)
    assert ring.coefficient(factor, (degree,)) > 0


def assert_factorization(
    ring: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
    result: Factorization,
) -> None:
    product = ring.one()
    keys: list[tuple[int, tuple[Fraction, ...]]] = []
    for factor, multiplicity in result.factors:
        assert factor.owner is ring
        assert not factor.is_zero()
        degree = ring.degree(factor, 0)
        assert degree >= 1
        assert ring.coefficients.is_one(
            ring.coefficient(factor, (degree,))
        )
        assert isinstance(multiplicity, int)
        assert multiplicity >= 1
        keys.append(factorization_key(factor))
        product = ring.mul(product, ring.pow(factor, multiplicity))
    assert keys == sorted(keys)
    assert ring.equal(
        ring.mul(ring.constant(result.unit), product),
        value,
    )


def test_factor_primitive_integer_splits_difference_of_squares():
    ring = integer_ring()
    value = integer_polynomial(ring, [-1, 0, 1])
    factors = factor_primitive_integer(ring, value)
    assert [factor.terms for factor in factors] == [
        (((0,), -1), ((1,), 1)),
        (((0,), 1), ((1,), 1)),
    ]
    assert ring.equal(integer_product(ring, factors), value)
    for factor in factors:
        assert_primitive_positive(ring, factor)


def test_factor_primitive_integer_returns_irreducible_x_fourth_plus_one():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 0, 0, 0, 1])
    # The search is not trivial: x^4 + 1 splits into two quadratics modulo 3.
    prime_ring = UnivariatePolynomialRing(X, PrimeField(3))
    reduced = reduce_mod_prime(prime_ring, value)
    modular_factors = factor_squarefree_mod_prime(prime_ring, reduced)
    assert [prime_ring.degree(factor, 0) for factor in modular_factors] == [
        2,
        2,
    ]
    factors = factor_primitive_integer(ring, value)
    assert len(factors) == 1
    assert factors[0].terms == value.terms
    assert ring.equal(factors[0], value)


def test_factor_primitive_integer_recombines_three_factors():
    ring = integer_ring()
    generator = ring.generator(0)
    value = ring.mul(
        ring.mul(
            ring.sub(generator, ring.one()),
            ring.add(generator, ring.one()),
        ),
        ring.add(ring.mul(generator, generator), ring.one()),
    )
    factors = factor_primitive_integer(ring, value)
    assert [factor.terms for factor in factors] == [
        (((0,), -1), ((1,), 1)),
        (((0,), 1), ((1,), 1)),
        (((0,), 1), ((2,), 1)),
    ]
    assert ring.equal(integer_product(ring, factors), value)
    for factor in factors:
        assert_primitive_positive(ring, factor)


def test_factor_primitive_integer_recombines_different_leading_divisors():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 5, 6])
    factors = factor_primitive_integer(ring, value)
    assert [factor.terms for factor in factors] == [
        (((0,), 1), ((1,), 2)),
        (((0,), 1), ((1,), 3)),
    ]
    assert ring.equal(
        ring.mul(factors[0], factors[1]),
        value,
    )


def test_factor_primitive_integer_recombines_equal_degree_factors():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 0, 3, 0, 2])
    factors = factor_primitive_integer(ring, value)
    assert [factor.terms for factor in factors] == [
        (((0,), 1), ((2,), 1)),
        (((0,), 1), ((2,), 2)),
    ]
    assert ring.equal(integer_product(ring, factors), value)


def test_factor_primitive_integer_finds_small_factor_when_large_exceeds_half():
    ring = integer_ring()
    generator = ring.generator(0)
    large = ring.add(
        ring.add(
            ring.mul(ring.mul(generator, generator), generator),
            ring.one(),
        ),
        generator,
    )
    value = ring.mul(ring.add(generator, ring.one()), large)
    assert ring.degree(value, 0) == 4
    factors = factor_primitive_integer(ring, value)
    assert [ring.degree(factor, 0) for factor in factors] == [1, 3]
    assert factors[0].terms == (((0,), 1), ((1,), 1))
    assert ring.equal(factors[1], large)
    assert ring.equal(integer_product(ring, factors), value)


def test_factor_primitive_integer_supports_characteristic_two():
    ring = integer_ring()
    value = integer_polynomial(ring, [2, 3, 1])
    factors = factor_primitive_integer(ring, value)
    assert [factor.terms for factor in factors] == [
        (((0,), 1), ((1,), 1)),
        (((0,), 2), ((1,), 1)),
    ]
    assert ring.equal(integer_product(ring, factors), value)


def test_factor_primitive_integer_handles_large_coefficients():
    ring = integer_ring()
    generator = ring.generator(0)
    small = ring.sub(generator, ring.constant(1_000_003))
    large = ring.add(generator, ring.constant(1_000_003))
    value = ring.mul(small, large)
    factors = factor_primitive_integer(ring, value)
    assert [factor.terms for factor in factors] == [
        (((0,), -1_000_003), ((1,), 1)),
        (((0,), 1_000_003), ((1,), 1)),
    ]
    assert ring.equal(integer_product(ring, factors), value)


def test_factor_primitive_integer_refuses_invalid_inputs():
    ring = integer_ring()
    with pytest.raises(FactorizationFragmentError) as zero:
        factor_primitive_integer(ring, ring.zero())
    assert "nonzero_polynomial" in zero.value.missing
    with pytest.raises(FactorizationFragmentError) as constant:
        factor_primitive_integer(ring, integer_polynomial(ring, [7]))
    assert "nonconstant_polynomial" in constant.value.missing
    with pytest.raises(FactorizationFragmentError) as negative:
        factor_primitive_integer(ring, integer_polynomial(ring, [-1, -1]))
    assert "positive_leading_coefficient" in negative.value.missing
    with pytest.raises(FactorizationFragmentError) as nonprimitive:
        factor_primitive_integer(ring, integer_polynomial(ring, [2, 0, 2]))
    assert "primitive_polynomial" in nonprimitive.value.missing
    with pytest.raises(FactorizationFragmentError) as nonsquarefree:
        factor_primitive_integer(ring, integer_polynomial(ring, [1, 2, 1]))
    assert "squarefree_polynomial" in nonsquarefree.value.missing
    foreign = integer_polynomial(integer_ring(), [-1, 0, 1])
    with pytest.raises(FactorizationFragmentError) as other_ring:
        factor_primitive_integer(ring, foreign)
    assert "ring_ownership" in other_ring.value.missing
    with pytest.raises(TypeError):
        factor_primitive_integer(
            rational_ring(),  # type: ignore[arg-type]
            rational_polynomial(
                rational_ring(), [Fraction(-1), Fraction(0), Fraction(1)]
            ),
        )
    with pytest.raises(TypeError):
        factor_primitive_integer(
            ring,
            integer_polynomial(ring, [-1, 0, 1]),
            None,  # type: ignore[arg-type]
        )


def test_factor_primitive_integer_tries_next_prime_when_precision_is_limited():
    ring = integer_ring()
    value = integer_polynomial(ring, [-1, 0, 1])
    factors = factor_primitive_integer(
        ring,
        value,
        FactorizationBudget(max_hensel_precision=2),
    )
    assert [factor.terms for factor in factors] == [
        (((0,), -1), ((1,), 1)),
        (((0,), 1), ((1,), 1)),
    ]
    assert ring.equal(integer_product(ring, factors), value)


def test_factor_primitive_integer_budget_exhaustion_returns_no_partial():
    ring = integer_ring()
    value = integer_polynomial(ring, [-1, 0, 1])
    with pytest.raises(FactorizationBudgetError) as recombination:
        factor_primitive_integer(
            ring,
            value,
            FactorizationBudget(max_recombination_tests=0),
        )
    assert "factorization_budget" in recombination.value.missing
    with pytest.raises(FactorizationBudgetError) as primes:
        factor_primitive_integer(
            ring,
            value,
            FactorizationBudget(max_prime_trials=0),
        )
    assert "factorization_budget" in primes.value.missing
    with pytest.raises(FactorizationBudgetError) as precision:
        factor_primitive_integer(
            ring,
            value,
            FactorizationBudget(max_hensel_precision=0),
        )
    assert "hensel_precision" in precision.value.missing
    with pytest.raises(FactorizationBudgetError) as modular:
        factor_primitive_integer(
            ring,
            value,
            FactorizationBudget(
                modular=ModularBudget(splitting=0, gcd=1 << 10)
            ),
        )
    assert "factorization_budget" in modular.value.missing


def test_factor_polynomial_over_q_splits_difference_of_squares():
    ring = rational_ring()
    value = rational_polynomial(
        ring, [Fraction(-1), Fraction(0), Fraction(1)]
    )
    result = factor_polynomial_over_q(ring, value)
    assert result.unit == Fraction(1)
    assert [
        (factor.terms, multiplicity)
        for factor, multiplicity in result.factors
    ] == [
        ((((0,), Fraction(-1)), ((1,), Fraction(1))), 1),
        ((((0,), Fraction(1)), ((1,), Fraction(1))), 1),
    ]
    assert_factorization(ring, value, result)


def test_factor_polynomial_over_q_returns_irreducible_x_fourth_plus_one():
    ring = rational_ring()
    value = rational_polynomial(
        ring,
        [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(1)],
    )
    result = factor_polynomial_over_q(ring, value)
    assert result.unit == Fraction(1)
    assert len(result.factors) == 1
    assert result.factors[0][0].terms == value.terms
    assert result.factors[0][1] == 1
    assert_factorization(ring, value, result)


def test_factor_polynomial_over_q_handles_nonmonic_integer_value():
    ring = rational_ring()
    value = rational_polynomial(
        ring, [Fraction(1), Fraction(5), Fraction(6)]
    )
    result = factor_polynomial_over_q(ring, value)
    assert result.unit == Fraction(6)
    assert [
        (factor.terms, multiplicity)
        for factor, multiplicity in result.factors
    ] == [
        (
            (
                ((0,), Fraction(1, 3)),
                ((1,), Fraction(1)),
            ),
            1,
        ),
        (
            (
                ((0,), Fraction(1, 2)),
                ((1,), Fraction(1)),
            ),
            1,
        ),
    ]
    assert_factorization(ring, value, result)


def test_factor_polynomial_over_q_handles_linear_value():
    ring = rational_ring()
    value = rational_polynomial(ring, [Fraction(1), Fraction(2)])
    result = factor_polynomial_over_q(ring, value)
    assert result.unit == Fraction(2)
    assert len(result.factors) == 1
    factor, multiplicity = result.factors[0]
    assert multiplicity == 1
    assert factor.terms == (
        ((0,), Fraction(1, 2)),
        ((1,), Fraction(1)),
    )
    assert_factorization(ring, value, result)


def test_factor_polynomial_over_q_handles_negative_leading_coefficient():
    ring = rational_ring()
    value = rational_polynomial(
        ring, [Fraction(1), Fraction(0), Fraction(-1)]
    )
    result = factor_polynomial_over_q(ring, value)
    assert result.unit == Fraction(-1)
    assert [
        factor.terms for factor, _ in result.factors
    ] == [
        (((0,), Fraction(-1)), ((1,), Fraction(1))),
        (((0,), Fraction(1)), ((1,), Fraction(1))),
    ]
    assert_factorization(ring, value, result)


def test_factor_polynomial_over_q_handles_constants():
    ring = rational_ring()
    for coefficient in (Fraction(5), Fraction(-3, 4), Fraction(1, 7)):
        value = ring.constant(coefficient)
        result = factor_polynomial_over_q(ring, value)
        assert result.unit == coefficient
        assert result.factors == ()


def test_factor_polynomial_over_q_refuses_zero():
    ring = rational_ring()
    with pytest.raises(FactorizationFragmentError) as zero:
        factor_polynomial_over_q(ring, ring.zero())
    assert "nonzero_polynomial" in zero.value.missing


def test_factor_polynomial_over_q_keeps_repeated_factor_multiplicities():
    ring = rational_ring()
    generator = ring.generator(0)
    minus = ring.sub(generator, ring.one())
    plus = ring.add(generator, ring.one())
    value = ring.mul(
        ring.mul(minus, minus),
        ring.mul(ring.mul(plus, plus), plus),
    )
    result = factor_polynomial_over_q(ring, value)
    assert result.unit == Fraction(1)
    assert [
        (factor.terms, multiplicity)
        for factor, multiplicity in result.factors
    ] == [
        ((((0,), Fraction(-1)), ((1,), Fraction(1))), 2),
        ((((0,), Fraction(1)), ((1,), Fraction(1))), 3),
    ]
    assert_factorization(ring, value, result)


def test_factor_polynomial_over_q_handles_rational_coefficients():
    ring = rational_ring()
    value = rational_polynomial(
        ring,
        [Fraction(-1, 2), Fraction(0), Fraction(1, 2)],
    )
    result = factor_polynomial_over_q(ring, value)
    assert result.unit == Fraction(1, 2)
    assert [
        factor.terms for factor, _ in result.factors
    ] == [
        (((0,), Fraction(-1)), ((1,), Fraction(1))),
        (((0,), Fraction(1)), ((1,), Fraction(1))),
    ]
    assert_factorization(ring, value, result)
    positive = rational_polynomial(
        ring,
        [Fraction(2, 3), Fraction(0), Fraction(2, 3)],
    )
    positive_result = factor_polynomial_over_q(ring, positive)
    assert positive_result.unit == Fraction(2, 3)
    assert len(positive_result.factors) == 1
    assert positive_result.factors[0][0].terms == (
        ((0,), Fraction(1)),
        ((2,), Fraction(1)),
    )
    assert_factorization(ring, positive, positive_result)


def test_factor_polynomial_over_q_is_idempotent_on_its_factors():
    ring = rational_ring()
    values = (
        rational_polynomial(ring, [Fraction(-1), Fraction(0), Fraction(1)]),
        rational_polynomial(ring, [Fraction(1), Fraction(5), Fraction(6)]),
        rational_polynomial(
            ring, [Fraction(2), Fraction(0), Fraction(3), Fraction(0), Fraction(1)]
        ),
    )
    for value in values:
        result = factor_polynomial_over_q(ring, value)
        for factor, _ in result.factors:
            repeated = factor_polynomial_over_q(ring, factor)
            assert repeated.unit == Fraction(1)
            assert len(repeated.factors) == 1
            assert repeated.factors[0][0].terms == factor.terms
            assert repeated.factors[0][1] == 1


def test_factor_polynomial_over_q_scales_its_unit():
    ring = rational_ring()
    value = rational_polynomial(
        ring, [Fraction(1), Fraction(5), Fraction(6)]
    )
    base = factor_polynomial_over_q(ring, value)
    for scale in (Fraction(-3, 5), Fraction(7, 2)):
        scaled = ring.mul(ring.constant(scale), value)
        result = factor_polynomial_over_q(ring, scaled)
        assert result.unit == scale * base.unit
        assert [
            (factor.terms, multiplicity)
            for factor, multiplicity in result.factors
        ] == [
            (factor.terms, multiplicity)
            for factor, multiplicity in base.factors
        ]
        assert_factorization(ring, scaled, result)


def test_factor_polynomial_over_q_refuses_foreign_and_nonpolynomial_input():
    ring = rational_ring()
    foreign = rational_polynomial(
        rational_ring(), [Fraction(-1), Fraction(0), Fraction(1)]
    )
    with pytest.raises(FactorizationFragmentError) as other_ring:
        factor_polynomial_over_q(ring, foreign)
    assert "ring_ownership" in other_ring.value.missing
    with pytest.raises(FactorizationFragmentError) as nonpolynomial:
        factor_polynomial_over_q(ring, object())  # type: ignore[arg-type]
    assert "ring_ownership" in nonpolynomial.value.missing
    with pytest.raises(TypeError):
        factor_polynomial_over_q(
            integer_ring(),  # type: ignore[arg-type]
            rational_polynomial(
                ring, [Fraction(-1), Fraction(0), Fraction(1)]
            ),
        )


def test_factorization_record_validation():
    ring = rational_ring()
    generator = ring.generator(0)
    linear = ring.add(generator, ring.one())
    other_linear = ring.sub(generator, ring.one())
    constant = ring.constant(Fraction(2))
    nonmonic = ring.mul(ring.constant(Fraction(2)), linear)
    record = Factorization(
        unit=Fraction(3, 2),
        factors=((linear, 2), (other_linear, 1)),
    )
    assert record.unit == Fraction(3, 2)
    assert len(record.factors) == 2
    assert Factorization(unit=Fraction(1), factors=()).factors == ()
    with pytest.raises(ValueError):
        Factorization(unit=Fraction(0), factors=())
    with pytest.raises(TypeError):
        Factorization(unit=1, factors=())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Factorization(unit=Fraction(1), factors=[])  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Factorization(  # type: ignore[arg-type]
            unit=Fraction(1), factors=((linear,),)
        )
    with pytest.raises(TypeError):
        Factorization(  # type: ignore[arg-type]
            unit=Fraction(1), factors=((3, 1),)
        )
    with pytest.raises(TypeError):
        Factorization(  # type: ignore[arg-type]
            unit=Fraction(1), factors=((linear, True),)
        )
    with pytest.raises(TypeError):
        Factorization(  # type: ignore[arg-type]
            unit=Fraction(1), factors=((linear, 1.5),)
        )
    with pytest.raises(ValueError):
        Factorization(unit=Fraction(1), factors=((linear, 0),))
    with pytest.raises(ValueError):
        Factorization(unit=Fraction(1), factors=((linear, -1),))
    with pytest.raises(ValueError):
        Factorization(unit=Fraction(1), factors=((constant, 1),))
    with pytest.raises(ValueError):
        Factorization(unit=Fraction(1), factors=((ring.zero(), 1),))
    with pytest.raises(ValueError):
        Factorization(unit=Fraction(1), factors=((nonmonic, 1),))
    with pytest.raises(ValueError):
        Factorization(
            unit=Fraction(1),
            factors=((linear, 1), (linear, 2)),
        )
    with pytest.raises(ValueError):
        Factorization(
            unit=Fraction(1),
            factors=((linear, 1), (other_linear, 0)),
        )
    mixed_ring = rational_ring()
    mixed = mixed_ring.add(mixed_ring.generator(0), mixed_ring.one())
    with pytest.raises(ValueError):
        Factorization(
            unit=Fraction(1),
            factors=((linear, 1), (mixed, 1)),
        )
    integer = integer_ring()
    integer_factor = integer_polynomial(integer, [1, 1])
    with pytest.raises(TypeError):
        Factorization(  # type: ignore[arg-type]
            unit=Fraction(1), factors=((integer_factor, 1),)
        )


def test_factorization_key_is_degree_then_coefficients():
    ring = rational_ring()
    generator = ring.generator(0)
    linear = ring.add(generator, ring.one())
    quadratic = ring.add(ring.mul(generator, generator), ring.one())
    negative = ring.sub(generator, ring.one())
    assert factorization_key(negative) < factorization_key(linear)
    assert factorization_key(linear) < factorization_key(quadratic)
    half = rational_polynomial(
        ring, [Fraction(1, 2), Fraction(1)]
    )
    assert factorization_key(half) < factorization_key(linear)
