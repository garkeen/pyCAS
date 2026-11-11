"""Hensel lifting and witness construction over ``Z[x]``/``Q[x]``."""

from fractions import Fraction

import pytest

from cas.algebra.factorization import (
    FactorizationBudget,
    FactorizationBudgetError,
    FactorizationFragmentError,
    HenselLift,
    hensel_lift_factorization,
    hensel_witness_for_radical,
)
from cas.algebra.finite_field import PrimeField, is_prime64
from cas.algebra.integer_polynomial import (
    coefficient_bound,
    congruent_mod,
    integer_primitive_form,
)
from cas.algebra.integers import IntegerRing
from cas.algebra.modular_factorization import (
    ModularBudget,
    factor_squarefree_mod_prime,
)
from cas.algebra.modular_polynomial import (
    is_irreducible_mod_prime,
    reduce_mod_prime,
)
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


def prime_ring(modulus: int) -> UnivariatePolynomialRing[int]:
    return UnivariatePolynomialRing(X, PrimeField(modulus))


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


def modular_factors(
    value: Polynomial[int],
    prime: int,
) -> tuple[
    UnivariatePolynomialRing[int],
    Polynomial[int],
    tuple[Polynomial[int], ...],
]:
    """The normalized reduction and its complete Berlekamp factorization."""
    ring = prime_ring(prime)
    reduced = reduce_mod_prime(ring, value)
    degree = ring.degree(reduced, 0)
    leading = ring.coefficient(reduced, (degree,))
    normalized = ring.mul(
        ring.constant(ring.coefficients.inv(leading)), reduced
    )
    factors = factor_squarefree_mod_prime(ring, normalized)
    return ring, normalized, factors


def least_precision(prime: int, value: Polynomial[int]) -> int:
    bound = 2 * coefficient_bound(value)
    precision = 1
    while prime**precision <= bound:
        precision += 1
    return precision


def assert_lift(
    ring: PolynomialRing[int],
    value: Polynomial[int],
    prime: int,
    precision: int,
    lifted: tuple[Polynomial[int], ...],
) -> None:
    modulus = prime**precision
    assert lifted
    owner = lifted[0].owner
    embedded = owner.sum(
        owner.monomial(exponents, coefficient)
        for exponents, coefficient in value.terms
    )
    degree = ring.degree(value, 0)
    leading = ring.coefficient(value, (degree,))
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


def test_lift_of_six_x_squared_plus_five_x_plus_one_mod_five():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 5, 6])
    ring_p, _, factors = modular_factors(value, 5)
    for index, factor in enumerate(factors):
        assert is_irreducible_mod_prime(ring_p, factor)
        for other in factors[index + 1 :]:
            assert not ring_p.equal(factor, other)
    lifted = hensel_lift_factorization(ring, value, 5, factors, 3)
    assert [factor.terms for factor in lifted] == [
        (((0,), 42), ((1,), 1)),
        (((0,), 63), ((1,), 1)),
    ]
    for lifted_factor, modular_factor in zip(lifted, factors):
        assert ring_p.equal(
            reduce_mod_prime(ring_p, lifted_factor), modular_factor
        )
    assert_lift(ring, value, 5, 3, lifted)


@pytest.mark.parametrize(("prime", "precision"), [(3, 4), (5, 3)])
def test_lift_of_x_fourth_plus_one(prime, precision):
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 0, 0, 0, 1])
    _, _, factors = modular_factors(value, prime)
    assert len(factors) == 2
    lifted = hensel_lift_factorization(
        ring, value, prime, factors, precision
    )
    assert [ring.degree(factor, 0) for factor in lifted] == [2, 2]
    assert_lift(ring, value, prime, precision, lifted)


def test_lift_reconstructs_products_of_known_integer_factors():
    ring = integer_ring()
    generator = ring.generator(0)
    examples = (
        (ring.mul(
            ring.mul(
                ring.sub(generator, ring.one()),
                ring.add(generator, ring.one()),
            ),
            ring.add(ring.mul(generator, generator), ring.one()),
        ), 5),
        (ring.mul(
            ring.add(ring.mul(generator, generator), ring.one()),
            ring.add(ring.mul(generator, generator), ring.constant(2)),
        ), 5),
    )
    for value, prime in examples:
        _, _, factors = modular_factors(value, prime)
        precision = least_precision(prime, value)
        lifted = hensel_lift_factorization(
            ring, value, prime, factors, precision
        )
        assert_lift(ring, value, prime, precision, lifted)
    first = hensel_lift_factorization(
        ring, examples[0][0], 5, modular_factors(examples[0][0], 5)[2], 3
    )
    assert len(first) == 4
    assert all(ring.degree(factor, 0) == 1 for factor in first)


def test_lift_accepts_integer_ring_factors():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 5, 6])
    _, _, modular = modular_factors(value, 5)
    integer_factors = tuple(
        ring.sum(
            ring.monomial(exponents, coefficient)
            for exponents, coefficient in factor.terms
        )
        for factor in modular
    )
    lifted = hensel_lift_factorization(
        ring, value, 5, integer_factors, 3
    )
    assert_lift(ring, value, 5, 3, lifted)


def test_lift_supports_characteristic_two():
    ring = integer_ring()
    value = integer_polynomial(ring, [0, 1, 1])
    _, normalized, factors = modular_factors(value, 2)
    assert len(factors) == 2
    precision = least_precision(2, value)
    lifted = hensel_lift_factorization(
        ring, value, 2, factors, precision
    )
    assert_lift(ring, value, 2, precision, lifted)


def test_witness_for_a_radical_with_all_linear_factors():
    ring = rational_ring()
    radical = rational_polynomial(
        ring,
        [
            Fraction(24),
            Fraction(-50),
            Fraction(35),
            Fraction(-10),
            Fraction(1),
        ],
    )
    witness = hensel_witness_for_radical(ring, radical)
    assert is_prime64(witness.prime)
    assert witness.precision >= 1
    form = integer_primitive_form(ring, radical)
    integer_ring_value = form.primitive
    owner = integer_ring_value.owner
    degree = owner.degree(integer_ring_value, 0)
    leading = owner.coefficient(integer_ring_value, (degree,))
    assert leading > 0
    assert_lift(
        owner,
        integer_ring_value,
        witness.prime,
        witness.precision,
        witness.lifted,
    )
    assert len(witness.lifted) == 4


def test_witness_for_x_fourth_plus_one():
    ring = rational_ring()
    radical = rational_polynomial(
        ring, [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(1)]
    )
    witness = hensel_witness_for_radical(ring, radical)
    assert witness.prime == 3
    assert witness.precision == 4
    form = integer_primitive_form(ring, radical)
    assert_lift(
        form.primitive.owner,
        form.primitive,
        witness.prime,
        witness.precision,
        witness.lifted,
    )
    repeated = hensel_witness_for_radical(ring, radical)
    assert (repeated.prime, repeated.precision) == (
        witness.prime,
        witness.precision,
    )
    assert [factor.terms for factor in repeated.lifted] == [
        factor.terms for factor in witness.lifted
    ]


def test_lift_refuses_nonzero_constant_and_positive_leading_violations():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 5, 6])
    _, _, factors = modular_factors(value, 5)
    with pytest.raises(FactorizationFragmentError) as zero:
        hensel_lift_factorization(ring, ring.zero(), 5, factors, 3)
    assert "nonzero_polynomial" in zero.value.missing
    with pytest.raises(FactorizationFragmentError) as constant:
        hensel_lift_factorization(
            ring, integer_polynomial(ring, [5]), 5, factors, 3
        )
    assert "nonconstant_polynomial" in constant.value.missing
    with pytest.raises(FactorizationFragmentError) as negative:
        hensel_lift_factorization(
            ring, integer_polynomial(ring, [-1, -1]), 5, factors, 3
        )
    assert "positive_leading_coefficient" in negative.value.missing


def test_lift_refuses_nonprimitive_and_nonsquarefree_values():
    ring = integer_ring()
    ring_p = prime_ring(3)
    generator = ring_p.generator(0)
    with pytest.raises(FactorizationFragmentError) as nonprimitive:
        hensel_lift_factorization(
            ring, integer_polynomial(ring, [2, 2]), 3, (generator,), 2
        )
    assert "primitive_squarefree_polynomial" in nonprimitive.value.missing
    with pytest.raises(FactorizationFragmentError) as nonsquarefree:
        hensel_lift_factorization(
            ring,
            integer_polynomial(ring, [1, 2, 1]),
            3,
            (ring_p.add(generator, ring_p.one()),),
            2,
        )
    assert "primitive_squarefree_polynomial" in nonsquarefree.value.missing


def test_lift_refuses_bad_primes():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 5, 6])
    _, _, factors = modular_factors(value, 5)
    with pytest.raises(FactorizationFragmentError) as composite:
        hensel_lift_factorization(ring, value, 4, factors, 3)
    assert "prime_modulus" in composite.value.missing
    with pytest.raises(FactorizationFragmentError) as bad_prime:
        hensel_lift_factorization(
            ring, integer_polynomial(ring, [1, 5]), 5, factors, 2
        )
    assert "applicable_prime" in bad_prime.value.missing


def test_lift_refuses_bad_factor_data():
    ring = integer_ring()
    value = integer_polynomial(ring, [-1, 0, 1])
    ring_p, _, _ = modular_factors(value, 5)
    generator = ring_p.generator(0)
    one_plus = ring_p.add(generator, ring_p.one())
    with pytest.raises(FactorizationFragmentError) as nonmonic:
        hensel_lift_factorization(
            ring,
            value,
            5,
            (ring_p.mul(ring_p.constant(2), one_plus),),
            2,
        )
    assert "monic_factors" in nonmonic.value.missing
    with pytest.raises(FactorizationFragmentError) as constant:
        hensel_lift_factorization(
            ring, value, 5, (ring_p.constant(1),), 2
        )
    assert "nonconstant_factors" in constant.value.missing
    with pytest.raises(FactorizationFragmentError) as incomplete:
        hensel_lift_factorization(ring, value, 5, (one_plus,), 2)
    assert "complete_factorization" in incomplete.value.missing
    with pytest.raises(FactorizationFragmentError) as duplicate:
        hensel_lift_factorization(
            ring, value, 5, (one_plus, one_plus), 2
        )
    assert "distinct_factors" in duplicate.value.missing
    shared = ring_p.mul(one_plus, ring_p.add(generator, ring_p.constant(2)))
    with pytest.raises(FactorizationFragmentError) as not_coprime:
        hensel_lift_factorization(
            ring, value, 5, (shared, one_plus), 2
        )
    assert "coprime_factors" in not_coprime.value.missing
    with pytest.raises(FactorizationFragmentError) as empty:
        hensel_lift_factorization(ring, value, 5, (), 2)
    assert "complete_factorization" in empty.value.missing
    rational = rational_ring()
    with pytest.raises(FactorizationFragmentError) as foreign:
        hensel_lift_factorization(
            ring,
            value,
            5,
            (rational_polynomial(rational, [Fraction(1), Fraction(1)]),),
            2,
        )
    assert "factor_ring" in foreign.value.missing


def test_lift_refuses_bad_precision_and_budget():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 0, 1])
    _, _, factors = modular_factors(value, 3)
    for precision in (0, -1):
        with pytest.raises(FactorizationFragmentError) as invalid:
            hensel_lift_factorization(ring, value, 3, factors, precision)
        assert "positive_precision" in invalid.value.missing
    with pytest.raises(FactorizationBudgetError) as exhausted:
        hensel_lift_factorization(
            ring,
            value,
            3,
            factors,
            2,
            FactorizationBudget(max_hensel_precision=1),
        )
    assert "hensel_precision" in exhausted.value.missing


def test_witness_refuses_invalid_radicals():
    ring = rational_ring()
    with pytest.raises(FactorizationFragmentError) as zero:
        hensel_witness_for_radical(ring, ring.zero())
    assert "nonzero_polynomial" in zero.value.missing
    with pytest.raises(FactorizationFragmentError) as constant:
        hensel_witness_for_radical(ring, ring.constant(Fraction(3)))
    assert "nonconstant_polynomial" in constant.value.missing
    with pytest.raises(FactorizationFragmentError) as nonmonic:
        hensel_witness_for_radical(
            ring,
            rational_polynomial(ring, [Fraction(1), Fraction(2)]),
        )
    assert "monic_polynomial" in nonmonic.value.missing
    with pytest.raises(FactorizationFragmentError) as nonsquarefree:
        hensel_witness_for_radical(
            ring,
            rational_polynomial(
                ring, [Fraction(1), Fraction(2), Fraction(1)]
            ),
        )
    assert "primitive_squarefree_polynomial" in nonsquarefree.value.missing
    with pytest.raises(TypeError):
        hensel_witness_for_radical(
            integer_ring(),  # type: ignore[arg-type]
            integer_polynomial(integer_ring(), [1, 0, 1]),
        )


def test_witness_budget_exhaustion():
    ring = rational_ring()
    radical = rational_polynomial(
        ring, [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(1)]
    )
    with pytest.raises(FactorizationBudgetError) as no_trials:
        hensel_witness_for_radical(
            ring, radical, FactorizationBudget(max_prime_trials=0)
        )
    assert "factorization_budget" in no_trials.value.missing
    with pytest.raises(FactorizationBudgetError) as bad_first_prime:
        hensel_witness_for_radical(
            ring, radical, FactorizationBudget(max_prime_trials=1)
        )
    assert "factorization_budget" in bad_first_prime.value.missing
    with pytest.raises(FactorizationBudgetError) as no_precision:
        hensel_witness_for_radical(
            ring, radical, FactorizationBudget(max_hensel_precision=0)
        )
    assert "hensel_precision" in no_precision.value.missing
    with pytest.raises(FactorizationBudgetError) as modular_exhausted:
        hensel_witness_for_radical(
            ring,
            radical,
            FactorizationBudget(modular=ModularBudget(splitting=0, gcd=1000)),
        )
    assert "factorization_budget" in modular_exhausted.value.missing


def test_factorization_budget_validation():
    budget = FactorizationBudget()
    assert budget.max_prime_trials > 0
    assert budget.max_hensel_precision > 0
    assert budget.max_recombination_tests > 0
    assert isinstance(budget.modular, ModularBudget)
    with pytest.raises(ValueError):
        FactorizationBudget(max_prime_trials=-1)
    with pytest.raises(ValueError):
        FactorizationBudget(max_hensel_precision=-1)
    with pytest.raises(ValueError):
        FactorizationBudget(max_recombination_tests=-1)
    with pytest.raises(TypeError):
        FactorizationBudget(max_prime_trials=True)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        FactorizationBudget(max_hensel_precision=2.0)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        FactorizationBudget(max_recombination_tests=True)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        FactorizationBudget(max_recombination_tests=2.0)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        FactorizationBudget(modular=None)  # type: ignore[arg-type]


def test_hensel_lift_record_validation():
    ring = integer_ring()
    value = integer_polynomial(ring, [1, 5, 6])
    _, _, factors = modular_factors(value, 5)
    lifted = hensel_lift_factorization(ring, value, 5, factors, 3)
    witness = HenselLift(prime=5, precision=3, lifted=lifted)
    assert witness.lifted == lifted
    generator = ring.generator(0)
    nonmonic = ring.mul(ring.constant(2), generator)
    with pytest.raises(TypeError):
        HenselLift(prime=True, precision=3, lifted=lifted)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        HenselLift(prime=5, precision=3.0, lifted=lifted)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        HenselLift(prime=4, precision=3, lifted=lifted)
    with pytest.raises(ValueError):
        HenselLift(prime=5, precision=0, lifted=lifted)
    with pytest.raises(ValueError):
        HenselLift(prime=5, precision=3, lifted=())
    with pytest.raises(ValueError):
        HenselLift(
            prime=5,
            precision=3,
            lifted=(ring.constant(3),),
        )
    with pytest.raises(ValueError):
        HenselLift(prime=5, precision=3, lifted=(nonmonic,))
    with pytest.raises(ValueError):
        HenselLift(
            prime=5,
            precision=1,
            lifted=(ring.add(generator, ring.constant(5)),),
        )
    with pytest.raises(ValueError):
        HenselLift(
            prime=5,
            precision=3,
            lifted=(generator, integer_polynomial(integer_ring(), [1, 1])),
        )
    with pytest.raises(TypeError):
        HenselLift(prime=5, precision=3, lifted=(rational_ring().one(),))  # type: ignore[arg-type]
