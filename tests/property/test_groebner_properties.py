"""Randomized Groebner laws: cofactors, criterion and canonical reduced bases."""

import random
from fractions import Fraction

from cas.algebra.groebner import (
    buchberger,
    ideal_equal,
    ideal_membership,
    leading_coefficient,
    leading_monomial,
    normal_form,
    s_polynomial,
)
from cas.algebra.polynomial import MonomialOrder, Polynomial, PolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

SEED = 20261110
X, Y = SymbolId(1), SymbolId(2)


def make_ring(order: MonomialOrder) -> PolynomialRing[Fraction]:
    return PolynomialRing((X, Y), RationalField(), order)


def random_polynomial(
    rng: random.Random,
    ring: PolynomialRing[Fraction],
    *,
    max_degree: int = 2,
    max_terms: int = 4,
) -> Polynomial[Fraction]:
    value = ring.zero()
    for _ in range(rng.randint(1, max_terms)):
        exponents = (
            rng.randint(0, max_degree),
            rng.randint(0, max_degree),
        )
        coefficient = Fraction(rng.randint(-3, 3), rng.randint(1, 3))
        value = ring.add(value, ring.monomial(exponents, coefficient))
    return value


def random_system(
    rng: random.Random,
    ring: PolynomialRing[Fraction],
    *,
    count: int = 3,
) -> tuple[Polynomial[Fraction], ...]:
    return tuple(random_polynomial(rng, ring) for _ in range(count))


def reduced_basis(
    ring: PolynomialRing[Fraction],
    generators: tuple[Polynomial[Fraction], ...],
):
    return buchberger(ring, generators, budget=50000)


def assert_same_reduced_basis(
    ring: PolynomialRing[Fraction],
    left,
    right,
) -> None:
    assert len(left.basis) == len(right.basis)
    for first, second in zip(left.basis, right.basis):
        assert ring.equal(first, second)


def assert_cofactor_identity(ring, basis) -> None:
    for element, cofactors in zip(basis.basis, basis.cofactors):
        combination = ring.sum(
            ring.mul(cofactor, generator)
            for cofactor, generator in zip(
                cofactors, basis.original_generators
            )
        )
        assert ring.equal(combination, element)


def assert_buchberger_criterion(ring, basis) -> None:
    for left_index, left in enumerate(basis.basis):
        for right in basis.basis[left_index + 1 :]:
            value = s_polynomial(ring, left, right)
            assert normal_form(ring, value, basis.basis).is_zero()


def assert_reduced_basis_shape(ring, basis) -> None:
    for index, element in enumerate(basis.basis):
        assert not element.is_zero()
        assert ring.coefficients.is_one(leading_coefficient(ring, element))
        for exponents, _ in element.terms:
            for other_index, other in enumerate(basis.basis):
                if other_index == index:
                    continue
                divisor = leading_monomial(ring, other)
                assert not all(
                    left <= right for left, right in zip(divisor, exponents)
                )


def test_random_systems_satisfy_the_groebner_laws():
    for order in (
        MonomialOrder.LEX,
        MonomialOrder.GRLEX,
        MonomialOrder.GREVLEX,
    ):
        rng = random.Random(SEED + list(MonomialOrder).index(order))
        ring = make_ring(order)
        for _ in range(10):
            generators = random_system(rng, ring)
            basis = reduced_basis(ring, generators)
            assert_cofactor_identity(ring, basis)
            assert_reduced_basis_shape(ring, basis)
            assert_buchberger_criterion(ring, basis)
            for generator in generators:
                assert normal_form(ring, generator, basis.basis).is_zero()

            again = reduced_basis(ring, basis.basis)
            assert_same_reduced_basis(ring, basis, again)
            assert ideal_equal(basis, again)


def test_random_systems_have_order_and_scaling_independent_reduced_bases():
    for order in (
        MonomialOrder.LEX,
        MonomialOrder.GRLEX,
        MonomialOrder.GREVLEX,
    ):
        rng = random.Random(SEED + 100 + list(MonomialOrder).index(order))
        ring = make_ring(order)
        for _ in range(10):
            generators = random_system(rng, ring)
            basis = reduced_basis(ring, generators)
            scaled = [
                ring.mul(
                    ring.constant(
                        Fraction(rng.choice([-3, -2, -1, 2, 3]), rng.randint(1, 3))
                    ),
                    generator,
                )
                for generator in generators
            ]
            rng.shuffle(scaled)
            alternate = reduced_basis(ring, tuple(scaled))
            assert_same_reduced_basis(ring, basis, alternate)
            assert ideal_equal(basis, alternate)
            for _ in range(3):
                value = random_polynomial(rng, ring, max_degree=3)
                assert ideal_membership(basis, value) == ideal_membership(
                    alternate, value
                )


def test_random_ideal_membership_is_exact_for_buchberger_bases():
    for order in (
        MonomialOrder.LEX,
        MonomialOrder.GRLEX,
        MonomialOrder.GREVLEX,
    ):
        rng = random.Random(SEED + 200 + list(MonomialOrder).index(order))
        ring = make_ring(order)
        for _ in range(10):
            generators = random_system(rng, ring)
            basis = reduced_basis(ring, generators)

            for _ in range(3):
                cofactors = [
                    random_polynomial(rng, ring, max_degree=2)
                    for _ in generators
                ]
                combination = ring.sum(
                    ring.mul(cofactor, generator)
                    for cofactor, generator in zip(cofactors, generators)
                )
                assert ideal_membership(basis, combination)

            for _ in range(3):
                value = random_polynomial(rng, ring, max_degree=3)
                assert ideal_membership(basis, value) == normal_form(
                    ring, value, basis.basis
                ).is_zero()
