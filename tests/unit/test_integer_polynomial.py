"""Integer primitive forms, coefficient bounds and exact coefficient helpers."""

import random
from fractions import Fraction

import pytest

from cas.algebra.integer_polynomial import (
    IntegerPolynomialForm,
    coefficient_bound,
    congruent_mod,
    integer_divisors,
    integer_primitive_form,
    monic_rational_form,
    positive_primitive_part,
    rational_polynomial_form,
    symmetric_residue,
)
from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import Polynomial, PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)
Y = SymbolId(2)


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


def assert_primitive(ring: PolynomialRing[int], value: Polynomial[int]) -> None:
    assert not value.is_zero()
    assert ring.coefficients.is_one(ring.content(value))
    assert ring.coefficient(value, (ring.degree(value, 0),)) > 0


@pytest.mark.parametrize(
    ("coefficients", "unit", "primitive"),
    [
        ([Fraction(1), Fraction(2)], Fraction(1), [1, 2]),
        ([Fraction(-2, 3), Fraction(0), Fraction(2, 3)], Fraction(2, 3), [-1, 0, 1]),
        ([Fraction(1), Fraction(0), Fraction(-1)], Fraction(-1), [-1, 0, 1]),
        ([Fraction(5, 2)], Fraction(5, 2), [1]),
        ([Fraction(-3, 4)], Fraction(-3, 4), [1]),
        ([Fraction(1, 3), Fraction(1, 2)], Fraction(1, 6), [2, 3]),
        ([Fraction(2, 3), Fraction(0), Fraction(4, 3)], Fraction(2, 3), [1, 0, 2]),
    ],
)
def test_integer_primitive_form_examples(coefficients, unit, primitive):
    ring_q = rational_ring()
    value = rational_polynomial(ring_q, coefficients)
    form = integer_primitive_form(ring_q, value)
    assert_primitive(form.primitive.owner, form.primitive)
    assert form.primitive.terms == tuple(
        ((index,), coefficient)
        for index, coefficient in enumerate(primitive)
        if coefficient
    )
    assert form.unit == unit
    embedded = rational_polynomial_form(ring_q, form.primitive)
    assert ring_q.equal(
        ring_q.mul(ring_q.constant(form.unit), embedded),
        value,
    )


def test_integer_primitive_form_rejects_zero_and_foreign_values():
    ring_q = rational_ring()
    with pytest.raises(ValueError):
        integer_primitive_form(ring_q, ring_q.zero())
    with pytest.raises(ValueError):
        integer_primitive_form(ring_q, UnivariatePolynomialRing(Y, RationalField()).one())
    with pytest.raises(TypeError):
        integer_primitive_form(integer_ring(), integer_ring().one())  # type: ignore[arg-type]


def test_integer_primitive_form_is_unique_and_hashable():
    ring_q = rational_ring()
    value = rational_polynomial(ring_q, [Fraction(2, 3), Fraction(0), Fraction(-2, 3)])
    first = integer_primitive_form(ring_q, value)
    second = integer_primitive_form(ring_q, value)
    assert first == second
    assert hash(first) == hash(second)
    other = integer_primitive_form(ring_q, rational_polynomial(ring_q, [Fraction(1)]))
    assert first != other


def test_integer_polynomial_form_invariants():
    ring_z = integer_ring()
    IntegerPolynomialForm(Fraction(1), ring_z.generator(0))
    with pytest.raises(ValueError):
        IntegerPolynomialForm(Fraction(0), ring_z.generator(0))
    with pytest.raises(TypeError):
        IntegerPolynomialForm(1, ring_z.generator(0))  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        IntegerPolynomialForm(Fraction(1), ring_z.zero())
    with pytest.raises(ValueError):
        IntegerPolynomialForm(Fraction(1), ring_z.constant(2))
    with pytest.raises(ValueError):
        IntegerPolynomialForm(Fraction(1), ring_z.neg(ring_z.generator(0)))
    with pytest.raises(TypeError):
        IntegerPolynomialForm(Fraction(1), rational_ring().generator(0))


def test_rational_polynomial_form_is_the_coefficient_embedding():
    ring_q = rational_ring()
    ring_z = integer_ring()
    value = integer_polynomial(ring_z, [1, 2])
    embedded = rational_polynomial_form(ring_q, value)
    assert embedded.terms == (
        ((0,), Fraction(1)),
        ((1,), Fraction(2)),
    )
    assert rational_polynomial_form(ring_q, ring_z.zero()).is_zero()
    with pytest.raises(ValueError):
        rational_polynomial_form(
            UnivariatePolynomialRing(Y, RationalField()),
            value,
        )
    with pytest.raises(TypeError):
        rational_polynomial_form(ring_q, ring_q.one())


def test_monic_rational_form_divides_by_the_leading_coefficient():
    ring_q = rational_ring()
    value = rational_polynomial(ring_q, [Fraction(1), Fraction(2)])
    assert monic_rational_form(ring_q, value).terms == (
        ((0,), Fraction(1, 2)),
        ((1,), Fraction(1)),
    )
    assert monic_rational_form(ring_q, ring_q.constant(Fraction(5))).terms == (
        ((0,), Fraction(1)),
    )
    with pytest.raises(ValueError):
        monic_rational_form(ring_q, ring_q.zero())
    with pytest.raises(ValueError):
        monic_rational_form(ring_q, UnivariatePolynomialRing(Y, RationalField()).one())


def test_coefficient_bound_on_large_known_factors():
    ring_z = integer_ring()
    factor = integer_polynomial(ring_z, [1, 10**6])
    other = integer_polynomial(ring_z, [1, -(10**6), 1])
    product = ring_z.mul(factor, other)
    bound = coefficient_bound(product)
    assert bound > 10**12
    for value in (factor, other):
        for _, coefficient in value.terms:
            assert abs(coefficient) < bound


def test_coefficient_bound_on_random_known_factor_products():
    rng = random.Random(20261111)
    ring_z = integer_ring()
    for _ in range(80):
        left = integer_polynomial(
            ring_z,
            [rng.randint(-500, 500) for _ in range(rng.randint(1, 5))],
        )
        right = integer_polynomial(
            ring_z,
            [rng.randint(-500, 500) for _ in range(rng.randint(1, 5))],
        )
        if left.is_zero() or right.is_zero():
            continue
        product = ring_z.mul(left, right)
        bound = coefficient_bound(product)
        assert bound > 0
        for value in (left, right):
            for _, coefficient in value.terms:
                assert abs(coefficient) < bound


def test_coefficient_bound_constants_and_refusals():
    ring_z = integer_ring()
    assert coefficient_bound(ring_z.constant(7)) == 8
    assert coefficient_bound(ring_z.constant(-7)) == 8
    with pytest.raises(ValueError):
        coefficient_bound(ring_z.zero())
    with pytest.raises(TypeError):
        coefficient_bound(rational_ring().one())  # type: ignore[arg-type]


def test_symmetric_residue_ranges_and_congruence():
    ring_z = integer_ring()
    value = integer_polynomial(ring_z, [0, 1, 2, 3, 4, 5, 6, 7, -1, -2])
    residue = symmetric_residue(ring_z, value, 7)
    assert residue.terms == (
        ((1,), 1),
        ((2,), 2),
        ((3,), 3),
        ((4,), -3),
        ((5,), -2),
        ((6,), -1),
        ((8,), -1),
        ((9,), -2),
    )
    for _, coefficient in residue.terms:
        assert -3 <= coefficient <= 3
    assert congruent_mod(value, residue, 7)
    even = integer_polynomial(ring_z, [3, 4, -3, -4])
    assert symmetric_residue(ring_z, even, 6).terms == (
        ((0,), 3),
        ((1,), -2),
        ((2,), 3),
        ((3,), 2),
    )
    assert symmetric_residue(ring_z, value, 1).is_zero()
    with pytest.raises(ValueError):
        symmetric_residue(ring_z, value, 0)
    with pytest.raises(ValueError):
        symmetric_residue(ring_z, value, -7)
    with pytest.raises(TypeError):
        symmetric_residue(ring_z, value, True)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        symmetric_residue(integer_ring(), integer_ring().one(), 7)


def test_positive_primitive_part_normalizes_content_and_sign():
    ring_z = integer_ring()
    assert positive_primitive_part(
        ring_z, integer_polynomial(ring_z, [3, -9, 6])
    ).terms == (
        ((0,), 1),
        ((1,), -3),
        ((2,), 2),
    )
    assert positive_primitive_part(
        ring_z, integer_polynomial(ring_z, [-2, 0, 4])
    ).terms == (
        ((0,), -1),
        ((2,), 2),
    )
    assert positive_primitive_part(
        ring_z, integer_polynomial(ring_z, [-3, -6])
    ).terms == (
        ((0,), 1),
        ((1,), 2),
    )
    for value in (
        integer_polynomial(ring_z, [3, -9, 6]),
        integer_polynomial(ring_z, [-2, 0, 4]),
        integer_polynomial(ring_z, [-5]),
    ):
        assert_primitive(ring_z, positive_primitive_part(ring_z, value))
    assert positive_primitive_part(ring_z, ring_z.zero()).is_zero()
    with pytest.raises(ValueError):
        positive_primitive_part(integer_ring(), integer_ring().one())


def test_integer_divisors_are_positive_and_ascending():
    assert integer_divisors(1) == (1,)
    assert integer_divisors(-1) == (1,)
    assert integer_divisors(12) == (1, 2, 3, 4, 6, 12)
    assert integer_divisors(-12) == (1, 2, 3, 4, 6, 12)
    assert integer_divisors(81) == (1, 3, 9, 27, 81)
    assert integer_divisors(97) == (1, 97)
    with pytest.raises(ValueError):
        integer_divisors(0)
    with pytest.raises(TypeError):
        integer_divisors(True)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        integer_divisors(12.0)  # type: ignore[arg-type]


def test_congruent_mod_is_exact_coefficient_wise_divisibility():
    ring_z = integer_ring()
    left = integer_polynomial(ring_z, [5, 3, 1])
    right = integer_polynomial(ring_z, [2, 0, 1])
    assert congruent_mod(left, right, 3)
    assert not congruent_mod(left, integer_polynomial(ring_z, [2, 1, 1]), 3)
    assert congruent_mod(
        integer_polynomial(ring_z, [3, 0, 0, 0]),
        ring_z.zero(),
        3,
    )
    assert congruent_mod(left, right, 1)
    with pytest.raises(ValueError):
        congruent_mod(left, right, 0)
    with pytest.raises(ValueError):
        congruent_mod(left, right, -3)
    with pytest.raises(TypeError):
        congruent_mod(left, right, True)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        congruent_mod(left, integer_ring().one(), 3)
    with pytest.raises(TypeError):
        congruent_mod(left, 1, 3)  # type: ignore[arg-type]
