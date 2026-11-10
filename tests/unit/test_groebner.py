"""Multivariate division, Buchberger bases and cofactors over a field."""

from dataclasses import replace
from fractions import Fraction

import pytest

from cas.algebra.groebner import (
    BuchbergerBudgetError,
    GroebnerBasis,
    GroebnerFragmentError,
    GroebnerStatistics,
    buchberger,
    ideal_equal,
    ideal_membership,
    leading_coefficient,
    leading_monomial,
    leading_term,
    multivariate_divmod,
    normal_form,
    s_polynomial,
)
from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import MonomialOrder, Polynomial, PolynomialRing
from cas.algebra.protocols import Field
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X, Y = SymbolId(1), SymbolId(2)


def make_ring(order: MonomialOrder = MonomialOrder.LEX) -> PolynomialRing[Fraction]:
    return PolynomialRing((X, Y), RationalField(), order)


def polynomial(
    ring: PolynomialRing[Fraction],
    terms: dict[tuple[int, ...], Fraction | int],
) -> Polynomial[Fraction]:
    return ring.sum(
        ring.monomial(exponents, Fraction(coefficient))
        for exponents, coefficient in terms.items()
    )


def x(ring: PolynomialRing[Fraction]) -> Polynomial[Fraction]:
    return ring.generator(0)


def y(ring: PolynomialRing[Fraction]) -> Polynomial[Fraction]:
    return ring.generator(1)


def assert_same_basis(
    ring: PolynomialRing[Fraction],
    actual: tuple[Polynomial[Fraction], ...],
    expected: tuple[Polynomial[Fraction], ...],
) -> None:
    assert len(actual) == len(expected)
    remaining = list(expected)
    for value in actual:
        for index, candidate in enumerate(remaining):
            if ring.equal(value, candidate):
                del remaining[index]
                break
        else:
            raise AssertionError("a polynomial is missing from the basis")
    assert not remaining


def assert_reduced(
    ring: PolynomialRing[Fraction],
    basis: tuple[Polynomial[Fraction], ...],
) -> None:
    for index, value in enumerate(basis):
        assert not value.is_zero()
        assert ring.coefficients.is_one(leading_coefficient(ring, value))
        for exponents, _ in value.terms:
            for other_index, other in enumerate(basis):
                if other_index == index:
                    continue
                divisor = leading_monomial(ring, other)
                assert not all(
                    left <= right for left, right in zip(divisor, exponents)
                )


def assert_cofactor_identity(
    ring: PolynomialRing[Fraction],
    basis,
) -> None:
    for element, cofactors in zip(basis.basis, basis.cofactors):
        combination = ring.sum(
            ring.mul(cofactor, generator)
            for cofactor, generator in zip(
                cofactors, basis.original_generators
            )
        )
        assert ring.equal(combination, element)


def test_leading_helpers_follow_the_declared_order():
    lex = make_ring(MonomialOrder.LEX)
    grlex = make_ring(MonomialOrder.GRLEX)
    grevlex = make_ring(MonomialOrder.GREVLEX)
    terms = {(2, 0): Fraction(3), (0, 3): Fraction(1), (1, 1): Fraction(-2)}
    lex_value = polynomial(lex, terms)
    grlex_value = polynomial(grlex, terms)
    grevlex_value = polynomial(grevlex, terms)

    assert leading_monomial(lex, lex_value) == (2, 0)
    assert leading_coefficient(lex, lex_value) == 3
    assert leading_term(lex, lex_value) == ((2, 0), Fraction(3))

    assert leading_monomial(grlex, grlex_value) == (0, 3)
    assert leading_coefficient(grlex, grlex_value) == 1

    assert leading_monomial(grevlex, grevlex_value) == (0, 3)
    assert leading_coefficient(grevlex, grevlex_value) == 1

    for ring in (lex, grlex, grevlex):
        with pytest.raises(GroebnerFragmentError) as raised:
            leading_term(ring, ring.zero())
        assert raised.value.missing == frozenset({"nonzero_polynomial"})


def test_division_returns_quotients_and_the_exact_remainder():
    ring = make_ring()
    value = polynomial(
        ring,
        {
            (2, 1): 1,
            (1, 2): 1,
            (0, 2): 1,
        },
    )
    first = polynomial(ring, {(1, 1): 1, (0, 0): -1})
    second = polynomial(ring, {(0, 2): 1, (0, 0): -1})
    division = multivariate_divmod(ring, value, (first, second))

    assert ring.equal(
        division.quotients[0], ring.add(x(ring), y(ring))
    )
    assert ring.equal(division.quotients[1], ring.one())
    assert ring.equal(
        division.remainder,
        ring.add(ring.add(x(ring), y(ring)), ring.one()),
    )
    reconstructed = ring.add(
        ring.sum(
            ring.mul(quotient, divisor)
            for quotient, divisor in zip(
                division.quotients, (first, second)
            )
        ),
        division.remainder,
    )
    assert ring.equal(reconstructed, value)

    for exponents, _ in division.remainder.terms:
        for divisor in (first, second):
            leading = leading_monomial(ring, divisor)
            assert not all(
                left <= right
                for left, right in zip(leading, exponents)
            )


def test_division_scales_by_non_monic_leading_coefficients():
    ring = make_ring()
    divisor = polynomial(ring, {(1, 0): 2, (0, 0): 1})
    quotient = polynomial(ring, {(1, 0): 1, (0, 0): 3})
    remainder = y(ring)
    value = ring.add(ring.mul(divisor, quotient), remainder)
    division = multivariate_divmod(ring, value, (divisor,))
    assert ring.equal(division.quotients[0], quotient)
    assert ring.equal(division.remainder, remainder)


def test_division_handles_empty_divisors_zero_input_and_zero_divisor():
    ring = make_ring()
    value = polynomial(ring, {(1, 0): 2, (0, 0): 1})
    division = multivariate_divmod(ring, value, ())
    assert division.quotients == ()
    assert ring.equal(division.remainder, value)

    zero_division = multivariate_divmod(ring, ring.zero(), (value,))
    assert ring.equal(zero_division.quotients[0], ring.zero())
    assert zero_division.remainder.is_zero()

    with pytest.raises(GroebnerFragmentError) as raised:
        multivariate_divmod(ring, value, (ring.zero(),))
    assert raised.value.missing == frozenset({"nonzero_divisor"})

    with pytest.raises(ValueError):
        multivariate_divmod(ring, value, (make_ring().generator(0),))


def test_a_non_groebner_remainder_is_not_an_ideal_normal_form():
    ring = make_ring()
    first = polynomial(ring, {(2, 0): 1, (0, 1): -1})
    second = polynomial(ring, {(1, 1): 1, (0, 0): -1})
    combination = s_polynomial(ring, first, second)
    assert ring.equal(
        combination,
        polynomial(ring, {(1, 0): 1, (0, 2): -1}),
    )
    remainder = normal_form(ring, combination, (first, second))
    assert ring.equal(remainder, combination)
    assert not remainder.is_zero()


def test_s_polynomial_uses_exact_leading_coefficients():
    ring = make_ring()
    left = polynomial(ring, {(2, 0): 2, (0, 1): 1})
    right = polynomial(ring, {(1, 1): 3, (0, 0): 1})
    value = s_polynomial(ring, left, right)
    assert ring.equal(
        value,
        polynomial(
            ring,
            {(0, 2): Fraction(1, 2), (1, 0): Fraction(-1, 3)},
        ),
    )

    scalar_multiple = ring.mul(ring.constant(Fraction(2)), left)
    assert s_polynomial(ring, left, scalar_multiple).is_zero()

    for zero in (ring.zero(),):
        with pytest.raises(GroebnerFragmentError) as raised:
            s_polynomial(ring, left, zero)
        assert raised.value.missing == frozenset({"nonzero_polynomial"})

    with pytest.raises(ValueError):
        s_polynomial(ring, left, make_ring().generator(1))


def test_buchberger_reduces_the_circle_line_system_in_each_order():
    expected_terms = (
        {(0, 2): 1, (0, 0): Fraction(-1, 2)},
        {(1, 0): 1, (0, 1): -1},
    )
    for order in (
        MonomialOrder.LEX,
        MonomialOrder.GRLEX,
        MonomialOrder.GREVLEX,
    ):
        ring = make_ring(order)
        circle = polynomial(
            ring, {(2, 0): 1, (0, 2): 1, (0, 0): -1}
        )
        line = polynomial(ring, {(1, 0): 1, (0, 1): -1})
        basis = buchberger(ring, (circle, line), budget=1000)

        expected = tuple(polynomial(ring, terms) for terms in expected_terms)
        assert_same_basis(ring, basis.basis, expected)
        assert_reduced(ring, basis.basis)
        assert_cofactor_identity(ring, basis)
        for generator in basis.original_generators:
            assert normal_form(ring, generator, basis.basis).is_zero()
        assert basis.statistics.pairs >= 1
        assert basis.statistics.reductions >= 1


def test_buchberger_order_changes_the_parabola_system_reduced_basis():
    lex = make_ring(MonomialOrder.LEX)
    lex_first = polynomial(lex, {(2, 0): 1, (0, 1): -1})
    lex_second = polynomial(lex, {(1, 0): 1, (0, 2): -1})
    lex_basis = buchberger(lex, (lex_first, lex_second), budget=1000)
    assert_same_basis(
        lex,
        lex_basis.basis,
        (
            polynomial(lex, {(0, 4): 1, (0, 1): -1}),
            polynomial(lex, {(1, 0): 1, (0, 2): -1}),
        ),
    )

    grlex = make_ring(MonomialOrder.GRLEX)
    grlex_first = polynomial(grlex, {(2, 0): 1, (0, 1): -1})
    grlex_second = polynomial(grlex, {(1, 0): 1, (0, 2): -1})
    grlex_basis = buchberger(grlex, (grlex_first, grlex_second), budget=1000)
    assert_same_basis(
        grlex,
        grlex_basis.basis,
        (
            polynomial(grlex, {(2, 0): 1, (0, 1): -1}),
            polynomial(grlex, {(1, 0): -1, (0, 2): 1}),
        ),
    )

    for basis in (lex_basis, grlex_basis):
        assert_reduced(basis.ring, basis.basis)
        assert_cofactor_identity(basis.ring, basis)
        for generator in basis.original_generators:
            assert normal_form(
                basis.ring, generator, basis.basis
            ).is_zero()


def test_empty_zero_and_duplicate_generators():
    ring = make_ring()
    empty = buchberger(ring, (), budget=0)
    assert empty.basis == ()
    assert empty.original_generators == ()
    assert empty.statistics.pairs == 0
    assert ideal_membership(empty, ring.zero())
    assert not ideal_membership(empty, x(ring))

    zero = buchberger(ring, (ring.zero(),), budget=0)
    assert zero.basis == ()
    assert len(zero.original_generators) == 1
    assert ideal_membership(zero, ring.zero())
    assert not ideal_membership(zero, x(ring))

    value = polynomial(ring, {(2, 0): 1, (0, 1): -1})
    duplicated = buchberger(
        ring,
        (value, ring.zero(), ring.mul(ring.constant(Fraction(3)), value)),
        budget=100,
    )
    plain = buchberger(ring, (value,), budget=100)
    assert_same_basis(ring, duplicated.basis, plain.basis)
    assert len(duplicated.original_generators) == 3
    assert_cofactor_identity(ring, duplicated)
    for generator in duplicated.original_generators:
        assert normal_form(ring, generator, duplicated.basis).is_zero()


def test_unit_ideal_is_the_whole_ring():
    ring = make_ring()
    basis = buchberger(
        ring,
        (ring.constant(Fraction(3)), polynomial(ring, {(1, 0): 1})),
        budget=100,
    )
    assert len(basis.basis) == 1
    assert ring.equal(basis.basis[0], ring.one())
    assert ideal_membership(basis, x(ring))
    assert ideal_membership(basis, y(ring))
    assert ideal_membership(basis, ring.zero())
    assert_cofactor_identity(ring, basis)


def test_ideal_membership_and_ideal_equality():
    ring = make_ring()
    circle = polynomial(ring, {(2, 0): 1, (0, 2): 1, (0, 0): -1})
    line = polynomial(ring, {(1, 0): 1, (0, 1): -1})
    basis = buchberger(ring, (circle, line), budget=1000)

    assert ideal_membership(basis, circle)
    assert ideal_membership(basis, line)
    assert ideal_membership(
        basis,
        ring.add(circle, ring.mul(line, ring.add(x(ring), y(ring)))),
    )
    assert not ideal_membership(basis, x(ring))
    assert not ideal_membership(basis, y(ring))

    alternate = buchberger(
        ring,
        (
            ring.mul(ring.constant(Fraction(2)), line),
            ring.mul(ring.constant(Fraction(-3)), circle),
            ring.add(circle, line),
        ),
        budget=1000,
    )
    assert ideal_equal(basis, alternate)
    assert_same_basis(ring, basis.basis, alternate.basis)

    first_ideal = buchberger(ring, (x(ring),), budget=10)
    second_ideal = buchberger(ring, (y(ring),), budget=10)
    assert not ideal_equal(first_ideal, second_ideal)
    assert not ideal_membership(first_ideal, y(ring))

    with pytest.raises(ValueError):
        ideal_membership(basis, make_ring().generator(0))
    other_ring = make_ring()
    with pytest.raises(ValueError):
        ideal_equal(
            first_ideal,
            buchberger(other_ring, (x(other_ring),), budget=10),
        )


def test_non_field_coefficients_are_refused():
    integer_ring = PolynomialRing((X,), IntegerRing())
    value = integer_ring.generator(0)
    for operation in (
        lambda: multivariate_divmod(integer_ring, value, (value,)),
        lambda: normal_form(integer_ring, value, (value,)),
        lambda: s_polynomial(integer_ring, value, value),
        lambda: buchberger(integer_ring, (value,), budget=10),
        lambda: buchberger(integer_ring, (), budget=10),
    ):
        with pytest.raises(GroebnerFragmentError) as raised:
            operation()
        assert raised.value.missing == frozenset({"coefficient_field"})


def test_mixed_rings_are_refused():
    lex = make_ring(MonomialOrder.LEX)
    grlex = make_ring(MonomialOrder.GRLEX)
    with pytest.raises(ValueError):
        multivariate_divmod(lex, lex.generator(0), (grlex.generator(0),))
    with pytest.raises(ValueError):
        normal_form(lex, grlex.generator(0), (lex.generator(0),))
    with pytest.raises(ValueError):
        s_polynomial(lex, lex.generator(0), grlex.generator(0))
    with pytest.raises(ValueError):
        buchberger(lex, (lex.generator(0), grlex.generator(0)), budget=10)


def test_groebner_basis_is_sealed_to_buchberger():
    ring = make_ring()
    with pytest.raises(ValueError, match="issued only by buchberger"):
        GroebnerBasis(
            ring=ring,
            order=ring.monomial_order,
            original_generators=(),
            basis=(),
            cofactors=(),
            statistics=GroebnerStatistics(0, 0),
        )

    issued = buchberger(ring, (), budget=0)
    assert isinstance(issued, GroebnerBasis)
    with pytest.raises(ValueError, match="issued only by buchberger"):
        replace(issued, basis=())


@pytest.mark.parametrize("budget", [True, False, 1.5, "10", None])
def test_buchberger_rejects_non_integer_budgets(budget):
    ring = make_ring()
    with pytest.raises(TypeError, match="budget must be an int"):
        buchberger(ring, (), budget=budget)  # type: ignore[arg-type]


def test_budget_exhaustion_never_returns_a_partial_basis():
    ring = make_ring()
    first = polynomial(ring, {(2, 0): 1, (0, 1): -1})
    second = polynomial(ring, {(1, 0): 1, (0, 2): -1})

    with pytest.raises(BuchbergerBudgetError) as raised:
        buchberger(ring, (first, second), budget=0)
    assert raised.value.used == 1
    assert raised.value.budget == 0
    assert raised.value.phase == "critical pair"
    assert raised.value.missing == frozenset({"buchberger_budget"})

    with pytest.raises(BuchbergerBudgetError) as raised:
        buchberger(ring, (first, second), budget=1)
    assert raised.value.used == 2
    assert raised.value.phase == "leading-term reduction"

    completed = buchberger(ring, (first, second), budget=1000)
    assert completed.basis

    with pytest.raises(ValueError):
        buchberger(ring, (first,), budget=-1)


class FiniteField5(Field[int]):
    """A test-local field of five elements, used to check characteristic p."""

    def zero(self) -> int:
        return 0

    def one(self) -> int:
        return 1

    def add(self, left: int, right: int) -> int:
        return (left + right) % 5

    def neg(self, value: int) -> int:
        return (-value) % 5

    def mul(self, left: int, right: int) -> int:
        return (left * right) % 5

    def contains(self, value: object) -> bool:
        return isinstance(value, int) and 0 <= value < 5

    def equal(self, left: int, right: int) -> bool:
        return (left - right) % 5 == 0

    def inv(self, value: int) -> int:
        if value % 5 == 0:
            raise ZeroDivisionError("zero has no inverse in GF(5)")
        return pow(value, -1, 5)

    @property
    def characteristic(self) -> int:
        return 5


def test_positive_characteristic_is_supported():
    coefficients = FiniteField5()
    ring = PolynomialRing((X, Y), coefficients, MonomialOrder.LEX)
    first = ring.sub(ring.pow(ring.generator(0), 2), ring.generator(1))
    second = ring.sub(ring.generator(0), ring.pow(ring.generator(1), 2))
    basis = buchberger(ring, (first, second), budget=1000)

    assert len(basis.basis) == 2
    for element, cofactors in zip(basis.basis, basis.cofactors):
        combination = ring.sum(
            ring.mul(cofactor, generator)
            for cofactor, generator in zip(
                cofactors, basis.original_generators
            )
        )
        assert ring.equal(combination, element)
        assert coefficients.is_one(leading_coefficient(ring, element))
    for generator in basis.original_generators:
        assert normal_form(ring, generator, basis.basis).is_zero()
    for left_index, left in enumerate(basis.basis):
        for right in basis.basis[left_index + 1 :]:
            value = s_polynomial(ring, left, right)
            assert normal_form(ring, value, basis.basis).is_zero()
