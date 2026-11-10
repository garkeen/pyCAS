"""Exact Cauchy bounds and open-interval real-root isolation over Q."""

from fractions import Fraction

import pytest

from cas.algebra.polynomial import UnivariatePolynomialRing
from cas.algebra.protocols import Field
from cas.algebra.rationals import RationalField
from cas.algebra.real_roots import (
    RealRootBudgetError,
    RealRootFragmentError,
    cauchy_bound,
    count_real_roots_open,
    evaluate,
    isolate_real_roots_open,
)
from cas.foundation.ids import SymbolId

X = SymbolId(1)


def ring() -> UnivariatePolynomialRing[Fraction]:
    return UnivariatePolynomialRing(X, RationalField())


def q(value: int, denominator: int = 1) -> Fraction:
    return Fraction(value, denominator)


def product_of_linear(
    base: UnivariatePolynomialRing[Fraction],
    roots: tuple[Fraction, ...],
):
    value = base.one()
    for root in roots:
        value = base.mul(
            value, base.sub(base.generator(0), base.constant(root))
        )
    return value


def test_cauchy_bound_bounds_known_rational_roots():
    base = ring()
    value = product_of_linear(base, (q(-7), q(5)))
    bound = cauchy_bound(base, value)
    assert bound == q(36)
    assert bound > abs(q(-7)) and bound > abs(q(5))


def test_cauchy_bound_of_a_nonzero_constant_is_one():
    base = ring()
    assert cauchy_bound(base, base.constant(q(7, 3))) == q(1)


def test_cauchy_bound_refuses_the_zero_polynomial():
    base = ring()
    with pytest.raises(RealRootFragmentError) as zero:
        cauchy_bound(base, base.zero())
    assert zero.value.missing == frozenset({"nonzero_polynomial"})


class UnorderedRationals(Field[Fraction]):
    """A characteristic-zero field with no order interface, for boundary tests."""

    def __init__(self) -> None:
        self._inner = RationalField()

    def zero(self) -> Fraction:
        return self._inner.zero()

    def one(self) -> Fraction:
        return self._inner.one()

    def add(self, left: Fraction, right: Fraction) -> Fraction:
        return self._inner.add(left, right)

    def neg(self, value: Fraction) -> Fraction:
        return self._inner.neg(value)

    def mul(self, left: Fraction, right: Fraction) -> Fraction:
        return self._inner.mul(left, right)

    def contains(self, value: object) -> bool:
        return self._inner.contains(value)

    def equal(self, left: Fraction, right: Fraction) -> bool:
        return self._inner.equal(left, right)

    def inv(self, value: Fraction) -> Fraction:
        return self._inner.inv(value)

    @property
    def characteristic(self) -> int:
        return 0


def test_cauchy_bound_refuses_a_non_ordered_coefficient_field():
    coefficients = UnorderedRationals()
    base = UnivariatePolynomialRing(X, coefficients)
    value = base.sub(
        base.pow(base.generator(0), 2),
        base.constant(coefficients.one()),
    )
    with pytest.raises(RealRootFragmentError) as not_ordered:
        cauchy_bound(base, value)
    assert not_ordered.value.missing == frozenset(
        {"ordered_coefficient_field"}
    )


class ParityField(Field[int]):
    """GF(2) as a test-only field of positive characteristic."""

    def zero(self) -> int:
        return 0

    def one(self) -> int:
        return 1

    def add(self, left: int, right: int) -> int:
        return (left + right) % 2

    def neg(self, value: int) -> int:
        return value

    def mul(self, left: int, right: int) -> int:
        return (left * right) % 2

    def contains(self, value: object) -> bool:
        return value in (0, 1)

    def equal(self, left: int, right: int) -> bool:
        return left == right

    def inv(self, value: int) -> int:
        if value == 0:
            raise ZeroDivisionError("zero has no inverse in GF(2)")
        return 1

    @property
    def characteristic(self) -> int:
        return 2


def test_cauchy_bound_refuses_positive_characteristic():
    base = UnivariatePolynomialRing(SymbolId(3), ParityField())
    with pytest.raises(RealRootFragmentError) as positive:
        cauchy_bound(base, base.generator(0))
    assert positive.value.missing == frozenset({"characteristic_zero_field"})


def test_isolation_of_x_squared_minus_two_returns_two_disjoint_intervals():
    base = ring()
    value = base.sub(
        base.pow(base.generator(0), 2), base.constant(q(2))
    )
    intervals = isolate_real_roots_open(base, value, budget=100)
    assert intervals == ((q(-4), q(0)), (q(0), q(4)))
    assert intervals[0][1] <= intervals[1][0]
    for lower, upper in intervals:
        assert lower < upper
        assert evaluate(base, value, lower) != 0
        assert evaluate(base, value, upper) != 0
        assert count_real_roots_open(base, value, lower, upper) == 1


def test_isolation_of_x_squared_plus_one_is_empty():
    base = ring()
    value = base.add(
        base.pow(base.generator(0), 2), base.constant(q(1))
    )
    assert isolate_real_roots_open(base, value, budget=10) == ()


def test_isolation_of_x_returns_one_interval_containing_zero():
    base = ring()
    intervals = isolate_real_roots_open(
        base, base.generator(0), budget=10
    )
    assert len(intervals) == 1
    lower, upper = intervals[0]
    assert lower < q(0) < upper
    assert evaluate(base, base.generator(0), lower) != 0
    assert evaluate(base, base.generator(0), upper) != 0


def test_isolation_of_a_nonzero_constant_is_empty():
    base = ring()
    assert (
        isolate_real_roots_open(
            base, base.constant(q(7, 3)), budget=10
        )
        == ()
    )


def test_isolation_never_uses_a_root_valued_midpoint():
    base = ring()
    value = base.mul(
        base.generator(0),
        base.sub(
            base.pow(base.generator(0), 2), base.constant(q(2))
        ),
    )
    intervals = isolate_real_roots_open(base, value, budget=200)
    assert len(intervals) == 3
    for lower, upper in intervals:
        assert evaluate(base, value, lower) != 0
        assert evaluate(base, value, upper) != 0
        assert count_real_roots_open(base, value, lower, upper) == 1
    assert all(
        earlier[1] <= later[0]
        for earlier, later in zip(intervals, intervals[1:])
    )


def test_isolation_refuses_zero_and_non_squarefree_polynomials():
    base = ring()
    with pytest.raises(RealRootFragmentError) as zero:
        isolate_real_roots_open(base, base.zero(), budget=10)
    assert zero.value.missing == frozenset({"nonzero_polynomial"})
    repeated = base.pow(
        base.sub(base.generator(0), base.constant(q(1))), 2
    )
    with pytest.raises(RealRootFragmentError) as nonsquare:
        isolate_real_roots_open(base, repeated, budget=10)
    assert nonsquare.value.missing == frozenset({"squarefree_polynomial"})


def test_isolation_reports_budget_exhaustion_instead_of_a_partial_set():
    base = ring()
    value = base.sub(
        base.pow(base.generator(0), 2), base.constant(q(2))
    )
    with pytest.raises(RealRootBudgetError) as exhausted:
        isolate_real_roots_open(base, value, budget=0)
    assert exhausted.value.missing == frozenset(
        {"root_isolation_budget"}
    )


def test_isolation_covers_the_total_sturm_count_for_several_roots():
    base = ring()
    roots = (q(-3), q(0), q(1, 2), q(4))
    value = product_of_linear(base, roots)
    bound = cauchy_bound(base, value)
    intervals = isolate_real_roots_open(base, value, budget=200)
    total = count_real_roots_open(base, value, -bound, bound)
    assert total == len(roots)
    assert len(intervals) == len(roots)
    assert sum(
        count_real_roots_open(base, value, lower, upper)
        for lower, upper in intervals
    ) == total
    for root in roots:
        assert sum(
            1 for lower, upper in intervals if lower < root < upper
        ) == 1
