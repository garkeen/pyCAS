"""Randomized laws for exact open real-root isolation."""

import random
from fractions import Fraction

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.algebra.real_roots import (
    cauchy_bound,
    count_real_roots_open,
    evaluate,
    isolate_real_roots_open,
)
from cas.foundation.ids import SymbolId

SEED = 20261110
X = SymbolId(1)


def ring() -> UnivariatePolynomialRing[Fraction]:
    return UnivariatePolynomialRing(X, RationalField())


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


def random_roots(rng: random.Random) -> tuple[Fraction, ...]:
    roots = {
        Fraction(rng.randint(-10, 10), rng.randint(1, 6))
        for _ in range(rng.randint(1, 5))
    }
    return tuple(sorted(roots))


def random_squarefree_polynomial(
    rng: random.Random,
    base: UnivariatePolynomialRing[Fraction],
) -> Polynomial[Fraction]:
    value = base.zero()
    for _ in range(rng.randint(1, 5)):
        degree = rng.randint(1, 4)
        coefficient = Fraction(rng.randint(-6, 6), rng.randint(1, 3))
        value = base.add(
            value, base.monomial((degree,), coefficient)
        )
    if base.is_constant(value):
        return base.generator(0)
    part = base.squarefree_part(value)
    if base.is_constant(part):
        return base.generator(0)
    return part


def assert_valid_isolation(
    base: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> tuple[tuple[Fraction, Fraction], ...]:
    bound = cauchy_bound(base, value)
    intervals = isolate_real_roots_open(base, value, budget=2048)
    total = count_real_roots_open(base, value, -bound, bound)
    assert sum(
        count_real_roots_open(base, value, lower, upper)
        for lower, upper in intervals
    ) == total
    assert all(lower < upper for lower, upper in intervals)
    assert all(
        earlier[1] <= later[0]
        for earlier, later in zip(intervals, intervals[1:])
    )
    for lower, upper in intervals:
        assert evaluate(base, value, lower) != 0
        assert evaluate(base, value, upper) != 0
        assert count_real_roots_open(base, value, lower, upper) == 1
    return intervals


def test_isolation_covers_every_known_root_exactly_once():
    rng = random.Random(SEED)
    base = ring()
    for _ in range(60):
        roots = random_roots(rng)
        value = product_of_linear(base, roots)
        bound = cauchy_bound(base, value)
        assert all(abs(root) < bound for root in roots)
        intervals = assert_valid_isolation(base, value)
        assert len(intervals) == len(roots)
        for root in roots:
            assert sum(
                1 for lower, upper in intervals if lower < root < upper
            ) == 1


def test_isolation_of_random_squarefree_polynomials_is_complete():
    rng = random.Random(SEED + 1)
    base = ring()
    for _ in range(50):
        value = random_squarefree_polynomial(rng, base)
        intervals = assert_valid_isolation(base, value)
        bound = cauchy_bound(base, value)
        radius = bound + 1
        for lower, upper in intervals:
            assert -radius <= lower and upper <= radius


def test_isolation_is_invariant_under_nonzero_scaling():
    rng = random.Random(SEED + 2)
    base = ring()
    scales = (Fraction(2), Fraction(-3), Fraction(5, 7))
    for _ in range(40):
        value = product_of_linear(base, random_roots(rng))
        expected_total = count_real_roots_open(
            base, value, -cauchy_bound(base, value), cauchy_bound(base, value)
        )
        for scale in scales:
            scaled = base.mul(base.constant(scale), value)
            intervals = assert_valid_isolation(base, scaled)
            assert (
                sum(
                    count_real_roots_open(base, scaled, lower, upper)
                    for lower, upper in intervals
                )
                == expected_total
            )
