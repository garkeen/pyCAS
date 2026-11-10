"""Randomized laws for the exact Sturm real-root count."""

import random
from fractions import Fraction

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.algebra.real_roots import count_real_roots_open
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


def evaluate(
    base: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
    point: Fraction,
) -> Fraction:
    coefficients = base.coefficients
    result = coefficients.zero()
    for exponent in range(base.degree(value, 0), -1, -1):
        result = coefficients.add(
            coefficients.mul(result, point),
            base.coefficient(value, (exponent,)),
        )
    return result


def rebuilt_chain(
    base: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> tuple[Polynomial[Fraction], ...]:
    if base.is_constant(value):
        return (value,)
    chain = [value, base.derivative(value, 0)]
    while not base.is_constant(chain[-1]):
        _, remainder = base.divmod(chain[-2], chain[-1])
        following = base.neg(remainder)
        if following.is_zero():
            break
        chain.append(following)
    assert base.is_constant(chain[-1])
    return tuple(chain)


def variations(
    base: UnivariatePolynomialRing[Fraction],
    chain: tuple[Polynomial[Fraction], ...],
    point: Fraction,
) -> int:
    result = 0
    previous = 0
    for entry in chain:
        sign = base.coefficients.sign(evaluate(base, entry, point))
        if sign == 0:
            continue
        if previous != 0 and sign != previous:
            result += 1
        previous = sign
    return result


def count_from_rebuilt_chain(
    base: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
    lower: Fraction,
    upper: Fraction,
) -> int:
    chain = rebuilt_chain(base, value)
    correction = 1 if evaluate(base, value, upper) == 0 else 0
    return (
        variations(base, chain, lower)
        - variations(base, chain, upper)
        - correction
    )


def random_roots(rng: random.Random) -> tuple[Fraction, ...]:
    roots = {
        Fraction(rng.randint(-8, 8), rng.randint(1, 5))
        for _ in range(rng.randint(1, 5))
    }
    return tuple(sorted(roots))


def random_split(
    rng: random.Random,
) -> tuple[Fraction, Fraction, Fraction]:
    lower, middle, upper = sorted(
        Fraction(value) for value in rng.sample(range(-10, 11), 3)
    )
    return lower, middle, upper


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


def test_count_matches_the_known_roots_of_a_factored_polynomial():
    rng = random.Random(SEED)
    base = ring()
    for _ in range(80):
        roots = random_roots(rng)
        value = product_of_linear(base, roots)
        lower, _, upper = random_split(rng)
        expected = sum(1 for root in roots if lower < root < upper)
        assert (
            count_real_roots_open(base, value, lower, upper) == expected
        )


def test_count_is_additive_across_a_split_endpoint():
    rng = random.Random(SEED + 1)
    base = ring()
    for _ in range(60):
        roots = random_roots(rng)
        value = product_of_linear(base, roots)
        lower, middle, upper = random_split(rng)
        correction = 1 if evaluate(base, value, middle) == 0 else 0
        assert count_real_roots_open(
            base, value, lower, upper
        ) == (
            count_real_roots_open(base, value, lower, middle)
            + count_real_roots_open(base, value, middle, upper)
            + correction
        )


def test_count_is_invariant_under_nonzero_scaling():
    rng = random.Random(SEED + 2)
    base = ring()
    scales = (Fraction(2), Fraction(-3), Fraction(5, 7), Fraction(-1, 4))
    for _ in range(60):
        value = product_of_linear(base, random_roots(rng))
        lower, _, upper = random_split(rng)
        expected = count_real_roots_open(base, value, lower, upper)
        for scale in scales:
            scaled = base.mul(base.constant(scale), value)
            assert (
                count_real_roots_open(base, scaled, lower, upper)
                == expected
            )


def test_count_agrees_with_an_independently_rebuilt_chain():
    rng = random.Random(SEED + 3)
    base = ring()
    for _ in range(60):
        value = random_squarefree_polynomial(rng, base)
        lower, _, upper = random_split(rng)
        expected = count_from_rebuilt_chain(
            base, value, lower, upper
        )
        assert (
            count_real_roots_open(base, value, lower, upper) == expected
        )
