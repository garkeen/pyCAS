"""Randomized algebraic laws: fields, Euclidean division and polynomial rings."""

import random
from fractions import Fraction

from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

SEED = 20261025

X, Y = SymbolId(1), SymbolId(2)


def random_rational(rng: random.Random) -> Fraction:
    return Fraction(rng.randint(-9, 9), rng.randint(1, 9))


def random_polynomial(
    rng: random.Random,
    ring,
    *,
    generators: int = 1,
    max_degree: int = 4,
    max_terms: int = 5,
):
    value = ring.zero()
    for _ in range(rng.randint(1, max_terms)):
        exponents = tuple(
            rng.randint(0, max_degree) for _ in range(generators)
        )
        coefficient = Fraction(rng.randint(-4, 4), rng.randint(1, 3))
        value = ring.add(value, ring.monomial(exponents, coefficient))
    return value


def test_q_field_laws():
    rng = random.Random(SEED)
    field = RationalField()
    for _ in range(200):
        a, b, c = (random_rational(rng) for _ in range(3))
        assert field.equal(field.add(a, b), field.add(b, a))
        assert field.equal(field.mul(a, b), field.mul(b, a))
        assert field.equal(
            field.add(field.add(a, b), c), field.add(a, field.add(b, c))
        )
        assert field.equal(
            field.mul(field.mul(a, b), c), field.mul(a, field.mul(b, c))
        )
        assert field.equal(
            field.mul(a, field.add(b, c)),
            field.add(field.mul(a, b), field.mul(a, c)),
        )
        assert field.equal(field.add(a, field.zero()), a)
        assert field.equal(field.mul(a, field.one()), a)
        assert field.equal(field.add(a, field.neg(a)), field.zero())
        if not field.is_zero(a):
            assert field.equal(field.mul(a, field.inv(a)), field.one())


def test_z_division_and_gcd_laws():
    rng = random.Random(SEED + 1)
    ring = IntegerRing()
    divisors = [value for value in range(-9, 10) if value]
    for _ in range(200):
        a = rng.randint(-1000, 1000)
        b = rng.choice(divisors)
        quotient, remainder = ring.divmod(a, b)
        assert b * quotient + remainder == a
        assert abs(remainder) < abs(b)
        divisor = ring.gcd(a, b)
        assert divisor >= 0
        if divisor:
            assert a % divisor == 0
            assert b % divisor == 0


def test_polynomial_ring_laws_and_derivative_rules():
    rng = random.Random(SEED + 2)
    ring = UnivariatePolynomialRing(X, RationalField())
    for _ in range(100):
        p = random_polynomial(rng, ring)
        q = random_polynomial(rng, ring)
        r = random_polynomial(rng, ring)
        assert ring.equal(ring.add(p, q), ring.add(q, p))
        assert ring.equal(ring.mul(p, q), ring.mul(q, p))
        assert ring.equal(
            ring.add(ring.add(p, q), r), ring.add(p, ring.add(q, r))
        )
        assert ring.equal(
            ring.mul(ring.mul(p, q), r), ring.mul(p, ring.mul(q, r))
        )
        assert ring.equal(
            ring.mul(p, ring.add(q, r)),
            ring.add(ring.mul(p, q), ring.mul(p, r)),
        )
        assert ring.equal(ring.add(p, ring.zero()), p)
        assert ring.equal(ring.mul(p, ring.one()), p)
        assert ring.equal(ring.sub(p, q), ring.add(p, ring.neg(q)))
        assert ring.equal(ring.pow(p, 2), ring.mul(p, p))

        dp = ring.derivative(p, 0)
        dq = ring.derivative(q, 0)
        assert ring.equal(ring.derivative(ring.add(p, q), 0), ring.add(dp, dq))
        assert ring.equal(
            ring.derivative(ring.mul(p, q), 0),
            ring.add(ring.mul(dp, q), ring.mul(p, dq)),
        )


def test_multivariate_derivatives_obey_the_same_rules():
    rng = random.Random(SEED + 3)
    ring = PolynomialRing((X, Y), RationalField())
    for _ in range(80):
        p = random_polynomial(rng, ring, generators=2)
        q = random_polynomial(rng, ring, generators=2)
        index = rng.randrange(2)
        dp = ring.derivative(p, index)
        dq = ring.derivative(q, index)
        assert ring.equal(ring.derivative(ring.add(p, q), index), ring.add(dp, dq))
        assert ring.equal(
            ring.derivative(ring.mul(p, q), index),
            ring.add(ring.mul(dp, q), ring.mul(p, dq)),
        )


def test_rational_function_field_laws():
    rng = random.Random(SEED + 4)
    polynomials = UnivariatePolynomialRing(X, RationalField())
    field = RationalFunctionField(polynomials)

    def nonzero():
        while True:
            value = random_polynomial(rng, polynomials)
            if not value.is_zero():
                return value

    for _ in range(40):
        a = field.fraction(random_polynomial(rng, polynomials), nonzero())
        b = field.fraction(random_polynomial(rng, polynomials), nonzero())
        c = field.fraction(random_polynomial(rng, polynomials), nonzero())
        assert field.equal(field.add(a, b), field.add(b, a))
        assert field.equal(field.mul(a, b), field.mul(b, a))
        assert field.equal(
            field.add(field.add(a, b), c), field.add(a, field.add(b, c))
        )
        assert field.equal(
            field.mul(field.mul(a, b), c), field.mul(a, field.mul(b, c))
        )
        assert field.equal(
            field.mul(a, field.add(b, c)),
            field.add(field.mul(a, b), field.mul(a, c)),
        )
        assert field.equal(field.add(a, field.neg(a)), field.zero())
        if not field.is_zero(a):
            assert field.equal(field.mul(a, field.inv(a)), field.one())
        assert field.equal(
            field.derivative(field.mul(a, b)),
            field.add(
                field.mul(field.derivative(a), b),
                field.mul(a, field.derivative(b)),
            ),
        )
