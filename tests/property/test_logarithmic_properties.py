"""Fixed-seed properties of rational-residue logarithmic integration."""

import random
from fractions import Fraction
from math import isqrt

import pytest

from cas.algebra.factorization import FactorizationBudget
from cas.algebra.logarithmic_integration import (
    LogarithmicIntegrationBudget,
    LogarithmicIntegrationBudgetError,
    LogarithmicIntegrationFragmentError,
    RationalLogIntegral,
    rational_log_integral,
)
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

SEED = 20261112
X = SymbolId(8201)
Q = RationalField()
QX = UnivariatePolynomialRing(X, Q)
FIELD = RationalFunctionField(QX)


def poly(*coefficients: Fraction) -> Polynomial[Fraction]:
    return QX.sum(
        QX.monomial((index,), coefficient)
        for index, coefficient in enumerate(coefficients)
    )


def x() -> Polynomial[Fraction]:
    return QX.generator(0)


def candidate_factors() -> tuple[Polynomial[Fraction], ...]:
    linear = tuple(
        poly(Fraction(-root), Fraction(1)) for root in range(-3, 4)
    )
    quadratic = (
        poly(Fraction(1), Fraction(0), Fraction(1)),
        poly(Fraction(2), Fraction(0), Fraction(1)),
        poly(Fraction(1), Fraction(1), Fraction(1)),
        poly(Fraction(1), Fraction(-1), Fraction(1)),
    )
    return linear + quadratic


def random_factors(
    rng: random.Random,
    count: int,
) -> tuple[Polynomial[Fraction], ...]:
    """Pairwise-coprime monic squarefree factors of total degree at most three."""
    candidates = list(candidate_factors())
    rng.shuffle(candidates)
    chosen: list[Polynomial[Fraction]] = []
    degree = 0
    for candidate in candidates:
        candidate_degree = QX.degree(candidate, 0)
        if degree + candidate_degree > 3:
            continue
        if any(
            not QX.is_one(QX.gcd(candidate, other)) for other in chosen
        ):
            continue
        chosen.append(candidate)
        degree += candidate_degree
        if len(chosen) == count:
            return tuple(chosen)
    return tuple(chosen)


def random_coefficients(
    rng: random.Random,
    count: int,
) -> tuple[Fraction, ...]:
    pool = sorted(
        {
            Fraction(numerator, denominator)
            for numerator in (-3, -2, -1, 1, 2, 3)
            for denominator in (1, 2, 3)
        }
    )
    rng.shuffle(pool)
    return tuple(pool[:count])


def log_derivative(coefficient: Fraction, argument: Polynomial[Fraction]) -> RationalFunction[Fraction]:
    return FIELD.fraction(
        QX.mul(QX.constant(coefficient), QX.derivative(argument, 0)),
        argument,
    )


def identity_rhs(result: RationalLogIntegral) -> RationalFunction[Fraction]:
    total = FIELD.derivative(result.polynomial_part)
    for term in result.log_terms:
        total = FIELD.add(
            total, log_derivative(term.coefficient, term.argument)
        )
    return total


def random_polynomial(rng: random.Random, count: int) -> Polynomial[Fraction]:
    return poly(
        *(
            Fraction(rng.randint(-2, 2), rng.randint(1, 2))
            for _ in range(count)
        )
    )


def test_random_rational_log_derivative_sums_are_integrated():
    rng = random.Random(SEED)
    for _ in range(40):
        count = rng.randint(1, 3)
        factors = random_factors(rng, count)
        if not factors:
            continue
        coefficients = random_coefficients(rng, len(factors))
        value = FIELD.derivative(
            FIELD.of_polynomial(random_polynomial(rng, rng.randint(1, 3)))
        )
        for coefficient, argument in zip(coefficients, factors):
            value = FIELD.add(
                value, log_derivative(coefficient, argument)
            )
        result = rational_log_integral(FIELD, value)
        assert FIELD.equal(identity_rhs(result), value)
        assert len(result.log_terms) == len(factors)
        by_coefficient = {
            term.coefficient: term.argument for term in result.log_terms
        }
        assert set(by_coefficient) == set(coefficients)
        for coefficient, argument in zip(coefficients, factors):
            assert QX.equal(by_coefficient[coefficient], argument)
        seen: list[Polynomial[Fraction]] = []
        for term in result.log_terms:
            degree = QX.degree(term.argument, 0)
            assert degree >= 1
            assert QX.coefficients.is_one(
                QX.coefficient(term.argument, (degree,))
            )
            assert QX.is_one(
                QX.gcd(term.argument, QX.derivative(term.argument, 0))
            )
            for other in seen:
                assert QX.is_one(QX.gcd(term.argument, other))
            seen.append(term.argument)


def test_x_over_x_squared_plus_a_is_always_integrated():
    for a in (Fraction(1), Fraction(2), Fraction(3, 2), Fraction(1, 4), Fraction(9)):
        denominator = poly(a, Fraction(0), Fraction(1))
        value = FIELD.fraction(x(), denominator)
        result = rational_log_integral(FIELD, value)
        assert len(result.log_terms) == 1
        term = result.log_terms[0]
        assert term.coefficient == Fraction(1, 2)
        assert QX.equal(term.argument, denominator)
        assert FIELD.equal(identity_rhs(result), value)


def is_rational_square(value: Fraction) -> bool:
    if value < 0:
        return False
    numerator = isqrt(value.numerator)
    denominator = isqrt(value.denominator)
    return numerator * numerator == value.numerator and (
        denominator * denominator == value.denominator
    )


def isqrt_square(value: Fraction) -> Fraction:
    return Fraction(isqrt(value.numerator), isqrt(value.denominator))


def test_one_over_x_squared_minus_a_is_accepted_exactly_for_square_a():
    for a in (
        Fraction(1),
        Fraction(4),
        Fraction(9),
        Fraction(1, 4),
        Fraction(1, 9),
        Fraction(2),
        Fraction(3),
        Fraction(5, 4),
    ):
        denominator = poly(-a, Fraction(0), Fraction(1))
        value = FIELD.fraction(QX.one(), denominator)
        if is_rational_square(a):
            result = rational_log_integral(FIELD, value)
            assert FIELD.equal(identity_rhs(result), value)
            assert len(result.log_terms) == 2
            assert {term.coefficient for term in result.log_terms} == {
                Fraction(-1, 2) / isqrt_square(a),
                Fraction(1, 2) / isqrt_square(a),
            }
        else:
            with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
                rational_log_integral(FIELD, value)
            assert caught.value.missing == frozenset(
                {"rational_residues", "algebraic_logarithmic_part"}
            )


def test_one_over_x_squared_plus_positive_a_has_irrational_residues():
    # R(y) = y**2 + 1/(4a) has the non-real roots +-i/(2*sqrt(a)), so the
    # residue polynomial has no rational root for every positive rational a.
    for a in (Fraction(1), Fraction(2), Fraction(1, 4), Fraction(9, 5)):
        denominator = poly(a, Fraction(0), Fraction(1))
        with pytest.raises(LogarithmicIntegrationFragmentError):
            rational_log_integral(FIELD, FIELD.fraction(QX.one(), denominator))


def test_budget_exhaustion_never_returns_a_partial_integral():
    value = FIELD.fraction(
        QX.one(), poly(Fraction(-1), Fraction(0), Fraction(1))
    )
    with pytest.raises(LogarithmicIntegrationBudgetError) as caught:
        rational_log_integral(
            FIELD, value, LogarithmicIntegrationBudget(max_degree=1)
        )
    assert caught.value.missing == frozenset({"max_degree"})
    with pytest.raises(LogarithmicIntegrationBudgetError) as caught:
        rational_log_integral(
            FIELD,
            value,
            LogarithmicIntegrationBudget(
                factorization=FactorizationBudget(max_prime_trials=0)
            ),
        )
    assert caught.value.missing == frozenset({"factorization_budget"})
