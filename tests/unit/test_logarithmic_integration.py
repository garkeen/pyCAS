"""Rational-residue logarithmic integration over ``Q(x)``."""

from fractions import Fraction

import pytest

from cas.algebra.factorization import FactorizationBudget
from cas.algebra.logarithmic_integration import (
    LogarithmicIntegrationBudget,
    LogarithmicIntegrationBudgetError,
    LogarithmicIntegrationFragmentError,
    RationalLogIntegral,
    RationalLogTerm,
    rational_log_integral,
    residue_polynomial,
)
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(8101)
OTHER_X = SymbolId(8102)
Q = RationalField()
QX = UnivariatePolynomialRing(X, Q)
OTHER_QX = UnivariatePolynomialRing(OTHER_X, Q)
FIELD = RationalFunctionField(QX)
OTHER_FIELD = RationalFunctionField(OTHER_QX)


def poly(*coefficients: Fraction) -> Polynomial[Fraction]:
    return QX.sum(
        QX.monomial((index,), coefficient)
        for index, coefficient in enumerate(coefficients)
    )


def other_poly(*coefficients: Fraction) -> Polynomial[Fraction]:
    return OTHER_QX.sum(
        OTHER_QX.monomial((index,), coefficient)
        for index, coefficient in enumerate(coefficients)
    )


def x() -> Polynomial[Fraction]:
    return QX.generator(0)


def coefficients(value: Polynomial[Fraction]) -> tuple[Fraction, ...]:
    ring = value.owner
    return tuple(
        ring.coefficient(value, (index,))
        for index in range(ring.degree(value, 0) + 1)
    )


def identity_rhs(result: RationalLogIntegral) -> RationalFunction[Fraction]:
    total = FIELD.derivative(result.polynomial_part)
    for term in result.log_terms:
        total = FIELD.add(
            total,
            FIELD.fraction(
                QX.mul(
                    QX.constant(term.coefficient),
                    QX.derivative(term.argument, 0),
                ),
                term.argument,
            ),
        )
    return total


def assert_identity(
    result: RationalLogIntegral, value: RationalFunction[Fraction]
) -> None:
    assert FIELD.equal(identity_rhs(result), value)


def test_zero_has_a_zero_polynomial_part_and_no_log_terms():
    result = rational_log_integral(FIELD, FIELD.zero())
    assert FIELD.equal(result.polynomial_part, FIELD.zero())
    assert result.log_terms == ()
    assert_identity(result, FIELD.zero())


def test_a_constant_integrates_to_a_linear_polynomial():
    value = FIELD.of_polynomial(QX.constant(Fraction(5)))
    result = rational_log_integral(FIELD, value)
    assert FIELD.equal(
        result.polynomial_part, FIELD.of_polynomial(poly(Fraction(0), Fraction(5)))
    )
    assert result.log_terms == ()
    assert_identity(result, value)


def test_a_polynomial_integrates_term_by_term():
    value = FIELD.of_polynomial(poly(Fraction(3), Fraction(0), Fraction(1)))
    result = rational_log_integral(FIELD, value)
    expected = poly(Fraction(0), Fraction(3), Fraction(0), Fraction(1, 3))
    assert FIELD.equal(result.polynomial_part, FIELD.of_polynomial(expected))
    assert result.log_terms == ()
    assert_identity(result, value)


def test_one_over_x_emits_the_unit_logarithm():
    value = FIELD.fraction(QX.one(), x())
    result = rational_log_integral(FIELD, value)
    assert FIELD.equal(result.polynomial_part, FIELD.zero())
    assert len(result.log_terms) == 1
    term = result.log_terms[0]
    assert term.coefficient == Fraction(1)
    assert QX.equal(term.argument, x())
    assert_identity(result, value)


def test_one_over_x_squared_minus_one_splits_into_two_logarithms():
    value = FIELD.fraction(
        QX.one(), poly(Fraction(-1), Fraction(0), Fraction(1))
    )
    result = rational_log_integral(FIELD, value)
    assert FIELD.equal(result.polynomial_part, FIELD.zero())
    assert [term.coefficient for term in result.log_terms] == [
        Fraction(-1, 2),
        Fraction(1, 2),
    ]
    assert QX.equal(result.log_terms[0].argument, poly(Fraction(1), Fraction(1)))
    assert QX.equal(result.log_terms[1].argument, poly(Fraction(-1), Fraction(1)))
    assert_identity(result, value)


def test_two_x_over_x_squared_plus_one_is_a_single_unit_logarithm():
    value = FIELD.fraction(
        poly(Fraction(0), Fraction(2)),
        poly(Fraction(1), Fraction(0), Fraction(1)),
    )
    result = rational_log_integral(FIELD, value)
    assert len(result.log_terms) == 1
    term = result.log_terms[0]
    assert term.coefficient == Fraction(1)
    assert QX.equal(
        term.argument, poly(Fraction(1), Fraction(0), Fraction(1))
    )
    assert_identity(result, value)


def test_x_over_x_squared_plus_one_has_the_half_residue():
    value = FIELD.fraction(
        x(), poly(Fraction(1), Fraction(0), Fraction(1))
    )
    result = rational_log_integral(FIELD, value)
    assert len(result.log_terms) == 1
    term = result.log_terms[0]
    assert term.coefficient == Fraction(1, 2)
    assert QX.equal(
        term.argument, poly(Fraction(1), Fraction(0), Fraction(1))
    )
    assert_identity(result, value)


def test_a_squared_squarefree_denominator_uses_hermite_then_logarithms():
    denominator = poly(Fraction(-1), Fraction(0), Fraction(1))
    value = FIELD.fraction(QX.one(), QX.pow(denominator, 2))
    result = rational_log_integral(FIELD, value)
    assert FIELD.equal(
        result.polynomial_part,
        FIELD.fraction(
            QX.neg(x()),
            QX.mul(QX.constant(Fraction(2)), denominator),
        ),
    )
    assert [term.coefficient for term in result.log_terms] == [
        Fraction(-1, 4),
        Fraction(1, 4),
    ]
    assert QX.equal(
        result.log_terms[0].argument, poly(Fraction(-1), Fraction(1))
    )
    assert QX.equal(
        result.log_terms[1].argument, poly(Fraction(1), Fraction(1))
    )
    assert_identity(result, value)


def test_a_repeated_linear_pole_is_absorbed_by_hermite():
    factor = poly(Fraction(-1), Fraction(1))
    value = FIELD.fraction(QX.one(), QX.pow(factor, 2))
    result = rational_log_integral(FIELD, value)
    assert FIELD.equal(
        result.polynomial_part, FIELD.fraction(QX.neg(QX.one()), factor)
    )
    assert result.log_terms == ()
    assert_identity(result, value)


def test_an_improper_fraction_integrates_its_polynomial_part():
    value = FIELD.fraction(
        poly(Fraction(1), Fraction(0), Fraction(1)),
        poly(Fraction(-1), Fraction(0), Fraction(1)),
    )
    result = rational_log_integral(FIELD, value)
    assert FIELD.equal(result.polynomial_part, FIELD.of_polynomial(x()))
    assert [term.coefficient for term in result.log_terms] == [
        Fraction(-1),
        Fraction(1),
    ]
    assert QX.equal(
        result.log_terms[0].argument, poly(Fraction(1), Fraction(1))
    )
    assert QX.equal(
        result.log_terms[1].argument, poly(Fraction(-1), Fraction(1))
    )
    assert_identity(result, value)


def test_residue_polynomial_values_are_monic():
    cases = (
        (
            poly(Fraction(-1), Fraction(0), Fraction(1)),
            QX.one(),
            (Fraction(-1, 4), Fraction(0), Fraction(1)),
        ),
        (
            poly(Fraction(1), Fraction(0), Fraction(1)),
            QX.one(),
            (Fraction(1, 4), Fraction(0), Fraction(1)),
        ),
        (
            poly(Fraction(1), Fraction(0), Fraction(1)),
            poly(Fraction(0), Fraction(2)),
            (Fraction(1), Fraction(-2), Fraction(1)),
        ),
    )
    for denominator, numerator, expected in cases:
        residue = residue_polynomial(QX, denominator, numerator)
        assert coefficients(residue) == expected
        assert isinstance(residue.owner, UnivariatePolynomialRing)
        assert isinstance(residue.owner.coefficients, RationalField)
        assert residue.owner.generators != QX.generators


def test_residue_polynomial_of_the_constant_denominator_is_one():
    residue = residue_polynomial(QX, QX.one(), QX.zero())
    assert residue.owner.degree(residue, 0) == 0
    assert residue.owner.is_one(residue)


@pytest.mark.parametrize(
    "denominator",
    (
        poly(Fraction(1), Fraction(0), Fraction(1)),
        poly(Fraction(-1), Fraction(0), Fraction(0), Fraction(1)),
        poly(
            Fraction(1),
            Fraction(0),
            Fraction(0),
            Fraction(0),
            Fraction(1),
        ),
        QX.pow(poly(Fraction(1), Fraction(0), Fraction(1)), 2),
    ),
)
def test_irrational_residues_are_refused_without_a_partial_result(
    denominator: Polynomial[Fraction],
):
    value = FIELD.fraction(QX.one(), denominator)
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        rational_log_integral(FIELD, value)
    assert caught.value.missing == frozenset(
        {"rational_residues", "algebraic_logarithmic_part"}
    )
    assert caught.value.detail


def test_residue_polynomial_rejects_a_non_squarefree_denominator():
    denominator = QX.pow(poly(Fraction(-1), Fraction(1)), 2)
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        residue_polynomial(QX, denominator, QX.one())
    assert caught.value.missing == frozenset({"squarefree_denominator"})


def test_residue_polynomial_rejects_an_improper_fraction():
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        residue_polynomial(
            QX,
            poly(Fraction(-1), Fraction(0), Fraction(1)),
            poly(Fraction(0), Fraction(0), Fraction(0), Fraction(1)),
        )
    assert caught.value.missing == frozenset({"proper_fraction"})


def test_residue_polynomial_rejects_a_non_coprime_fraction():
    denominator = poly(Fraction(-1), Fraction(0), Fraction(1))
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        residue_polynomial(
            QX, denominator, poly(Fraction(-1), Fraction(1))
        )
    assert caught.value.missing == frozenset({"coprime_fraction"})


def test_residue_polynomial_rejects_a_zero_denominator():
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        residue_polynomial(QX, QX.zero(), QX.one())
    assert caught.value.missing == frozenset({"nonzero_denominator"})


def test_residue_polynomial_rejects_a_non_monic_denominator():
    denominator = QX.mul(QX.constant(Fraction(2)), poly(Fraction(-1), Fraction(0), Fraction(1)))
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        residue_polynomial(QX, denominator, QX.one())
    assert caught.value.missing == frozenset({"monic_denominator"})


def test_residue_polynomial_rejects_a_foreign_ring_operand():
    denominator = poly(Fraction(-1), Fraction(0), Fraction(1))
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        residue_polynomial(QX, denominator, other_poly(Fraction(1)))
    assert caught.value.missing == frozenset({"ring_ownership"})
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        residue_polynomial(
            QX, other_poly(Fraction(-1), Fraction(0), Fraction(1)), QX.one()
        )
    assert caught.value.missing == frozenset({"ring_ownership"})


def test_a_non_q_field_is_refused_by_the_integrator():
    from cas.algebra.finite_field import PrimeField

    prime_ring = UnivariatePolynomialRing(X, PrimeField(5))
    prime_field = RationalFunctionField(prime_ring)
    with pytest.raises(TypeError):
        rational_log_integral(prime_field, prime_field.zero())


def test_a_foreign_field_value_is_refused():
    with pytest.raises(LogarithmicIntegrationFragmentError) as caught:
        rational_log_integral(FIELD, OTHER_FIELD.zero())
    assert caught.value.missing == frozenset({"field_ownership"})


def test_the_degree_budget_bounds_the_input_denominator():
    value = FIELD.fraction(
        QX.one(), poly(Fraction(-1), Fraction(0), Fraction(1))
    )
    budget = LogarithmicIntegrationBudget(max_degree=1)
    with pytest.raises(LogarithmicIntegrationBudgetError) as caught:
        rational_log_integral(FIELD, value, budget)
    assert caught.value.missing == frozenset({"max_degree"})
    with pytest.raises(LogarithmicIntegrationBudgetError) as caught:
        residue_polynomial(
            QX,
            poly(Fraction(-1), Fraction(0), Fraction(1)),
            QX.one(),
            budget,
        )
    assert caught.value.missing == frozenset({"max_degree"})


def test_the_degree_budget_bounds_the_input_numerator():
    value = FIELD.fraction(
        QX.monomial((2,), Fraction(1)), QX.one()
    )
    budget = LogarithmicIntegrationBudget(max_degree=1)
    with pytest.raises(LogarithmicIntegrationBudgetError) as caught:
        rational_log_integral(FIELD, value, budget)
    assert caught.value.missing == frozenset({"max_degree"})


def test_factorization_budget_exhaustion_preserves_the_missing_tokens():
    value = FIELD.fraction(
        QX.one(), poly(Fraction(-1), Fraction(0), Fraction(1))
    )
    budget = LogarithmicIntegrationBudget(
        factorization=FactorizationBudget(max_prime_trials=0)
    )
    with pytest.raises(LogarithmicIntegrationBudgetError) as caught:
        rational_log_integral(FIELD, value, budget)
    assert caught.value.missing == frozenset({"factorization_budget"})


def test_the_budget_rejects_booleans_negatives_and_wrong_nested_types():
    with pytest.raises(TypeError):
        LogarithmicIntegrationBudget(max_degree=True)
    with pytest.raises(ValueError):
        LogarithmicIntegrationBudget(max_degree=-1)
    with pytest.raises(TypeError):
        LogarithmicIntegrationBudget(factorization=object())  # type: ignore[arg-type]


def test_a_log_term_requires_a_nonzero_rational_coefficient():
    with pytest.raises(ValueError):
        RationalLogTerm(Fraction(0), x())
    with pytest.raises(TypeError):
        RationalLogTerm(1, x())  # type: ignore[arg-type]


def test_a_log_term_requires_a_monic_squarefree_nonconstant_argument():
    with pytest.raises(ValueError):
        RationalLogTerm(Fraction(1), QX.zero())
    with pytest.raises(ValueError):
        RationalLogTerm(Fraction(1), QX.one())
    with pytest.raises(ValueError):
        RationalLogTerm(
            Fraction(1),
            QX.mul(QX.constant(Fraction(2)), poly(Fraction(1), Fraction(1))),
        )
    with pytest.raises(ValueError):
        RationalLogTerm(
            Fraction(1), QX.pow(poly(Fraction(-1), Fraction(1)), 2)
        )


def test_the_integral_record_rejects_duplicate_coefficients():
    with pytest.raises(ValueError):
        RationalLogIntegral(
            FIELD.zero(),
            (
                RationalLogTerm(Fraction(1), x()),
                RationalLogTerm(Fraction(1), poly(Fraction(1), Fraction(1))),
            ),
        )


def test_the_integral_record_rejects_non_coprime_arguments():
    product = QX.mul(x(), poly(Fraction(1), Fraction(1)))
    with pytest.raises(ValueError):
        RationalLogIntegral(
            FIELD.zero(),
            (
                RationalLogTerm(Fraction(1), product),
                RationalLogTerm(Fraction(2), poly(Fraction(1), Fraction(1))),
            ),
        )


def test_the_integral_record_rejects_foreign_ring_arguments():
    with pytest.raises(ValueError):
        RationalLogIntegral(
            FIELD.zero(),
            (RationalLogTerm(Fraction(1), other_poly(Fraction(0), Fraction(1))),),
        )


def test_the_integral_record_sorts_terms_deterministically():
    early = RationalLogTerm(Fraction(-1), poly(Fraction(1), Fraction(1)))
    late = RationalLogTerm(Fraction(1), poly(Fraction(-1), Fraction(1)))
    record = RationalLogIntegral(FIELD.zero(), (late, early))
    assert record.log_terms == (early, late)
    assert record.log_terms[0].coefficient == Fraction(-1)


def test_the_integral_record_rejects_a_non_q_field():
    from cas.algebra.finite_field import PrimeField

    prime_field = RationalFunctionField(
        UnivariatePolynomialRing(X, PrimeField(5))
    )
    with pytest.raises(TypeError):
        RationalLogIntegral(prime_field.zero(), ())
