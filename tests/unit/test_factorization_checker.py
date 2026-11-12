"""The independent `HasFactorization` checker over a univariate Q[x] ring."""

from dataclasses import replace
from fractions import Fraction

import pytest
from factorization_support import (
    FactorizationBundle,
    FactorizationSetup,
    check_bundle,
    factorization_setup,
    make_bundle,
    make_checker,
    make_problem,
    make_raw_bundle,
    render,
    valid_bundle,
    variable,
)
from support import (
    head_app,
    proposition_in,
    structural,
    verification_context,
)

from cas.algebra.factorization import hensel_witness_for_radical
from cas.algebra.integer_polynomial import rational_polynomial_form
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Unverified,
    Verified,
)
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ResultLanguage,
    VariableRoles,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.algebra.factorization_checker import FactorizationChecker
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
    HenselIrreducibilityWitness,
    factorization_factor_set,
    factorization_product_term,
)
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.syntax import term as T


def ring(setup: FactorizationSetup):
    return setup.runtime.ring


def generator(setup: FactorizationSetup) -> Polynomial[Fraction]:
    return ring(setup).generator(0)


def polynomial(
    setup: FactorizationSetup,
    terms: tuple[tuple[int, Fraction], ...],
) -> Polynomial[Fraction]:
    actual = ring(setup)
    return actual.sum(
        actual.monomial((exponent,), coefficient)
        for exponent, coefficient in terms
    )


def x_squared_minus_one(setup):
    return ring(setup).sub(
        ring(setup).pow(generator(setup), 2), ring(setup).one()
    )


def x_fourth_plus_one(setup):
    return ring(setup).add(
        ring(setup).pow(generator(setup), 4), ring(setup).one()
    )


def entries_of(
    setup: FactorizationSetup,
    pairs: tuple[tuple[Polynomial[Fraction], int], ...],
) -> tuple[tuple[T.Term, int], ...]:
    return tuple(
        (render(setup, value), multiplicity)
        for value, multiplicity in pairs
    )


def witness_for(
    setup: FactorizationSetup,
    radical: Polynomial[Fraction],
):
    """Build honest lifted values, terms and a structural witness."""
    actual_ring = ring(setup)
    lift = hensel_witness_for_radical(actual_ring, radical)
    values = tuple(
        rational_polynomial_form(actual_ring, factor)
        for factor in lift.lifted
    )
    terms = tuple(render(setup, value) for value in values)
    witness = HenselIrreducibilityWitness(
        lift.prime, lift.precision, terms
    )
    return lift, values, terms, witness


def assert_verified(
    setup: FactorizationSetup, bundle: FactorizationBundle
) -> None:
    outcome = check_bundle(setup, bundle)
    assert isinstance(outcome, Verified), outcome
    assert outcome.checked == (bundle.proposition,)


def assert_invalid(
    setup: FactorizationSetup,
    bundle: FactorizationBundle,
    **kwargs: object,
) -> InvalidEvidence:
    outcome = check_bundle(setup, bundle, **kwargs)  # type: ignore[arg-type]
    assert isinstance(outcome, InvalidEvidence), outcome
    return outcome


def assert_refuted(
    setup: FactorizationSetup,
    bundle: FactorizationBundle,
    **kwargs: object,
) -> Refuted:
    outcome = check_bundle(setup, bundle, **kwargs)  # type: ignore[arg-type]
    assert isinstance(outcome, Refuted), outcome
    return outcome


def test_x_squared_minus_one_is_verified(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    assert bundle.certificate.irreducibility is None
    assert_verified(setup, bundle)


def test_x_fourth_plus_one_is_verified_with_a_witness(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    assert bundle.certificate.irreducibility is not None
    assert_verified(setup, bundle)


def test_six_x_squared_plus_five_x_plus_one_is_verified(runtime):
    setup = factorization_setup(runtime)
    value = polynomial(
        setup, ((2, Fraction(6)), (1, Fraction(5)), (0, Fraction(1)))
    )
    bundle = valid_bundle(setup, value)
    assert_verified(setup, bundle)


def test_repeated_factors_are_verified(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    value = actual_ring.mul(
        actual_ring.pow(
            actual_ring.sub(generator(setup), actual_ring.one()), 2
        ),
        actual_ring.pow(
            actual_ring.add(generator(setup), actual_ring.one()), 3
        ),
    )
    bundle = valid_bundle(setup, value)
    assert bundle.certificate.irreducibility is None
    assert_verified(setup, bundle)


def test_a_constant_is_verified_with_an_empty_factor_set(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, ring(setup).constant(Fraction(7)))
    assert bundle.factors == factorization_factor_set(
        setup.signature, ()
    )
    assert_verified(setup, bundle)


def test_an_all_linear_factorization_needs_no_witness(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    value = actual_ring.mul(
        actual_ring.sub(generator(setup), actual_ring.one()),
        actual_ring.sub(
            generator(setup), actual_ring.constant(Fraction(2))
        ),
    )
    bundle = valid_bundle(setup, value)
    assert bundle.certificate.irreducibility is None
    assert_verified(setup, bundle)


def test_a_rational_nonmonic_value_is_verified(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    value = actual_ring.mul(
        actual_ring.constant(Fraction(1, 2)),
        actual_ring.mul(
            actual_ring.add(generator(setup), actual_ring.one()),
            actual_ring.sub(
                generator(setup), actual_ring.constant(Fraction(2))
            ),
        ),
    )
    bundle = valid_bundle(setup, value)
    assert_verified(setup, bundle)


def test_a_negative_value_is_verified(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, ring(setup).neg(x_fourth_plus_one(setup)))
    assert bundle.certificate.irreducibility is not None
    assert_verified(setup, bundle)


def test_a_repeated_nonlinear_factor_is_verified(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    value = actual_ring.mul(
        actual_ring.pow(
            actual_ring.add(
                actual_ring.pow(generator(setup), 2), actual_ring.one()
            ),
            2,
        ),
        actual_ring.sub(generator(setup), actual_ring.one()),
    )
    bundle = valid_bundle(setup, value)
    assert bundle.certificate.irreducibility is not None
    assert_verified(setup, bundle)


def test_a_rational_coefficient_irreducible_factor_is_verified(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    value = actual_ring.add(
        actual_ring.add(
            actual_ring.pow(generator(setup), 2),
            actual_ring.mul(
                actual_ring.constant(Fraction(1, 2)), generator(setup)
            ),
        ),
        actual_ring.one(),
    )
    bundle = valid_bundle(setup, value)
    assert bundle.certificate.irreducibility is not None
    assert_verified(setup, bundle)


def test_a_wrong_candidate_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    assert_invalid(setup, bundle, candidate=T.number(0))


@pytest.mark.parametrize("variant", ("none", "unit", "extra", "swap", "wrong"))
def test_a_missing_extra_or_swapped_structured_result_is_invalid(
    runtime, variant
):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    if variant == "none":
        structured = None
    elif variant == "unit":
        structured = (("unit", bundle.unit),)
    elif variant == "extra":
        structured = (
            ("unit", bundle.unit),
            ("factors", bundle.factors),
            ("extra", T.number(0)),
        )
    elif variant == "swap":
        structured = (
            ("factors", bundle.factors),
            ("unit", bundle.unit),
        )
    else:
        structured = (
            ("unit", T.number(99)),
            ("factors", bundle.factors),
        )
    assert_invalid(setup, bundle, structured=structured)


def test_a_wrong_candidate_role_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    assert_invalid(setup, bundle, role=CandidateRole.SOURCE)


def test_a_wrong_unit_is_refuted(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=T.number(2),
        entries=bundle.entries,
    )
    assert_refuted(setup, claimed)


def test_a_zero_unit_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    claimed = make_raw_bundle(
        setup,
        source=bundle.source,
        unit=T.number(0),
        factors=bundle.factors,
        candidate=T.number(1),
        radical=bundle.radical,
    )
    assert_invalid(setup, claimed)


def test_a_nonmonic_factor_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    first = actual_ring.mul(
        actual_ring.constant(Fraction(2)),
        actual_ring.add(generator(setup), actual_ring.one()),
    )
    second = actual_ring.add(
        actual_ring.mul(
            actual_ring.constant(Fraction(1, 2)), generator(setup)
        ),
        actual_ring.one(),
    )
    source = actual_ring.mul(
        actual_ring.constant(Fraction(2)),
        actual_ring.mul(first, second),
    )
    bundle = make_bundle(
        setup,
        source=render(setup, source),
        unit=T.number(2),
        entries=entries_of(setup, ((first, 1), (second, 1))),
    )
    assert_invalid(setup, bundle)


def test_a_constant_factor_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    bundle = make_bundle(
        setup,
        source=render(setup, generator(setup)),
        unit=T.number(1),
        entries=entries_of(
            setup, ((generator(setup), 1), (ring(setup).one(), 1))
        ),
    )
    assert_invalid(setup, bundle)


def test_a_duplicate_base_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    x = variable(setup)
    raw = T.app(structural(setup.signature, StructuralHead.SET), x, x)
    bundle = make_raw_bundle(
        setup,
        source=x,
        unit=T.number(1),
        factors=raw,
        candidate=T.number(1),
        radical=x,
    )
    assert_invalid(setup, bundle)


def test_a_power_one_wrapper_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    x = variable(setup)
    raw = T.app(
        structural(setup.signature, StructuralHead.SET),
        head_app(
            setup.signature, StructuralHead.POWER, x, T.number(1)
        ),
    )
    bundle = make_raw_bundle(
        setup,
        source=x,
        unit=T.number(1),
        factors=raw,
        candidate=x,
        radical=x,
    )
    assert_invalid(setup, bundle)


def test_a_nested_power_wrapper_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    x = variable(setup)
    inner = head_app(
        setup.signature, StructuralHead.POWER, x, T.number(2)
    )
    outer = head_app(
        setup.signature, StructuralHead.POWER, inner, T.number(2)
    )
    raw = T.app(structural(setup.signature, StructuralHead.SET), outer)
    bundle = make_raw_bundle(
        setup,
        source=head_app(
            setup.signature, StructuralHead.POWER, x, T.number(4)
        ),
        unit=T.number(1),
        factors=raw,
        candidate=T.number(1),
        radical=T.number(1),
    )
    assert_invalid(setup, bundle)


def test_non_coprime_factors_are_refuted(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    linear = actual_ring.sub(generator(setup), actual_ring.one())
    quadratic = actual_ring.sub(
        actual_ring.pow(generator(setup), 2), actual_ring.one()
    )
    source = actual_ring.mul(linear, quadratic)
    bundle = make_bundle(
        setup,
        source=render(setup, source),
        unit=T.number(1),
        entries=entries_of(setup, ((linear, 1), (quadratic, 1))),
    )
    assert_refuted(setup, bundle)


def test_a_degree_sum_mismatch_is_refuted(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    bundle = make_bundle(
        setup,
        source=render(setup, x_squared_minus_one(setup)),
        unit=T.number(1),
        entries=entries_of(
            setup,
            ((actual_ring.add(generator(setup), actual_ring.one()), 1),),
        ),
    )
    assert_refuted(setup, bundle)


def test_a_product_mismatch_is_refuted(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    bundle = make_bundle(
        setup,
        source=render(setup, x_squared_minus_one(setup)),
        unit=T.number(1),
        entries=entries_of(
            setup,
            (
                (
                    actual_ring.add(
                        actual_ring.pow(generator(setup), 2),
                        actual_ring.one(),
                    ),
                    1,
                ),
            ),
        ),
    )
    assert_refuted(setup, bundle)


def test_a_non_squarefree_radical_is_refuted(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    base = actual_ring.pow(
        actual_ring.add(generator(setup), actual_ring.one()), 2
    )
    bundle = make_bundle(
        setup,
        source=render(setup, base),
        unit=T.number(1),
        entries=entries_of(setup, ((base, 1),)),
    )
    assert_refuted(setup, bundle)


def test_a_radical_that_is_not_the_canonical_product_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        radical=T.number(1),
    )
    assert_invalid(setup, claimed)


def test_a_nonlinear_factor_without_a_witness_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=None,
    )
    assert_invalid(setup, claimed)


def test_a_linear_factorization_with_a_witness_is_invalid(runtime):
    setup = factorization_setup(runtime)
    linear = valid_bundle(setup, x_squared_minus_one(setup))
    nonlinear = valid_bundle(setup, x_fourth_plus_one(setup))
    witness = nonlinear.certificate.irreducibility
    assert witness is not None
    claimed = make_bundle(
        setup,
        source=linear.source,
        unit=linear.unit,
        entries=linear.entries,
        witness=witness,
    )
    assert_invalid(setup, claimed)


def test_a_nonprime_witness_prime_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    witness = bundle.certificate.irreducibility
    assert witness is not None
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(witness, prime=4),
    )
    assert_invalid(setup, claimed)


def test_a_too_small_witness_precision_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    witness = bundle.certificate.irreducibility
    assert witness is not None
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(witness, precision=1),
    )
    assert_invalid(setup, claimed)


def test_a_witness_prime_dividing_the_primitive_leading_coefficient_is_invalid(
    runtime,
):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    radical = actual_ring.add(
        actual_ring.add(
            actual_ring.pow(generator(setup), 2),
            actual_ring.mul(
                actual_ring.constant(Fraction(1, 2)), generator(setup)
            ),
        ),
        actual_ring.one(),
    )
    witness = HenselIrreducibilityWitness(
        2,
        6,
        (
            render(
                setup,
                actual_ring.add(generator(setup), actual_ring.one()),
            ),
        ),
    )
    bundle = make_bundle(
        setup,
        source=render(setup, radical),
        unit=T.number(1),
        entries=entries_of(setup, ((radical, 1),)),
        witness=witness,
    )
    outcome = assert_invalid(setup, bundle)
    assert "leading coefficient" in outcome.detail


def test_a_non_squarefree_modular_radical_is_invalid(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    radical = actual_ring.add(
        actual_ring.pow(generator(setup), 2), actual_ring.one()
    )
    witness = HenselIrreducibilityWitness(
        2,
        5,
        (
            render(
                setup,
                actual_ring.add(generator(setup), actual_ring.one()),
            ),
        ),
    )
    bundle = make_bundle(
        setup,
        source=render(setup, radical),
        unit=T.number(1),
        entries=entries_of(setup, ((radical, 1),)),
        witness=witness,
    )
    assert_invalid(setup, bundle)


def test_a_nonmonic_lifted_factor_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    _lift, values, terms, witness = witness_for(
        setup, x_fourth_plus_one(setup)
    )
    bad = render(
        setup,
        ring(setup).mul(ring(setup).constant(Fraction(2)), values[0]),
    )
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(witness, lifted=(bad, terms[1])),
    )
    assert_invalid(setup, claimed)


def test_a_constant_lifted_factor_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    _lift, _values, terms, witness = witness_for(
        setup, x_fourth_plus_one(setup)
    )
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(
            witness, lifted=(T.number(1), terms[1])
        ),
    )
    assert_invalid(setup, claimed)


def test_a_lifted_coefficient_outside_the_range_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    lift, values, terms, witness = witness_for(
        setup, x_fourth_plus_one(setup)
    )
    modulus = lift.prime**lift.precision
    bad = render(
        setup,
        ring(setup).add(
            values[0], ring(setup).constant(Fraction(modulus))
        ),
    )
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(witness, lifted=(bad, terms[1])),
    )
    assert_invalid(setup, claimed)


def test_a_lifted_factor_with_the_wrong_degree_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    _lift, _values, terms, witness = witness_for(
        setup, x_fourth_plus_one(setup)
    )
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(
            witness, lifted=(render(setup, generator(setup)), terms[1])
        ),
    )
    assert_invalid(setup, claimed)


def test_duplicate_lifted_factors_are_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    _lift, _values, terms, witness = witness_for(
        setup, x_fourth_plus_one(setup)
    )
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(witness, lifted=(terms[0], terms[0])),
    )
    assert_invalid(setup, claimed)


def test_a_reducible_lifted_modular_factor_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    lift, values, _terms, witness = witness_for(
        setup, x_fourth_plus_one(setup)
    )
    actual_ring = ring(setup)
    modulus = lift.prime**lift.precision
    product = actual_ring.mul(values[0], values[1])
    reduced = actual_ring.sum(
        actual_ring.monomial(
            exponents,
            Fraction(coefficient.numerator % modulus),
        )
        for exponents, coefficient in product.terms
    )
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(
            witness, lifted=(render(setup, reduced),)
        ),
    )
    assert_invalid(setup, claimed)


def test_a_lifted_congruence_failure_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_fourth_plus_one(setup))
    lift, values, terms, witness = witness_for(
        setup, x_fourth_plus_one(setup)
    )
    bad = render(
        setup,
        ring(setup).add(
            values[0], ring(setup).constant(Fraction(lift.prime))
        ),
    )
    claimed = make_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        entries=bundle.entries,
        witness=replace(witness, lifted=(bad, terms[1])),
    )
    assert_invalid(setup, claimed)


def test_a_claimed_reducible_factor_is_refuted(runtime):
    setup = factorization_setup(runtime)
    radical = x_squared_minus_one(setup)
    _lift, _values, _terms, witness = witness_for(setup, radical)
    bundle = make_bundle(
        setup,
        source=render(setup, radical),
        unit=T.number(1),
        entries=entries_of(setup, ((radical, 1),)),
        witness=witness,
    )
    assert_refuted(setup, bundle)


def test_a_reducible_quadratic_times_quadratic_factor_is_refuted(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    first = actual_ring.add(
        actual_ring.pow(generator(setup), 2), actual_ring.one()
    )
    second = actual_ring.add(
        actual_ring.pow(generator(setup), 2),
        actual_ring.constant(Fraction(2)),
    )
    radical = actual_ring.mul(first, second)
    _lift, _values, _terms, witness = witness_for(setup, radical)
    assert len(witness.lifted) >= 2
    bundle = make_bundle(
        setup,
        source=render(setup, radical),
        unit=T.number(1),
        entries=entries_of(setup, ((radical, 1),)),
        witness=witness,
    )
    outcome = assert_refuted(setup, bundle)
    assert "proper factor" in outcome.detail


def test_a_reducible_nonmonic_factor_is_refuted(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    first = actual_ring.add(
        actual_ring.pow(generator(setup), 2), actual_ring.one()
    )
    second = actual_ring.add(
        actual_ring.pow(generator(setup), 2),
        actual_ring.constant(Fraction(1, 2)),
    )
    radical = actual_ring.mul(first, second)
    _lift, _values, _terms, witness = witness_for(setup, radical)
    assert len(witness.lifted) >= 2
    bundle = make_bundle(
        setup,
        source=render(setup, radical),
        unit=T.number(1),
        entries=entries_of(setup, ((radical, 1),)),
        witness=witness,
    )
    outcome = assert_refuted(setup, bundle)
    assert "proper factor" in outcome.detail


def test_a_rational_cubic_with_two_modular_factors_is_verified(runtime):
    setup = factorization_setup(runtime)
    actual_ring = ring(setup)
    value = actual_ring.sum(
        (
            actual_ring.monomial((3,), Fraction(1)),
            actual_ring.monomial((1,), Fraction(1)),
            actual_ring.monomial((0,), Fraction(1, 2)),
        )
    )
    bundle = valid_bundle(setup, value)
    witness = bundle.certificate.irreducibility
    assert witness is not None
    assert len(witness.lifted) >= 2
    assert_verified(setup, bundle)


def test_irreducibility_budget_exhaustion_is_unverified(runtime):
    setup = factorization_setup(runtime)
    radical = x_squared_minus_one(setup)
    _lift, _values, _terms, witness = witness_for(setup, radical)
    bundle = make_bundle(
        setup,
        source=render(setup, radical),
        unit=T.number(1),
        entries=entries_of(setup, ((radical, 1),)),
        witness=witness,
    )
    outcome = check_bundle(
        setup, bundle, checker=make_checker(setup, pair_budget=0)
    )
    assert isinstance(outcome, Unverified), outcome
    assert outcome.reason is Reason.BUDGET
    assert outcome.missing == frozenset(
        {"factorization_irreducibility_budget"}
    )


def test_a_wrong_problem_operation_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    problem = make_problem(
        setup, bundle.source, operation="differentiate"
    )
    assert_invalid(setup, bundle, problem=problem)


def test_a_wrong_problem_target_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    other = runtime.table.intern("y")
    roles = VariableRoles(
        other,
        (),
        ParameterMode.SPECIFIED_VALUES,
        runtime.world.id,
        S.REAL,
    )
    problem = make_problem(setup, bundle.source, roles=roles)
    assert_invalid(setup, bundle, problem=problem)


def test_a_wrong_problem_input_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    other = ring(setup).add(generator(setup), ring(setup).one())
    problem = make_problem(setup, render(setup, other))
    assert_invalid(setup, bundle, problem=problem)


def test_a_wrong_problem_coverage_or_language_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    wrong_coverage = make_problem(
        setup, bundle.source, coverage=Coverage.SOUND_SET
    )
    assert_invalid(setup, bundle, problem=wrong_coverage)
    wrong_language = make_problem(
        setup, bundle.source, language=ResultLanguage.EXPRESSION
    )
    assert_invalid(setup, bundle, problem=wrong_language)


def test_a_region_restricted_problem_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    region = proposition_in(
        runtime.frames,
        setup.frame,
        setup.signature,
        head_app(
            setup.signature,
            StructuralHead.GT,
            variable(setup),
            T.number(0),
        ),
    )
    problem = make_problem(setup, bundle.source, region=region)
    assert_invalid(setup, bundle, problem=problem)


def test_a_context_without_algebra_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    context = verification_context(runtime, setup.frame)
    assert_invalid(setup, bundle, context=context)


def test_a_different_algebra_request_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    other = replace(runtime.request)
    context = verification_context(
        runtime, setup.frame, algebra=other
    )
    assert_invalid(setup, bundle, context=context)


def test_a_bridge_refusal_is_unverified(runtime):
    setup = factorization_setup(runtime)
    x = variable(setup)
    source = head_app(
        setup.signature, StructuralHead.POWER, x, T.number(-1)
    )
    empty = T.app(structural(setup.signature, StructuralHead.SET))
    bundle = make_raw_bundle(
        setup,
        source=source,
        unit=T.number(1),
        factors=empty,
        candidate=T.number(1),
        radical=T.number(1),
    )
    outcome = check_bundle(setup, bundle)
    assert isinstance(outcome, Unverified), outcome
    assert outcome.reason is Reason.FRAGMENT
    assert outcome.missing == frozenset({"nonnegative_power"})


def test_a_zero_source_is_invalid_evidence(runtime):
    setup = factorization_setup(runtime)
    empty = T.app(structural(setup.signature, StructuralHead.SET))
    bundle = make_raw_bundle(
        setup,
        source=T.number(0),
        unit=T.number(1),
        factors=empty,
        candidate=T.number(1),
        radical=T.number(1),
    )
    assert_invalid(setup, bundle)


def test_a_malformed_certificate_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    assert_invalid(setup, bundle, certificate=T.number(1))
    mismatched = FactorizationCertificate(
        bundle.source,
        runtime.variable,
        T.number(3),
        bundle.factors,
        bundle.radical,
    )
    assert_invalid(setup, bundle, certificate=mismatched)


def test_a_non_factorization_conclusion_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    other = proposition_in(
        runtime.frames,
        setup.frame,
        setup.signature,
        head_app(
            setup.signature,
            StructuralHead.GT,
            variable(setup),
            T.number(0),
        ),
    )
    request = CheckRequest(
        setup.frame,
        (other,),
        (),
        bundle.certificate,
        problem=bundle.problem,
        candidate=bundle.product,
        candidate_role=CandidateRole.RESULT,
        context=verification_context(
            runtime, setup.frame, algebra=runtime.request
        ),
        structured=(
            ("unit", bundle.unit),
            ("factors", bundle.factors),
        ),
    )
    outcome = make_checker(setup).check(request)
    assert isinstance(outcome, InvalidEvidence), outcome


def test_multiple_conclusions_are_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    request = CheckRequest(
        setup.frame,
        (bundle.proposition, bundle.proposition),
        (),
        bundle.certificate,
        problem=bundle.problem,
        candidate=bundle.product,
        candidate_role=CandidateRole.RESULT,
        context=verification_context(
            runtime, setup.frame, algebra=runtime.request
        ),
        structured=(
            ("unit", bundle.unit),
            ("factors", bundle.factors),
        ),
    )
    outcome = make_checker(setup).check(request)
    assert isinstance(outcome, InvalidEvidence), outcome


def test_the_checker_validates_its_ring_request_and_budget(runtime):
    setup = factorization_setup(runtime)
    other_ring = UnivariatePolynomialRing(
        runtime.variable, RationalField()
    )
    with pytest.raises(ValueError):
        FactorizationChecker(
            other_ring,
            setup.signature,
            setup.vocabulary,
            runtime.bridge,
            runtime.frames,
            runtime.request,
        )
    generator_roles = VariableRoles(
        None,
        (),
        ParameterMode.SPECIFIED_VALUES,
        runtime.world.id,
        None,
        (),
        (runtime.variable,),
        (S.REAL,),
    )
    generator_request = AlgebraRequest(
        coefficient=runtime.request.coefficient,
        coefficient_domain=runtime.request.coefficient_domain,
        parameter_ring=None,
        roles=generator_roles,
        interpretation=Interpretation.FORMAL,
    )
    with pytest.raises(ValueError):
        FactorizationChecker(
            runtime.ring,
            setup.signature,
            setup.vocabulary,
            runtime.bridge,
            runtime.frames,
            generator_request,
        )
    with pytest.raises(ValueError):
        make_checker(setup, pair_budget=-1)
    with pytest.raises(TypeError):
        make_checker(setup, pair_budget=True)  # type: ignore[arg-type]
    heads = {
        symbol: head
        for symbol, head in setup.signature.heads.items()
        if head is not StructuralHead.SET
    }
    without_set = LanguageSignature.build(
        heads,
        setup.signature.binders,
        setup.signature.operators,
    )
    with pytest.raises(ValueError):
        FactorizationChecker(
            runtime.ring,
            without_set,
            setup.vocabulary,
            runtime.bridge,
            runtime.frames,
            runtime.request,
        )
    checker = make_checker(setup)
    assert checker.id == "algebra.factorization"
    assert checker.version == "1"


def test_the_structured_payload_uses_the_claimed_terms(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    assert factorization_product_term(
        setup.signature, bundle.unit, bundle.factors
    ) == bundle.product
    assert_verified(setup, bundle)
    other_unit = T.number(2)
    wrong = (
        ("unit", other_unit),
        ("factors", bundle.factors),
    )
    assert_invalid(setup, bundle, structured=wrong)


def test_a_factor_set_order_mismatch_is_invalid(runtime):
    setup = factorization_setup(runtime)
    bundle = valid_bundle(setup, x_squared_minus_one(setup))
    members = list(bundle.entries)
    if len(members) < 2:
        pytest.skip("the value has fewer than two distinct factors")
    raw = T.app(
        structural(setup.signature, StructuralHead.SET),
        *tuple(reversed([term for term, _ in members])),
    )
    claimed = make_raw_bundle(
        setup,
        source=bundle.source,
        unit=bundle.unit,
        factors=raw,
        candidate=bundle.product,
        radical=bundle.radical,
    )
    assert_invalid(setup, claimed)
