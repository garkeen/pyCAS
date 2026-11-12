"""The independent `HasRationalLogAntiderivative` checker over ``Q(x)``."""

from dataclasses import replace
from fractions import Fraction

import pytest
from logarithmic_support import (
    LogBundle,
    LogSetup,
    check_bundle,
    checker,
    full_context,
    generator,
    linear_factor,
    log_setup,
    make_bundle,
    make_problem,
    monic_product,
    polynomial,
    render,
    render_polynomial,
    search_bundle,
    variable,
    view_of,
)
from support import proposition_in, verification_context

from cas.algebra.polynomial import Polynomial
from cas.algebra.rational import RationalFunction
from cas.kernel.evidence import (
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
    ValueDomain,
    VariableRoles,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.calculus.integration.logarithmic_checker import (
    LogarithmicIntegrationCheckBudget,
    LogarithmicIntegrationChecker,
)
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogVocabulary,
    parse_rational_log_terms,
    rational_log_term_set,
)
from cas.semantics.conditions import and_all
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T


def field(setup: LogSetup):
    return setup.bridge.field


def source_polynomial(
    setup: LogSetup, terms: tuple[tuple[int, Fraction], ...]
) -> RationalFunction[Fraction]:
    return field(setup).of_polynomial(polynomial(setup, terms))


def rational(
    setup: LogSetup,
    numerator: Polynomial[Fraction],
    denominator: Polynomial[Fraction],
) -> RationalFunction[Fraction]:
    return field(setup).fraction(numerator, denominator)


def x_squared_minus_one(setup: LogSetup) -> Polynomial[Fraction]:
    return monic_product(setup, (-1, 1))


def zero(setup: LogSetup) -> RationalFunction[Fraction]:
    return field(setup).zero()


def true_region(setup: LogSetup):
    return proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        T.TRUE,
    )


def region_proposition(setup: LogSetup, term: T.Term):
    return proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        term,
    )


def greater_than(
    setup: LogSetup, term: T.Term, bound: Fraction
) -> T.Term:
    return T.app(
        setup.signature.head_term(StructuralHead.GT),
        term,
        T.number(bound),
    )


def log_member(
    setup: LogSetup, coefficient: Fraction, argument: T.Term
) -> T.Term:
    logged = T.app(setup.vocabulary.log_function, argument)
    if coefficient == 1:
        return logged
    return T.app(
        setup.signature.head_term(StructuralHead.TIMES),
        T.number(coefficient),
        logged,
    )


def raw_log_set(setup: LogSetup, members: tuple[T.Term, ...]) -> T.Term:
    symbol = setup.signature.symbol_of(StructuralHead.SET)
    assert symbol is not None
    return T.app(T.symbol(symbol, "Set"), *members)


def assert_verified(
    setup: LogSetup, bundle: LogBundle, **kwargs: object
) -> None:
    outcome = check_bundle(setup, bundle, **kwargs)  # type: ignore[arg-type]
    assert isinstance(outcome, Verified), outcome
    assert outcome.checked == (bundle.proposition,)


def assert_invalid(
    setup: LogSetup, bundle: LogBundle, **kwargs: object
) -> InvalidEvidence:
    outcome = check_bundle(setup, bundle, **kwargs)  # type: ignore[arg-type]
    assert isinstance(outcome, InvalidEvidence), outcome
    return outcome


def assert_unverified(
    setup: LogSetup, bundle: LogBundle, **kwargs: object
) -> Unverified:
    outcome = check_bundle(setup, bundle, **kwargs)  # type: ignore[arg-type]
    assert isinstance(outcome, Unverified), outcome
    return outcome


def test_a_polynomial_source_without_logs_is_verified(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert bundle.log_terms == rational_log_term_set(
        setup.signature, setup.vocabulary.log_function, ()
    )
    assert bundle.region == T.TRUE
    assert_verified(setup, bundle)


def test_one_over_x_is_verified_with_its_log_domain(runtime):
    setup = log_setup(runtime)
    value = rational(setup, polynomial(setup, ((0, Fraction(1)),)), generator(setup))
    bundle = search_bundle(setup, value)
    assert bundle.region == greater_than(setup, variable(setup), Fraction(0))
    assert_verified(setup, bundle)
    assert_verified(setup, bundle, context=full_context(setup))


def test_one_over_x_squared_minus_one_is_verified(runtime):
    setup = log_setup(runtime)
    value = rational(
        setup,
        polynomial(setup, ((0, Fraction(1)),)),
        x_squared_minus_one(setup),
    )
    bundle = search_bundle(setup, value)
    entries = parse_rational_log_terms(
        setup.signature,
        setup.vocabulary.log_function,
        bundle.log_terms,
    )
    assert entries is not None
    coefficients = {coefficient for coefficient, _ in entries}
    assert any(coefficient < 0 for coefficient in coefficients)
    assert any(coefficient > 0 for coefficient in coefficients)
    assert_verified(setup, bundle)


def test_two_x_over_x_squared_plus_one_is_verified(runtime):
    setup = log_setup(runtime)
    numerator = polynomial(setup, ((1, Fraction(2)),))
    denominator = polynomial(
        setup, ((2, Fraction(1)), (0, Fraction(1)))
    )
    bundle = search_bundle(setup, rational(setup, numerator, denominator))
    assert_verified(setup, bundle)


def test_x_over_x_squared_plus_one_is_verified(runtime):
    setup = log_setup(runtime)
    denominator = polynomial(
        setup, ((2, Fraction(1)), (0, Fraction(1)))
    )
    bundle = search_bundle(
        setup, rational(setup, generator(setup), denominator)
    )
    assert_verified(setup, bundle)


def test_repeated_denominator_is_verified_with_a_non_total_part(runtime):
    setup = log_setup(runtime)
    denominator = field(setup).polynomials.pow(x_squared_minus_one(setup), 2)
    bundle = search_bundle(
        setup,
        rational(
            setup,
            polynomial(setup, ((0, Fraction(1)),)),
            denominator,
        ),
    )
    assert bundle.polynomial_part != T.number(0)
    assert_verified(setup, bundle)
    assert_verified(setup, bundle, context=full_context(setup))


def test_a_wrong_candidate_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(setup, bundle, candidate=T.number(0))


def test_a_missing_candidate_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(setup, bundle, candidate=None)


def test_a_wrong_candidate_role_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(setup, bundle, role=CandidateRole.REMAINDER)


def test_a_missing_certificate_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(setup, bundle, certificate=None)


def test_a_mismatched_certificate_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        certificate=replace(bundle.certificate, source=T.number(0)),
    )


@pytest.mark.parametrize(
    "structured",
    [
        None,
        (("polynomial_part", T.number(0)),),
        (
            ("polynomial_part", T.number(0)),
            ("log_terms", T.number(0)),
            ("extra", T.number(0)),
        ),
        (
            ("log_terms", T.number(0)),
            ("polynomial_part", T.number(0)),
        ),
    ],
)
def test_the_structured_result_must_be_exact(runtime, structured):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(setup, bundle, structured=structured)


def test_a_noncanonical_visible_result_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((2, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((3, Fraction(1, 3)),)
        ),
        entries=(),
        result=T.number(0),
    )
    assert_invalid(setup, bundle)


def test_a_wrong_coefficient_is_not_verified(runtime):
    setup = log_setup(runtime)
    value = rational(setup, polynomial(setup, ((0, Fraction(1)),)), generator(setup))
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=zero(setup),
        entries=((Fraction(2), generator(setup)),),
    )
    outcome = assert_unverified(setup, bundle)
    assert outcome.reason.value == "fragment"
    assert "regional_logarithmic_identity" in outcome.missing


def test_a_wrong_argument_is_not_verified(runtime):
    setup = log_setup(runtime)
    value = rational(setup, polynomial(setup, ((0, Fraction(1)),)), generator(setup))
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=zero(setup),
        entries=((Fraction(1), linear_factor(setup, 1)),),
    )
    outcome = assert_unverified(setup, bundle)
    assert "regional_logarithmic_identity" in outcome.missing


def test_a_missing_log_term_is_not_verified(runtime):
    setup = log_setup(runtime)
    value = rational(
        setup,
        polynomial(setup, ((0, Fraction(1)),)),
        x_squared_minus_one(setup),
    )
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=zero(setup),
        entries=((Fraction(1, 2), linear_factor(setup, 1)),),
    )
    outcome = assert_unverified(setup, bundle)
    assert "regional_logarithmic_identity" in outcome.missing


def test_an_extra_log_term_is_not_verified(runtime):
    setup = log_setup(runtime)
    value = rational(setup, polynomial(setup, ((0, Fraction(1)),)), generator(setup))
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=zero(setup),
        entries=(
            (Fraction(1), generator(setup)),
            (Fraction(2), linear_factor(setup, 1)),
        ),
    )
    outcome = assert_unverified(setup, bundle)
    assert "regional_logarithmic_identity" in outcome.missing


def test_a_zero_log_coefficient_is_invalid(runtime):
    setup = log_setup(runtime)
    log_terms = raw_log_set(
        setup, (log_member(setup, Fraction(0), variable(setup)),)
    )
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        log_terms=log_terms,
        log_arguments=(variable(setup),),
    )
    assert_invalid(setup, bundle)


def test_a_noncanonical_times_wrapper_is_invalid(runtime):
    setup = log_setup(runtime)
    logged = T.app(setup.vocabulary.log_function, variable(setup))
    wrapped = T.app(
        setup.signature.head_term(StructuralHead.TIMES),
        T.number(1),
        logged,
    )
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        log_terms=raw_log_set(setup, (wrapped,)),
        log_arguments=(variable(setup),),
    )
    assert_invalid(setup, bundle)


def test_a_duplicate_coefficient_is_invalid(runtime):
    setup = log_setup(runtime)
    argument = render_polynomial(setup, linear_factor(setup, 1))
    log_terms = raw_log_set(
        setup,
        (
            log_member(setup, Fraction(2), variable(setup)),
            log_member(setup, Fraction(2), argument),
        ),
    )
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        log_terms=log_terms,
        log_arguments=(variable(setup), argument),
    )
    assert_invalid(setup, bundle)


def test_a_non_monic_log_argument_is_invalid(runtime):
    setup = log_setup(runtime)
    ring = field(setup).polynomials
    nonmonic = ring.mul(
        ring.constant(Fraction(2)), generator(setup)
    )
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        entries=((Fraction(1), nonmonic),),
    )
    assert_invalid(setup, bundle)


def test_a_constant_log_argument_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        entries=((Fraction(1), polynomial(setup, ((0, Fraction(2)),))),),
    )
    assert_invalid(setup, bundle)


def test_a_non_squarefree_log_argument_is_invalid(runtime):
    setup = log_setup(runtime)
    ring = field(setup).polynomials
    square = ring.pow(generator(setup), 2)
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        entries=((Fraction(1), square),),
    )
    assert_invalid(setup, bundle)


def test_non_coprime_log_arguments_are_invalid(runtime):
    setup = log_setup(runtime)
    ring = field(setup).polynomials
    common = linear_factor(setup, 1)
    other = ring.mul(common, linear_factor(setup, -1))
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        entries=((Fraction(1), common), (Fraction(2), other)),
    )
    assert_invalid(setup, bundle)


def test_a_non_polynomial_log_argument_is_a_fragment_gap(runtime):
    setup = log_setup(runtime)
    inverse_x = T.app(
        setup.signature.head_term(StructuralHead.POWER),
        variable(setup),
        T.number(-1),
    )
    log_terms = raw_log_set(
        setup, (log_member(setup, Fraction(1), inverse_x),)
    )
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        log_terms=log_terms,
        log_arguments=(inverse_x,),
    )
    outcome = assert_unverified(setup, bundle)
    assert "polynomial_log_argument" in outcome.missing


def test_a_global_claim_with_a_non_total_source_is_guarded(runtime):
    setup = log_setup(runtime)
    value = rational(setup, polynomial(setup, ((0, Fraction(1)),)), generator(setup))
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=zero(setup),
        entries=((Fraction(1), generator(setup)),),
        region=true_region(setup),
    )
    outcome = assert_unverified(setup, bundle)
    assert outcome.reason.value == "guarded"
    assert "region_coverage" in outcome.missing


def test_a_claim_region_outside_the_source_domain_is_guarded(runtime):
    setup = log_setup(runtime)
    value = rational(setup, polynomial(setup, ((0, Fraction(1)),)), generator(setup))
    region = region_proposition(
        setup, greater_than(setup, variable(setup), Fraction(-1))
    )
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=zero(setup),
        entries=((Fraction(1), generator(setup)),),
        region=region,
    )
    outcome = assert_unverified(setup, bundle)
    assert outcome.reason.value == "guarded"
    assert "region_coverage" in outcome.missing


def test_a_claim_region_outside_a_log_domain_is_guarded(runtime):
    setup = log_setup(runtime)
    ring = field(setup).polynomials
    first = monic_product(setup, (-1, 1))
    second = monic_product(setup, (-2, 2))
    terms = (
        field(setup).fraction(
            ring.mul(ring.constant(Fraction(1)), ring.derivative(first, 0)),
            first,
        ),
        field(setup).fraction(
            ring.mul(ring.constant(Fraction(2)), ring.derivative(second, 0)),
            second,
        ),
    )
    value = field(setup).add(terms[0], terms[1])
    source_term = render(setup, value)
    source_view = view_of(setup, source_term)
    conditions = tuple(
        region.term
        for region in (
            source_view.source_domain,
            source_view.valid_on,
        )
        if region is not None and region.term != T.TRUE
    )
    region = region_proposition(
        setup,
        and_all(
            setup.signature,
            *conditions,
            greater_than(
                setup, render_polynomial(setup, first), Fraction(0)
            ),
        ),
    )
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=zero(setup),
        entries=(
            (Fraction(1), first),
            (Fraction(2), second),
        ),
        region=region,
    )
    outcome = assert_unverified(setup, bundle)
    assert outcome.reason.value == "guarded"
    assert "log_domain" in outcome.missing


def test_a_claim_region_outside_the_polynomial_part_domain_is_guarded(runtime):
    setup = log_setup(runtime)
    denominator = field(setup).polynomials.pow(x_squared_minus_one(setup), 2)
    value = rational(
        setup,
        polynomial(setup, ((0, Fraction(1)),)),
        denominator,
    )
    # The part has an extra pole at x = 2 that the positive-region conditions
    # do not rule out; coverage of the part domain must be refused.
    polynomial_part = rational(
        setup,
        polynomial(setup, ((0, Fraction(1)),)),
        monic_product(setup, (-2, 1)),
    )
    source_term = render(setup, value)
    source_view = view_of(setup, source_term)
    conditions = tuple(
        region.term
        for region in (
            source_view.source_domain,
            source_view.valid_on,
        )
        if region is not None and region.term != T.TRUE
    )
    region = region_proposition(
        setup,
        and_all(
            setup.signature,
            *conditions,
            greater_than(
                setup, render_polynomial(setup, linear_factor(setup, 1)), Fraction(0)
            ),
            greater_than(
                setup, render_polynomial(setup, linear_factor(setup, -1)), Fraction(0)
            ),
        ),
    )
    bundle = make_bundle(
        setup,
        source_value=value,
        polynomial_part_value=polynomial_part,
        entries=(
            (Fraction(1, 2), linear_factor(setup, 1)),
            (Fraction(-1, 2), linear_factor(setup, -1)),
        ),
        region=region,
    )
    outcome = assert_unverified(setup, bundle)
    assert outcome.reason.value == "guarded"
    assert "region_coverage" in outcome.missing


def test_a_cancelled_hole_log_argument_is_a_fragment_gap(runtime):
    setup = log_setup(runtime)
    factor = render_polynomial(setup, linear_factor(setup, 1))
    argument = T.app(
        setup.signature.head_term(StructuralHead.TIMES),
        variable(setup),
        T.app(
            setup.signature.head_term(StructuralHead.POWER),
            variable(setup),
            T.number(-1),
        ),
        factor,
    )
    log_terms = raw_log_set(
        setup, (log_member(setup, Fraction(1), argument),)
    )
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((1, Fraction(1)),)),
        polynomial_part_value=source_polynomial(
            setup, ((2, Fraction(1, 2)),)
        ),
        log_terms=log_terms,
        log_arguments=(argument,),
    )
    outcome = assert_unverified(setup, bundle)
    assert "polynomial_log_argument" in outcome.missing


def test_a_restricted_identity_failure_is_a_fragment_gap(runtime):
    setup = log_setup(runtime)
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((2, Fraction(1)),)),
        polynomial_part_value=zero(setup),
        entries=(),
        region=region_proposition(
            setup, greater_than(setup, variable(setup), Fraction(0))
        ),
    )
    outcome = assert_unverified(setup, bundle)
    assert "regional_logarithmic_identity" in outcome.missing


def test_a_global_identity_failure_is_refuted(runtime):
    setup = log_setup(runtime)
    bundle = make_bundle(
        setup,
        source_value=source_polynomial(setup, ((2, Fraction(1)),)),
        polynomial_part_value=zero(setup),
        entries=(),
        region=true_region(setup),
    )
    outcome = check_bundle(setup, bundle)
    assert isinstance(outcome, Refuted), outcome


def test_the_problem_operation_must_match(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        problem=make_problem(
            setup, bundle.source, operation="integrate_polynomial"
        ),
    )


def test_the_problem_inputs_must_match(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        problem=make_problem(
            setup, bundle.source, inputs=(T.number(1),)
        ),
    )


def test_the_problem_target_must_match(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    runtime = setup.runtime
    second = runtime.table.intern("y")
    roles = VariableRoles(
        second,
        (),
        ParameterMode.SPECIFIED_VALUES,
        runtime.world.id,
        S.REAL,
    )
    assert_invalid(
        setup,
        bundle,
        problem=make_problem(setup, bundle.source, roles=roles),
    )


def test_the_problem_coverage_must_be_one_verified(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        problem=make_problem(
            setup,
            bundle.source,
            coverage=Coverage.COMPLETE_SET,
        ),
    )


def test_the_problem_result_language_must_be_a_decomposition(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        problem=make_problem(
            setup,
            bundle.source,
            language=ResultLanguage.EXPRESSION,
        ),
    )


def test_the_problem_region_must_be_covered_by_the_claim(runtime):
    setup = log_setup(runtime)
    value = rational(
        setup, polynomial(setup, ((0, Fraction(1)),)), generator(setup)
    )
    bundle = search_bundle(setup, value)
    problem_region = region_proposition(
        setup, greater_than(setup, variable(setup), Fraction(-5))
    )
    assert_invalid(
        setup,
        bundle,
        problem=make_problem(
            setup, bundle.source, region=problem_region
        ),
    )


def test_a_context_without_the_fixed_algebra_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        context=verification_context(setup.runtime, setup.frame),
    )
    assert_invalid(setup, bundle, context=None)


def test_a_context_with_another_algebra_request_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    other = replace(setup.runtime.request)
    assert_invalid(
        setup,
        bundle,
        context=verification_context(
            setup.runtime, setup.frame, algebra=other
        ),
    )


def test_a_non_specification_conclusion_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        conclusions=(true_region(setup),),
    )


def test_more_than_one_conclusion_is_invalid(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    assert_invalid(
        setup,
        bundle,
        conclusions=(bundle.proposition, bundle.proposition),
    )


def test_the_checker_rejects_another_target(runtime):
    setup = log_setup(runtime)
    runtime = setup.runtime
    second = runtime.table.intern("y")
    roles = VariableRoles(
        second,
        (),
        ParameterMode.SPECIFIED_VALUES,
        runtime.world.id,
        S.REAL,
    )
    request = AlgebraRequest(
        coefficient=runtime.request.coefficient,
        coefficient_domain=runtime.request.coefficient_domain,
        parameter_ring=None,
        roles=roles,
        interpretation=runtime.request.interpretation,
        differential=runtime.request.differential,
    )
    with pytest.raises(ValueError):
        LogarithmicIntegrationChecker(
            setup.bridge,
            setup.signature,
            setup.vocabulary,
            runtime.frames,
            request,
        )


def test_the_checker_rejects_a_generator_request(runtime):
    setup = log_setup(runtime)
    runtime = setup.runtime
    roles = VariableRoles(
        None,
        (),
        ParameterMode.SPECIFIED_VALUES,
        runtime.world.id,
        None,
        (),
        (runtime.variable,),
        (S.REAL,),
    )
    request = AlgebraRequest(
        coefficient=runtime.request.coefficient,
        coefficient_domain=runtime.request.coefficient_domain,
        parameter_ring=None,
        roles=roles,
        interpretation=runtime.request.interpretation,
        differential=runtime.request.differential,
    )
    with pytest.raises(ValueError):
        LogarithmicIntegrationChecker(
            setup.bridge,
            setup.signature,
            setup.vocabulary,
            runtime.frames,
            request,
        )


def test_the_checker_rejects_a_non_rational_coefficient_domain(runtime):
    setup = log_setup(runtime)
    runtime = setup.runtime
    request = replace(
        runtime.request, coefficient_domain=ValueDomain.INTEGER
    )
    with pytest.raises(ValueError):
        LogarithmicIntegrationChecker(
            setup.bridge,
            setup.signature,
            setup.vocabulary,
            runtime.frames,
            request,
        )


def test_the_checker_rejects_a_signature_without_the_predicate(runtime):
    setup = log_setup(runtime)
    runtime = setup.runtime
    with pytest.raises(ValueError):
        LogarithmicIntegrationChecker(
            setup.bridge,
            runtime.signature,
            setup.vocabulary,
            runtime.frames,
            runtime.request,
        )


def test_the_checker_rejects_a_wrong_logarithm_operator(runtime):
    setup = log_setup(runtime)
    runtime = setup.runtime
    operators = dict(setup.signature.operators)
    operators[setup.vocabulary.log_symbol] = setup.vocabulary.signature
    signature = setup.signature.__class__.build(
        setup.signature.heads,
        setup.signature.binders,
        operators,
    )
    with pytest.raises(ValueError):
        LogarithmicIntegrationChecker(
            setup.bridge,
            signature,
            setup.vocabulary,
            runtime.frames,
            runtime.request,
        )
def test_the_checker_requires_declared_log_semantics(runtime):
    setup = log_setup(runtime)
    bare = RationalLogVocabulary(
        setup.vocabulary.symbol,
        setup.vocabulary.name,
        setup.vocabulary.log_symbol,
        setup.vocabulary.log_name,
    )
    with pytest.raises(ValueError):
        LogarithmicIntegrationChecker(
            setup.bridge,
            setup.signature,
            bare,
            runtime.frames,
            runtime.request,
        )


def test_the_checker_is_bound_to_the_declared_log_semantics(runtime):
    setup = log_setup(runtime)
    assert checker(setup).semantics is setup.semantics
    assert checker(setup).semantics.function.symbol == (
        setup.vocabulary.log_symbol
    )


def test_the_checker_budget_rejects_bool_and_negative_limits():
    for kwargs in (
        {"max_degree": True},
        {"max_log_terms": True},
        {"max_degree": -1},
        {"max_log_terms": -1},
    ):
        with pytest.raises((TypeError, ValueError)):
            LogarithmicIntegrationCheckBudget(**kwargs)  # type: ignore[arg-type]


def budgeted_checker(
    setup: LogSetup, **kwargs: int
) -> LogarithmicIntegrationChecker:
    runtime = setup.runtime
    return LogarithmicIntegrationChecker(
        setup.bridge,
        setup.signature,
        setup.vocabulary,
        runtime.frames,
        runtime.request,
        budget=LogarithmicIntegrationCheckBudget(**kwargs),
    )


def test_an_over_degree_source_returns_budget(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((3, Fraction(1)),))
    )
    outcome = check_bundle(
        setup,
        bundle,
        checker_override=budgeted_checker(setup, max_degree=2),
    )
    assert isinstance(outcome, Unverified), outcome
    assert outcome.reason is Reason.BUDGET
    assert outcome.missing == frozenset(
        {"logarithmic_integration_degree"}
    )


def test_too_many_log_terms_returns_budget(runtime):
    setup = log_setup(runtime)
    value = rational(
        setup,
        polynomial(setup, ((0, Fraction(1)),)),
        x_squared_minus_one(setup),
    )
    bundle = search_bundle(setup, value)
    outcome = check_bundle(
        setup,
        bundle,
        checker_override=budgeted_checker(setup, max_log_terms=1),
    )
    assert isinstance(outcome, Unverified), outcome
    assert outcome.reason is Reason.BUDGET
    assert outcome.missing == frozenset(
        {"logarithmic_integration_terms"}
    )


def test_the_checker_allows_one_antiderivative_degree_increment(runtime):
    setup = log_setup(runtime)
    bundle = search_bundle(
        setup, source_polynomial(setup, ((2, Fraction(1)),))
    )
    outcome = check_bundle(
        setup,
        bundle,
        checker_override=budgeted_checker(setup, max_degree=2),
    )
    assert isinstance(outcome, Verified), outcome


def test_the_checker_budget_still_admits_a_valid_claim(runtime):
    setup = log_setup(runtime)
    value = rational(
        setup,
        polynomial(setup, ((0, Fraction(1)),)),
        x_squared_minus_one(setup),
    )
    bundle = search_bundle(setup, value)
    outcome = check_bundle(
        setup,
        bundle,
        checker_override=budgeted_checker(
            setup, max_degree=2, max_log_terms=2
        ),
    )
    assert isinstance(outcome, Verified), outcome
