"""The derivative checker over a parameterized coefficient ring."""

from dataclasses import replace

from support import (
    head_app,
    render_value,
    runtime_proposition,
    typed_in,
    variable,
    verification_context,
    view_of,
)

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
    DomainRequirement,
    Exactness,
    InterpretationRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.certificate import DerivativeCertificate
from cas.math.calculus.differentiation.specification import has_derivative
from cas.runtime import bootstrap_parameterized
from cas.syntax import term as T


def setup():
    runtime = bootstrap_parameterized()
    parameter = T.symbol(runtime.request.parameters[0], "a")
    x = variable(runtime)
    source = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        parameter,
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(2)),
    )
    value = view_of(runtime, source).value
    candidate = render_value(runtime, runtime.differential.deriv(value))
    return runtime, parameter, x, source, candidate


def claim(runtime, source, candidate, variable_term=None):
    return runtime_proposition(
        runtime,
        has_derivative(
            runtime.vocabulary,
            T.TRUE,
            source,
            variable(runtime) if variable_term is None else variable_term,
            candidate,
        ),
    )


def check(
    runtime,
    proposition,
    source,
    candidate,
    variable_id=None,
    checked=None,
    role=CandidateRole.RESULT,
):
    certificate = DerivativeCertificate(
        T.TRUE,
        source,
        runtime.variable if variable_id is None else variable_id,
        candidate,
    )
    return runtime.checker.check(
        CheckRequest(
            runtime.frame.id,
            (proposition,),
            (),
            certificate,
            candidate=candidate if checked is None else checked,
            candidate_role=role,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )


def test_parameterized_candidates_are_verified():
    runtime, parameter, x, source, candidate = setup()
    outcome = check(runtime, claim(runtime, source, candidate), source, candidate)
    assert isinstance(outcome, Verified)


def test_a_perturbed_parameterized_candidate_is_refuted():
    runtime, parameter, x, source, candidate = setup()
    wrong = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        candidate,
        T.number(1),
    )
    outcome = check(runtime, claim(runtime, source, wrong), source, wrong)
    assert isinstance(outcome, Refuted)
    assert outcome.witnesses == (source, wrong)


def test_the_parameter_is_not_the_target():
    runtime, parameter, x, source, candidate = setup()
    proposition = runtime_proposition(
        runtime,
        has_derivative(
            runtime.vocabulary, T.TRUE, source, parameter, candidate
        ),
    )
    outcome = check(
        runtime,
        proposition,
        source,
        candidate,
        variable_id=runtime.request.parameters[0],
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT


def test_reciprocals_of_a_parameter_are_outside_the_fragment():
    runtime, parameter, x, _, _ = setup()
    source = head_app(
        runtime.signature,
        StructuralHead.POWER,
        parameter,
        T.number(-1),
    )
    candidate = T.number(0)
    outcome = check(runtime, claim(runtime, source, candidate), source, candidate)
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT


def test_a_missing_candidate_is_invalid_evidence():
    runtime, parameter, x, source, candidate = setup()
    certificate = DerivativeCertificate(
        T.TRUE, source, runtime.variable, candidate
    )
    outcome = runtime.checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim(runtime, source, candidate),),
            (),
            certificate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate" in outcome.detail


def test_a_missing_candidate_role_is_invalid_evidence():
    runtime, parameter, x, source, candidate = setup()
    outcome = check(
        runtime,
        claim(runtime, source, candidate),
        source,
        candidate,
        role=None,
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate role" in outcome.detail


def test_a_wrong_candidate_role_is_invalid_evidence():
    runtime, parameter, x, source, candidate = setup()
    outcome = check(
        runtime,
        claim(runtime, source, candidate),
        source,
        candidate,
        role=CandidateRole.SET,
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate role" in outcome.detail


def test_a_candidate_different_from_the_claim_is_invalid_evidence():
    runtime, parameter, x, source, candidate = setup()
    outcome = check(
        runtime,
        claim(runtime, source, candidate),
        source,
        candidate,
        checked=T.number(0),
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate" in outcome.detail


def matching_problem(runtime, source):
    return ProblemSpec(
        "differentiate",
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                source,
            ),
        ),
        runtime.request.roles,
        None,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        interpretation_requirement=(
            runtime.request.interpretation_requirement
        ),
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=runtime.request.value_domain,
        ),
    )


def check_with_problem(runtime, source, candidate, problem):
    certificate = DerivativeCertificate(
        T.TRUE, source, runtime.variable, candidate
    )
    return runtime.checker.check(
        CheckRequest(
            runtime.frame.id,
            (claim(runtime, source, candidate),),
            (),
            certificate,
            problem=problem,
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )


def test_a_matching_problem_binding_is_verified():
    runtime, parameter, x, source, candidate = setup()
    outcome = check_with_problem(
        runtime,
        source,
        candidate,
        matching_problem(runtime, source),
    )
    assert isinstance(outcome, Verified)


def test_a_problem_with_another_parameter_mode_is_refused():
    runtime, parameter, x, source, candidate = setup()
    problem = matching_problem(runtime, source)
    forged = replace(
        problem,
        roles=replace(
            problem.roles,
            parameter_mode=ParameterMode.GENERIC_PARAMETERS,
        ),
    )
    outcome = check_with_problem(runtime, source, candidate, forged)
    assert isinstance(outcome, InvalidEvidence)
    assert "roles" in outcome.detail


def test_a_problem_with_another_target_sort_is_refused():
    runtime, parameter, x, source, candidate = setup()
    problem = ProblemSpec(
        "differentiate",
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                T.number(1),
            ),
        ),
        replace(runtime.request.roles, target_sort=S.RATIONAL),
        None,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        interpretation_requirement=(
            runtime.request.interpretation_requirement
        ),
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=ValueDomain.RATIONAL,
        ),
    )
    outcome = check_with_problem(
        runtime, T.number(1), T.number(0), problem
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "roles" in outcome.detail


def test_a_problem_with_a_forged_role_world_is_refused():
    runtime, parameter, x, source, candidate = setup()
    other = bootstrap_parameterized()
    problem = matching_problem(runtime, source)
    object.__setattr__(
        problem,
        "roles",
        replace(problem.roles, world=other.world.id),
    )
    outcome = check_with_problem(runtime, source, candidate, problem)
    assert isinstance(outcome, InvalidEvidence)
    assert "roles" in outcome.detail


def test_a_problem_with_a_missing_interpretation_requirement_is_refused():
    runtime, parameter, x, source, candidate = setup()
    problem = replace(
        matching_problem(runtime, source),
        interpretation_requirement=None,
    )
    outcome = check_with_problem(runtime, source, candidate, problem)
    assert isinstance(outcome, InvalidEvidence)
    assert "interpretation" in outcome.detail


def test_a_problem_with_another_interpretation_requirement_is_refused():
    runtime, parameter, x, source, candidate = setup()
    problem = replace(
        matching_problem(runtime, source),
        interpretation_requirement=InterpretationRequirement.FORMAL,
    )
    outcome = check_with_problem(runtime, source, candidate, problem)
    assert isinstance(outcome, InvalidEvidence)
    assert "interpretation" in outcome.detail


def test_a_forged_approximate_problem_is_refused():
    runtime, parameter, x, source, candidate = setup()
    problem = matching_problem(runtime, source)
    object.__setattr__(problem, "exactness", Exactness.APPROXIMATE)
    outcome = check_with_problem(runtime, source, candidate, problem)
    assert isinstance(outcome, InvalidEvidence)
    assert "exactness" in outcome.detail
