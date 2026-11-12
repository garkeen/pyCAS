"""The registered rational-logarithmic integration operation over ``Q(x)``.

The operation is exercised directly, without bootstrap, workspace or REPL
wiring: admission, the fixed problem dimensions, the proposal it derives from
the low-level rational-residue search, and every structured refusal.
"""

from dataclasses import replace
from fractions import Fraction

import pytest
from logarithmic_support import (
    LogSetup,
    checker,
    full_context,
    log_setup,
    logarithmic_operation,
    monic_product,
    polynomial,
    rational_view,
    render,
    render_polynomial,
    variable,
    view_of,
)
from support import proposition_in

from cas.algebra.logarithmic_integration import (
    LogarithmicIntegrationBudget,
    rational_log_integral,
)
from cas.algebra.rational import RationalFunction
from cas.kernel.evidence import CheckRequest, Verified
from cas.language.decisions import Reason
from cas.language.execution import ConditionPolicy, ExecutionBudget
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ResultLanguage,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.calculus.integration.logarithmic_operation import (
    LogarithmicIntegrationOperation,
)
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogAntiderivativeCertificate,
    parse_rational_log_antiderivative,
    rational_log_antiderivative_term,
    rational_log_term_set,
)
from cas.math.calculus.integration.rational_view import (
    RationalFunctionView,
)
from cas.operations.capabilities import Capability
from cas.operations.protocols import (
    Admitted,
    ExecutionRequest,
    InvalidRequest,
    OperationRequest,
    Parsed,
    ProblemBuilt,
    ProblemUnsupported,
    ProposalInvalid,
    ProposalUnsupported,
    Proposed,
    Refused,
    ResultSchema,
    ResultShape,
    StructuredResult,
)
from cas.runtime.bootstrap import bootstrap_parameterized
from cas.semantics.conditions import and_all
from cas.syntax import term as T

_FRAGMENTS = (
    "1/x",
    "1/(x^2-1)",
    "2x/(x^2+1)",
    "x^2+1",
    "0",
)


def fragment_value(
    setup: LogSetup, name: str
) -> RationalFunction[Fraction]:
    """One distinguished ``Q(x)`` element of the declared fragment."""
    field = setup.bridge.field
    ring = field.polynomials
    if name == "1/x":
        return field.fraction(ring.one(), ring.generator(0))
    if name == "1/(x^2-1)":
        return field.fraction(ring.one(), monic_product(setup, (-1, 1)))
    if name == "2x/(x^2+1)":
        return field.fraction(
            polynomial(setup, ((1, Fraction(2)),)),
            polynomial(setup, ((2, Fraction(1)), (0, Fraction(1)))),
        )
    if name == "x^2+1":
        return field.of_polynomial(
            polynomial(setup, ((2, Fraction(1)), (0, Fraction(1))))
        )
    if name == "1/(x^2+1)":
        return field.fraction(
            ring.one(),
            polynomial(setup, ((2, Fraction(1)), (0, Fraction(1)))),
        )
    if name == "0":
        return field.zero()
    raise AssertionError(f"unknown fragment {name}")


def source_term(setup: LogSetup, name: str) -> T.Term:
    return render(setup, fragment_value(setup, name))


def request_for(
    setup: LogSetup,
    term: T.Term,
    *,
    target: int | None = None,
    inputs: tuple[T.Term, ...] | None = None,
    region: Proposition | None = None,
    coverage: Coverage = Coverage.ONE_VERIFIED,
    result_language: ResultLanguage | None = None,
    parameter_mode: ParameterMode | None = None,
) -> OperationRequest:
    return OperationRequest(
        setup.frame,
        (term,) if inputs is None else inputs,
        setup.runtime.variable if target is None else target,
        region=region,
        coverage=coverage,
        result_language=result_language,
        parameter_mode=parameter_mode,
    )


def built_execution(
    found: LogarithmicIntegrationOperation,
    request: OperationRequest,
) -> tuple[ProblemBuilt, ExecutionRequest]:
    built = found.build_problem(request)
    assert isinstance(built, ProblemBuilt), built
    execution = ExecutionRequest(
        request,
        built.problem,
        built.algebra,
        request.frame,
        ConditionPolicy.REQUIRE_PROVED,
        ExecutionBudget(),
    )
    return built, execution


def proposal_of(
    found: LogarithmicIntegrationOperation,
    request: OperationRequest,
) -> Proposed:
    built, execution = built_execution(found, request)
    assert built.algebra is not None
    outcome = found.propose(execution)
    assert isinstance(outcome, Proposed), outcome
    return outcome


def expected_claim_region(
    setup: LogSetup,
    source: T.Term,
    part: T.Term,
    arguments: tuple[T.Term, ...],
) -> T.Term:
    """The conjunction of the two definedness regions and every log domain."""
    conditions: list[T.Term] = []
    for term in (source, part):
        view = view_of(setup, term)
        for item in (view.source_domain, view.valid_on):
            if item is not None and item.term not in conditions:
                conditions.append(item.term)
    for argument in arguments:
        condition = T.app(
            setup.signature.head_term(StructuralHead.GT),
            argument,
            T.number(0),
        )
        if condition not in conditions:
            conditions.append(condition)
    return and_all(setup.signature, *conditions)


def expected_result(
    setup: LogSetup, name: str
) -> tuple[T.Term, T.Term, T.Term, tuple[T.Term, ...]]:
    """The low-level search rendered as ``(part, log set, result, arguments)``."""
    value = fragment_value(setup, name)
    search = rational_log_integral(setup.bridge.field, value)
    part = render(setup, search.polynomial_part)
    arguments = tuple(
        render_polynomial(setup, term.argument)
        for term in search.log_terms
    )
    log_terms = rational_log_term_set(
        setup.signature,
        setup.vocabulary.log_function,
        tuple(
            (term.coefficient, argument)
            for term, argument in zip(search.log_terms, arguments)
        ),
    )
    result = rational_log_antiderivative_term(
        setup.signature, part, log_terms
    )
    return part, log_terms, result, arguments


def test_the_registration_fixes_the_operation_contract(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    assert isinstance(found, LogarithmicIntegrationOperation)
    assert found.id == "integrate_rational_logarithmic"
    assert found.version == "1"
    assert found.problem_kind == "integrate_rational_logarithmic"
    assert found.specification_kind == "HasRationalLogAntiderivative"
    assert found.result_schema == ResultSchema(
        frozenset({ResultLanguage.DECOMPOSITION}),
        ResultShape.DECOMPOSITION,
    )
    assert found.result_schema.single_language() is (
        ResultLanguage.DECOMPOSITION
    )
    assert found.capability_requirements == frozenset(
        {Capability.RATIONAL_FUNCTION_FIELD}
    )
    assert found.input_schema.id == (
        "integrate_rational_logarithmic/rational-function"
    )
    assert found.parameter_schema.parse(()) == Parsed(None)
    assert len(found.checker_bindings) == 1
    binding = found.checker_bindings[0]
    assert binding.specification_kind == found.specification_kind
    assert binding.problem_kind == found.problem_kind
    assert binding.checker_id == rational_view(setup).checker_id
    assert binding.target == runtime.variable
    assert binding.candidate_role is CandidateRole.RESULT


def test_admission_accepts_the_rational_fragment(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    for name in _FRAGMENTS:
        request = request_for(setup, source_term(setup, name))
        outcome = found.input_schema.admit(request)
        assert isinstance(outcome, Admitted), (name, outcome)


def test_admission_refuses_outside_the_fragment(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    other = runtime.table.intern("t")
    wrong_target = found.input_schema.admit(
        request_for(setup, T.number(1), target=other)
    )
    assert isinstance(wrong_target, Refused)
    assert wrong_target.reason is Reason.FRAGMENT
    assert wrong_target.report.missing == frozenset({"target_view"})

    two_inputs = found.input_schema.admit(
        request_for(
            setup,
            T.number(1),
            inputs=(T.number(1), T.number(2)),
        )
    )
    assert isinstance(two_inputs, InvalidRequest)

    outside = T.app(setup.vocabulary.log_function, variable(setup))
    bridge_refusal = found.input_schema.admit(
        request_for(setup, outside)
    )
    assert isinstance(bridge_refusal, Refused)
    assert bridge_refusal.reason is Reason.FRAGMENT
    assert bridge_refusal.report.missing


def test_admission_refuses_a_parameter_family(runtime) -> None:
    setup = log_setup(runtime)
    parameterized = bootstrap_parameterized()
    view = rational_view(setup)
    operation = LogarithmicIntegrationOperation(
        setup.signature,
        setup.runtime.frames,
        setup.vocabulary,
        (
            RationalFunctionView(
                parameterized.request,
                setup.bridge.field,
                setup.bridge.parent,
                setup.bridge,
                view.checker_id,
            ),
        ),
        setup.runtime.table.name_of,
        parameterized.variable,
    )
    request = request_for(
        setup, T.number(1), target=parameterized.variable
    )
    refusal = operation.input_schema.admit(request)
    assert isinstance(refusal, Refused)
    assert refusal.reason is Reason.FRAGMENT
    assert refusal.report.missing == frozenset(
        {"coefficient_fraction_field"}
    )


def test_build_problem_fixes_the_request_dimensions(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    term = source_term(setup, "1/x")
    region = proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        T.app(
            setup.signature.head_term(StructuralHead.GT),
            variable(setup),
            T.number(2),
        ),
    )
    request = request_for(setup, term, region=region)
    built = found.build_problem(request)
    assert isinstance(built, ProblemBuilt)
    problem = built.problem
    assert problem.operation == "integrate_rational_logarithmic"
    assert problem.coverage is Coverage.ONE_VERIFIED
    assert problem.result_language is ResultLanguage.DECOMPOSITION
    assert problem.roles == setup.request.roles
    assert problem.region == region
    assert len(problem.inputs) == 1
    assert problem.inputs[0].term == term
    assert built.algebra is setup.request

    wrong_coverage = found.build_problem(
        replace(request, coverage=Coverage.COMPLETE_SET)
    )
    assert isinstance(wrong_coverage, ProblemUnsupported)
    assert wrong_coverage.reason is Reason.FRAGMENT

    wrong_language = found.build_problem(
        replace(request, result_language=ResultLanguage.EXPRESSION)
    )
    assert isinstance(wrong_language, ProblemUnsupported)

    wrong_mode = found.build_problem(
        replace(
            request, parameter_mode=ParameterMode.ALL_PARAMETER_VALUES
        )
    )
    assert isinstance(wrong_mode, ProblemUnsupported)

    wrong_target = found.build_problem(
        replace(request, target=runtime.table.intern("t"))
    )
    assert isinstance(wrong_target, ProblemUnsupported)
    assert wrong_target.missing == frozenset({"target_view"})


def test_the_proposal_matches_the_low_level_search(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    for name in _FRAGMENTS:
        term = source_term(setup, name)
        request = request_for(setup, term)
        built, execution = built_execution(found, request)
        proposed = found.propose(execution)
        assert isinstance(proposed, Proposed), proposed
        proposal = proposed.proposal
        part, log_terms, result, arguments = expected_result(setup, name)
        assert proposal.result == result
        assert proposal.answer_coverage is Coverage.ONE_VERIFIED
        assert isinstance(
            proposal.certificate, RationalLogAntiderivativeCertificate
        )
        claim = parse_rational_log_antiderivative(
            setup.vocabulary, proposal.specifications[0].term
        )
        assert claim is not None
        assert claim.source == term
        assert claim.variable == variable(setup)
        assert claim.polynomial_part == part
        assert claim.log_terms == log_terms
        assert claim.result == result
        certificate = proposal.certificate
        assert certificate.region == claim.region
        assert certificate.source == term
        assert certificate.variable == setup.runtime.variable
        assert certificate.polynomial_part == part
        assert certificate.log_terms == log_terms
        assert certificate.result == result
        assert proposal.structured == StructuredResult(
            "RationalLogAntiderivative",
            (
                ("polynomial_part", part),
                ("log_terms", log_terms),
            ),
        )
        region_term = expected_claim_region(
            setup, term, part, arguments
        )
        assert claim.region == region_term
        if region_term == T.TRUE:
            assert proposal.result_region is None
        else:
            assert proposal.result_region is not None
            assert proposal.result_region.term == region_term
            assert proposal.result_region.definedness == ()
        assert proposal.structured is not None
        verified = checker(setup).check(
            CheckRequest(
                setup.frame,
                proposal.specifications,
                (),
                proposal.certificate,
                problem=built.problem,
                candidate=proposal.result,
                candidate_role=CandidateRole.RESULT,
                context=full_context(setup),
                structured=proposal.structured.components,
            )
        )
        assert isinstance(verified, Verified), (name, verified)


def test_the_proposal_refuses_non_rational_residues(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    request = request_for(
        setup, source_term(setup, "1/(x^2+1)")
    )
    built, execution = built_execution(found, request)
    assert isinstance(built, ProblemBuilt)
    outcome = found.propose(execution)
    assert isinstance(outcome, ProposalUnsupported)
    assert outcome.reason is Reason.FRAGMENT
    assert outcome.missing == frozenset(
        {"rational_residues", "algebraic_logarithmic_part"}
    )
    assert outcome.conditions == ()


def test_budget_exhaustion_reports_no_partial_result(runtime) -> None:
    setup = log_setup(runtime)
    found = replace(
        logarithmic_operation(setup),
        budget=LogarithmicIntegrationBudget(max_degree=0),
    )
    request = request_for(setup, source_term(setup, "1/x"))
    built, execution = built_execution(found, request)
    assert isinstance(built, ProblemBuilt)
    outcome = found.propose(execution)
    assert isinstance(outcome, ProposalUnsupported)
    assert outcome.reason is Reason.BUDGET
    assert outcome.missing == frozenset({"max_degree"})


def test_the_proposal_refuses_mismatched_problem_or_algebra(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    request = request_for(setup, source_term(setup, "1/x"))
    built, execution = built_execution(found, request)
    assert built.algebra is not None

    wrong_operation = found.propose(
        replace(
            execution,
            problem=replace(built.problem, operation="differentiate"),
        )
    )
    assert isinstance(wrong_operation, ProposalInvalid)

    two_inputs = found.propose(
        replace(
            execution,
            problem=replace(
                built.problem, inputs=built.problem.inputs * 2
            ),
        )
    )
    assert isinstance(two_inputs, ProposalInvalid)

    other_algebra = found.propose(
        replace(execution, algebra=replace(built.algebra))
    )
    assert isinstance(other_algebra, ProposalInvalid)


def test_a_requested_region_outside_the_claim_is_guarded(runtime) -> None:
    setup = log_setup(runtime)
    found = logarithmic_operation(setup)
    term = source_term(setup, "1/x")
    outside = proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        T.app(
            setup.signature.head_term(StructuralHead.GT),
            variable(setup),
            T.number(-1),
        ),
    )
    request = request_for(setup, term, region=outside)
    built, execution = built_execution(found, request)
    assert isinstance(built, ProblemBuilt)
    assert built.problem.region == outside
    outcome = found.propose(execution)
    assert isinstance(outcome, ProposalUnsupported)
    assert outcome.reason is Reason.GUARDED
    assert outcome.missing == frozenset({"region_coverage"})
    assert outcome.conditions == (outside,)

    inside = proposition_in(
        setup.runtime.frames,
        setup.frame,
        setup.signature,
        T.app(
            setup.signature.head_term(StructuralHead.GT),
            variable(setup),
            T.number(2),
        ),
    )
    accepted = proposal_of(
        found, request_for(setup, term, region=inside)
    )
    assert accepted.proposal.result_region is not None
    assert accepted.proposal.result_region.term == T.app(
        setup.signature.head_term(StructuralHead.GT),
        variable(setup),
        T.number(0),
    )


def test_the_operation_validates_its_configuration(runtime) -> None:
    setup = log_setup(runtime)
    view = rational_view(setup)
    arguments = (
        setup.signature,
        setup.runtime.frames,
        setup.vocabulary,
    )
    with pytest.raises(TypeError):
        LogarithmicIntegrationOperation(
            *arguments,
            (view,),
            setup.runtime.table.name_of,
            setup.runtime.variable,
            budget=object(),  # type: ignore[arg-type]
        )
    with pytest.raises(ValueError):
        LogarithmicIntegrationOperation(
            *arguments,
            (),
            setup.runtime.table.name_of,
            setup.runtime.variable,
        )
    with pytest.raises(ValueError):
        LogarithmicIntegrationOperation(
            *arguments,
            (view, view),
            setup.runtime.table.name_of,
            setup.runtime.variable,
        )
    with pytest.raises(ValueError):
        LogarithmicIntegrationOperation(
            *arguments,
            (view,),
            setup.runtime.table.name_of,
            runtime.table.intern("t"),
        )
