"""The registered Q[x] factorization operation and its fixed problem contract."""

from dataclasses import replace
from fractions import Fraction

import pytest
from support import render_value, runtime_proposition, view_of

from cas.algebra.factorization import (
    FactorizationBudget,
    factor_polynomial_over_q,
)
from cas.frontend import parse
from cas.kernel.verdict import VerdictYes
from cas.language import typing as Ty
from cas.language.decisions import Reason
from cas.language.execution import ConditionPolicy, ExecutionBudget
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ResultLanguage,
    ValueDomain,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.algebra.factorization_operation import (
    FactorizationOperation,
)
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
    HenselIrreducibilityWitness,
    certificate_matches_claim,
    factorization_product_term,
    factorization_radical_term,
    parse_factor_entries,
    parse_factorization,
)
from cas.operations.capabilities import Capability
from cas.operations.protocols import (
    Admitted,
    ExecutionRequest,
    InvalidRequest,
    OperationRequest,
    ProblemBuilt,
    ProblemInvalid,
    ProblemUnsupported,
    ProposalInvalid,
    ProposalUnsupported,
    Refused,
    ResultSchema,
    ResultShape,
)
from cas.runtime.bootstrap import (
    bootstrap_parameterized,
    new_workspace,
)
from cas.semantics import elaborate
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState


def term(runtime, text):
    return parse(text, runtime.table, runtime.signature)


def operation(runtime):
    found = runtime.operations.get("factor_polynomial")
    assert isinstance(found, FactorizationOperation)
    return found


def factor_fixture(runtime, text):
    workspace = new_workspace(runtime)
    source = workspace.intake(term(runtime, text), "source")
    result = workspace.factor_polynomial(source, runtime.variable)
    return workspace, source, result


def request(runtime, text):
    return OperationRequest(
        runtime.frame.id, (term(runtime, text),), runtime.variable
    )


def claim_of(runtime, candidate):
    found = operation(runtime)
    claim = parse_factorization(
        found.vocabulary, candidate.specifications[0].term
    )
    assert claim is not None
    return claim


def test_the_registration_fixes_the_operation_contract(runtime):
    found = operation(runtime)
    assert found.id == "factor_polynomial"
    assert found.version == "1"
    assert found.problem_kind == "factor_polynomial"
    assert found.specification_kind == "HasFactorization"
    assert found.result_schema == ResultSchema(
        frozenset({ResultLanguage.DECOMPOSITION}),
        ResultShape.DECOMPOSITION,
    )
    assert found.result_schema.single_language() is (
        ResultLanguage.DECOMPOSITION
    )
    assert found.capability_requirements == frozenset(
        {Capability.FIELD, Capability.POLYNOMIAL_RING}
    )
    assert len(found.checker_bindings) == 1
    binding = found.checker_bindings[0]
    assert binding.specification_kind == "HasFactorization"
    assert binding.problem_kind == "factor_polynomial"
    assert binding.candidate_role is CandidateRole.RESULT
    assert binding.target is None


def test_the_operation_validates_its_budget(runtime):
    found = operation(runtime)
    with pytest.raises(TypeError):
        replace(found, budget=object())  # type: ignore[arg-type]


def test_the_proposal_refuses_a_mismatched_problem_or_algebra(runtime):
    found = operation(runtime)
    draft = request(runtime, "x^2 - 1")
    built = found.build_problem(draft)
    assert isinstance(built, ProblemBuilt)
    wrong_operation = found.propose(
        ExecutionRequest(
            draft,
            replace(built.problem, operation="differentiate"),
            built.algebra,
            draft.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )
    )
    assert isinstance(wrong_operation, ProposalInvalid)
    two_inputs = found.propose(
        ExecutionRequest(
            draft,
            replace(built.problem, inputs=built.problem.inputs * 2),
            built.algebra,
            draft.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )
    )
    assert isinstance(two_inputs, ProposalInvalid)
    other = replace(found.request)
    wrong_algebra = found.propose(
        ExecutionRequest(
            draft,
            built.problem,
            other,
            draft.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )
    )
    assert isinstance(wrong_algebra, ProposalInvalid)


@pytest.mark.parametrize(
    "text",
    [
        "x^2 - 1",
        "x^4 + 1",
        "6*x^2 + 5*x + 1",
        "(x - 1)^2*(x + 1)^3",
        "7",
        "-2*x^2 + 2",
        "(1/2)*x^2 - 1/2",
    ],
)
def test_admission_accepts_every_declared_in_fragment_input(runtime, text):
    outcome = operation(runtime).input_schema.admit(request(runtime, text))
    assert isinstance(outcome, Admitted)


def test_admission_refuses_the_zero_polynomial(runtime):
    outcome = operation(runtime).input_schema.admit(request(runtime, "0"))
    assert isinstance(outcome, Refused)
    assert outcome.reason is Reason.FRAGMENT
    assert outcome.report.missing == frozenset({"nonzero_polynomial"})


def test_admission_refuses_a_non_polynomial_input(runtime):
    x = T.symbol(runtime.variable, "x")
    reciprocal = T.app(
        runtime.signature.head_term(StructuralHead.POWER), x, T.number(-1)
    )
    outcome = operation(runtime).input_schema.admit(
        OperationRequest(
            runtime.frame.id, (reciprocal,), runtime.variable
        )
    )
    assert isinstance(outcome, Refused)
    assert outcome.reason is Reason.FRAGMENT
    assert "univariate_polynomial_representation" in outcome.report.missing


def test_admission_rejects_a_wrong_input_arity(runtime):
    outcome = operation(runtime).input_schema.admit(
        OperationRequest(
            runtime.frame.id,
            (T.number(1), T.number(2)),
            runtime.variable,
        )
    )
    assert isinstance(outcome, InvalidRequest)


def test_a_missing_target_is_invalid_and_another_target_is_unsupported(
    runtime,
):
    found = operation(runtime)
    source = term(runtime, "x^2 - 1")
    missing = found.build_problem(
        OperationRequest(runtime.frame.id, (source,), None)
    )
    assert isinstance(missing, ProblemInvalid)
    other = found.build_problem(
        OperationRequest(
            runtime.frame.id,
            (source,),
            runtime.table.lookup("y"),
        )
    )
    assert isinstance(other, ProblemUnsupported)
    assert other.reason is Reason.FRAGMENT
    assert other.missing == frozenset({"target_view"})


def test_a_restricted_region_is_refused_without_guessing(runtime):
    region = runtime_proposition(runtime, term(runtime, "x > 0"))
    outcome = operation(runtime).build_problem(
        OperationRequest(
            runtime.frame.id,
            (term(runtime, "x^2 - 1"),),
            runtime.variable,
            region,
        )
    )
    assert isinstance(outcome, ProblemUnsupported)
    assert outcome.reason is Reason.FRAGMENT
    assert outcome.missing == frozenset({"restricted_region"})


def test_explicit_coverage_and_result_language_mismatches_are_refused(
    runtime,
):
    found = operation(runtime)
    source = term(runtime, "x^2 - 1")
    coverage = found.build_problem(
        OperationRequest(
            runtime.frame.id,
            (source,),
            runtime.variable,
            coverage=Coverage.COMPLETE_SET,
        )
    )
    assert isinstance(coverage, ProblemUnsupported)
    assert coverage.missing == frozenset({"coverage:complete_set"})
    language = found.build_problem(
        OperationRequest(
            runtime.frame.id,
            (source,),
            runtime.variable,
            result_language=ResultLanguage.EXPRESSION,
        )
    )
    assert isinstance(language, ProblemUnsupported)
    assert language.missing == frozenset({"result_language:expression"})
    mode = found.build_problem(
        OperationRequest(
            runtime.frame.id,
            (source,),
            runtime.variable,
            parameter_mode=ParameterMode.GENERIC_PARAMETERS,
        )
    )
    assert isinstance(mode, ProblemUnsupported)
    assert mode.missing == frozenset(
        {"parameter_mode:generic_parameters"}
    )


def test_the_built_problem_fixes_the_factorization_dimensions(runtime):
    found = operation(runtime)
    outcome = found.build_problem(request(runtime, "x^2 - 1"))
    assert isinstance(outcome, ProblemBuilt)
    problem = outcome.problem
    assert problem.operation == "factor_polynomial"
    assert problem.target == runtime.variable
    assert problem.region is None
    assert problem.result_language is ResultLanguage.DECOMPOSITION
    assert problem.coverage is Coverage.ONE_VERIFIED
    assert problem.roles == found.request.roles
    assert (
        problem.interpretation_requirement
        == found.request.interpretation_requirement
    )
    assert problem.domain_requirement is not None
    assert problem.domain_requirement.coefficient is ValueDomain.RATIONAL
    assert problem.domain_requirement.values is ValueDomain.REAL
    assert problem.function_inputs == ()
    assert outcome.algebra is found.request


def test_zero_is_refused_by_the_proposal_without_a_partial_result(runtime):
    found = operation(runtime)
    draft = request(runtime, "x^2 - 1")
    built = found.build_problem(draft)
    assert isinstance(built, ProblemBuilt)
    typed_zero = elaborate.typed(
        T.number(0),
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
    )
    assert isinstance(typed_zero, Ty.TypedExpr)
    execution = ExecutionRequest(
        draft,
        replace(built.problem, inputs=(typed_zero,)),
        built.algebra,
        draft.frame,
        ConditionPolicy.REQUIRE_PROVED,
        ExecutionBudget(),
    )
    outcome = found.propose(execution)
    assert isinstance(outcome, ProposalUnsupported)
    assert outcome.reason is Reason.FRAGMENT
    assert outcome.missing == frozenset({"nonzero_polynomial"})


@pytest.mark.parametrize(
    ("text", "budget"),
    [
        ("x^2 - 1", FactorizationBudget(max_prime_trials=0)),
        (
            "x^2 - 3*x + 2",
            FactorizationBudget(max_recombination_tests=0),
        ),
    ],
)
def test_budget_exhaustion_proposes_no_partial_factorization(
    runtime, text, budget
):
    found = operation(runtime)
    draft = request(runtime, text)
    built = found.build_problem(draft)
    assert isinstance(built, ProblemBuilt)
    execution = ExecutionRequest(
        draft,
        built.problem,
        built.algebra,
        draft.frame,
        ConditionPolicy.REQUIRE_PROVED,
        ExecutionBudget(),
    )
    starved = replace(found, budget=budget)
    outcome = starved.propose(execution)
    assert isinstance(outcome, ProposalUnsupported)
    assert outcome.reason is Reason.BUDGET
    assert outcome.missing == frozenset({"factorization_budget"})


def test_x_squared_minus_one_publishes_the_claim_product_and_structured_result(
    runtime,
):
    _, source, result = factor_fixture(runtime, "x^2 - 1")
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    candidate = result.candidate
    assert candidate is not None
    assert candidate.term == result.result.term
    assert candidate.candidate_role is CandidateRole.RESULT
    assert candidate.problem.result_language is ResultLanguage.DECOMPOSITION
    assert candidate.problem.coverage is Coverage.ONE_VERIFIED
    assert candidate.problem.region is None
    assert result.region is None
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED
    assert result.verifications[0].judgment is not None
    claim = claim_of(runtime, candidate)
    assert claim.source == source.term
    assert claim.variable.symbol_id == runtime.variable
    assert claim.unit == T.number(1)
    entries = parse_factor_entries(runtime.signature, claim.factors)
    assert entries is not None
    assert len(entries) == 2
    found = operation(runtime)
    source_view = view_of(runtime, source.term)
    record = factor_polynomial_over_q(found.ring, source_view.value)
    rendered_record = {
        runtime.bridge.render(source_view, factor).term: multiplicity
        for factor, multiplicity in record.factors
    }
    assert dict(entries) == rendered_record
    assert candidate.term == factorization_product_term(
        runtime.signature, claim.unit, claim.factors
    )
    assert result.structured is not None
    assert result.structured.kind == "factorization"
    assert result.structured.components == (
        ("unit", claim.unit),
        ("factors", claim.factors),
    )
    assert candidate.structured == result.structured.components
    certificate = candidate.certificate
    assert isinstance(certificate, FactorizationCertificate)
    assert certificate_matches_claim(certificate, claim)
    assert certificate.radical == factorization_radical_term(
        runtime.signature, entries
    )
    assert certificate.irreducibility is None


def test_a_nonlinear_factorization_carries_a_hensel_witness(runtime):
    _, _, result = factor_fixture(runtime, "x^4 + 1")
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    certificate = candidate.certificate
    assert isinstance(certificate, FactorizationCertificate)
    witness = certificate.irreducibility
    assert isinstance(witness, HenselIrreducibilityWitness)
    assert witness.prime > 1
    assert witness.precision >= 1
    assert witness.lifted


def test_a_nonmonic_rational_input_keeps_the_leading_unit(runtime):
    _, _, result = factor_fixture(runtime, "6*x^2 + 5*x + 1")
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    claim = claim_of(runtime, candidate)
    assert claim.unit == T.number(6)
    entries = parse_factor_entries(runtime.signature, claim.factors)
    assert entries is not None
    assert len(entries) == 2
    assert sorted(multiplicity for _, multiplicity in entries) == [1, 1]


def test_repeated_factors_are_encoded_with_multiplicities(runtime):
    _, _, result = factor_fixture(runtime, "(x - 1)^2*(x + 1)^3")
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    claim = claim_of(runtime, candidate)
    entries = parse_factor_entries(runtime.signature, claim.factors)
    assert entries is not None
    assert sorted(multiplicity for _, multiplicity in entries) == [2, 3]


def test_a_nonzero_constant_is_its_own_unit_with_an_empty_factor_set(runtime):
    _, _, result = factor_fixture(runtime, "7")
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    claim = claim_of(runtime, candidate)
    assert claim.unit == T.number(7)
    assert parse_factor_entries(runtime.signature, claim.factors) == ()
    certificate = candidate.certificate
    assert isinstance(certificate, FactorizationCertificate)
    assert certificate.radical == T.number(1)
    assert certificate.irreducibility is None
    assert result.result is not None
    assert result.result.term == T.number(7)


def test_negative_and_rational_leading_units_are_in_fragment(runtime):
    for text, expected in (
        ("-2*x^2 + 2", T.number(-2)),
        ("(1/2)*x^2 - 1/2", T.number(Fraction(1, 2))),
    ):
        _, _, result = factor_fixture(runtime, text)
        assert result.status is OperationStatus.VERIFIED, result.detail
        candidate = result.candidate
        assert candidate is not None
        claim = claim_of(runtime, candidate)
        assert claim.unit == expected


def test_a_verified_candidate_equals_the_search_record(runtime):
    found = operation(runtime)
    value = found.ring.mul(
        found.ring.constant(Fraction(3)),
        found.ring.mul(
            found.ring.add(
                found.ring.monomial((1,), Fraction(1)),
                found.ring.constant(Fraction(-1)),
            ),
            found.ring.add(
                found.ring.monomial((1,), Fraction(1)),
                found.ring.constant(Fraction(1)),
            ),
        ),
    )
    workspace = new_workspace(runtime)
    source = workspace.intake(render_value(runtime, value), "source")
    result = workspace.factor_polynomial(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    claim = claim_of(runtime, candidate)
    record = factor_polynomial_over_q(found.ring, value)
    assert claim.unit == T.number(record.unit)
    entries = parse_factor_entries(runtime.signature, claim.factors)
    assert entries is not None
    view = view_of(runtime, T.number(1))
    rendered_record = {
        runtime.bridge.render(view, factor).term: multiplicity
        for factor, multiplicity in record.factors
    }
    assert dict(entries) == rendered_record


def test_the_parameterized_runtime_has_no_factorization_registration():
    runtime = bootstrap_parameterized()
    assert runtime.operations.get("factor_polynomial") is None
    assert runtime.table.lookup("HasFactorization") is None


def test_the_checker_reverifies_the_registered_candidate(runtime):
    workspace, _, result = factor_fixture(runtime, "x^3 + x + 1")
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    checked = workspace.check_candidate(candidate.id)
    assert checked.status is OperationStatus.VERIFIED, checked.detail
    assert checked.result is not None
    assert checked.result.term == candidate.term
    verdict = workspace.decide_candidate(candidate.id)
    assert isinstance(verdict, VerdictYes)
    assert verdict.receipt.checker_id == "algebra.factorization"
