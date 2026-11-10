"""Specialization through the workspace: candidates, commits and refusals."""

from dataclasses import replace
from fractions import Fraction

from support import (
    commit_now,
    equation,
    head_app,
    runtime_proposition,
    variable,
    view_of,
)

from cas.kernel.commit import CommitProposal, Committed, Rejected
from cas.language.execution import ConditionPolicy, ExecutionBudget
from cas.language.problems import ParameterMode
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.operations.protocols import (
    ExecutionRequest,
    GenericResultInput,
    OperationRequest,
    ProblemBuilt,
    Proposed,
    ValueMappingInput,
)
from cas.runtime import bootstrap_parameterized
from cas.semantics.regions import RegionSpec, region_from_proposition
from cas.semantics.specialization import (
    CoverageClaim,
    GenericResult,
    Specialization,
)
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.workflow.records import OperationStatus
from cas.workflow.workspace import Workspace


def square_source(runtime, a):
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.TIMES,
        a,
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(2)),
    )


def setup():
    runtime = bootstrap_parameterized()
    workspace = Workspace(runtime)
    a_id = runtime.request.parameters[0]
    a = T.symbol(a_id, "a")
    source = workspace.intake(square_source(runtime, a), "F")
    differentiated = workspace.differentiate(source, runtime.variable)
    assert differentiated.status is OperationStatus.VERIFIED
    return runtime, workspace, a_id, a, source, differentiated


def specialized_algebra(runtime):
    """The fixed Q[x] request the specialization operation selects."""
    view = runtime.specialization
    assert view is not None
    return view.request


def propose_with_family(runtime, source, parameter, family, value):
    """Build and propose one specialization without bypassing the operation."""
    operation = runtime.operations.get("specialize")
    assert operation is not None
    request = OperationRequest(
        runtime.frame.id,
        (source.term,),
        target=runtime.variable,
        parameters=(
            ("family", GenericResultInput(family)),
            ("values", ValueMappingInput({parameter: value})),
        ),
    )
    problem_outcome = operation.build_problem(request)
    assert isinstance(problem_outcome, ProblemBuilt)
    execution = ExecutionRequest(
        request,
        problem_outcome.problem,
        problem_outcome.algebra,
        request.frame,
        ConditionPolicy.REQUIRE_PROVED,
        ExecutionBudget(),
    )
    proposal_outcome = operation.propose(execution)
    assert isinstance(proposal_outcome, Proposed)
    return operation, proposal_outcome.proposal, problem_outcome.problem


def test_differentiation_records_the_parameter_family():
    runtime, workspace, _, _, source, differentiated = setup()
    generic = workspace.generic_result(source)
    assert generic is not None
    assert generic is differentiated.generic
    assert generic.coverage_claim is CoverageClaim.ALL_VALUES
    assert generic.is_unconditional
    assert isinstance(generic.valid_on, RegionSpec)
    assert generic.valid_on.condition.term == T.TRUE
    assert generic.excluded_cases == ()
    assert generic.result == differentiated.result.term
    assert (
        generic.correctness_specification
        == differentiated.verifications[0].specification
    )
    assert runtime.store.stats()["judgments"] == 1


def test_a_point_reuses_the_generic_formula_and_is_reverified():
    runtime, workspace, a_id, _, source, _ = setup()
    outcome = workspace.specialize(source, {a_id: 3})
    assert outcome.status is OperationStatus.VERIFIED
    assert outcome.trace == ("generic_formula",)
    assert outcome.detail == ""
    assert outcome.candidate is not None
    assert outcome.verifications
    assert outcome.result is not None
    assert outcome.verifications[0].judgment is not None
    assert workspace.applicability(
        outcome.verifications[0].judgment
    ).is_applicable()
    assert runtime.store.stats()["judgments"] == 2

    candidate = outcome.candidate
    assert candidate.problem.operation == "specialize"
    assert candidate.problem.parameter_mode is ParameterMode.SPECIFIED_VALUES
    assert candidate.problem.target == runtime.variable
    assert not B.free_symbols(candidate.term) & set(
        runtime.request.parameters
    )
    assert runtime.variable in B.free_symbols(candidate.term)

    claim = parse_has_derivative(
        runtime.vocabulary, outcome.verifications[0].specification.term
    )
    assert claim is not None
    assert not B.free_symbols(claim.source) & set(runtime.request.parameters)
    assert not B.free_symbols(claim.candidate) & set(
        runtime.request.parameters
    )
    assert runtime.variable in B.free_symbols(claim.source)
    assert runtime.variable in B.free_symbols(claim.candidate)

    inference = runtime.store.inference_of(
        outcome.verifications[0].judgment
    )
    assert inference.checker_id == "calculus.derivative.specialized"

    specialized = runtime.specialization
    assert specialized is not None
    source_value = view_of(
        runtime,
        claim.source,
        bridge=specialized.bridge,
        request=specialized.request,
    ).value
    candidate_value = view_of(
        runtime,
        claim.candidate,
        bridge=specialized.bridge,
        request=specialized.request,
    ).value
    assert specialized.ring.equal(
        candidate_value, specialized.differential.deriv(source_value)
    )
    assert [event.operation for event in workspace.events()] == [
        "Intake",
        "differentiate",
        "specialize",
    ]


def test_zero_and_fractional_points_are_verified():
    runtime, workspace, a_id, _, source, _ = setup()
    zero = workspace.specialize(source, {a_id: 0})
    assert zero.status is OperationStatus.VERIFIED
    assert zero.result is not None
    assert zero.result.term == T.number(0)
    assert zero.trace == ("generic_formula",)

    half = workspace.specialize(source, {a_id: Fraction(1, 2)})
    assert half.status is OperationStatus.VERIFIED
    assert half.result is not None
    assert half.result.term == variable(runtime)


def test_a_generic_request_still_specializes():
    runtime = bootstrap_parameterized(
        parameter_mode=ParameterMode.GENERIC_PARAMETERS
    )
    workspace = Workspace(runtime)
    a_id = runtime.request.parameters[0]
    a = T.symbol(a_id, "a")
    source = workspace.intake(square_source(runtime, a), "F")
    differentiated = workspace.differentiate(source, runtime.variable)
    assert differentiated.generic is not None
    assert differentiated.generic.coverage_claim is CoverageClaim.GENERIC

    outcome = workspace.specialize(source, {a_id: 4})
    assert outcome.status is OperationStatus.VERIFIED
    assert outcome.result is not None
    assert outcome.result.term == head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(8),
        variable(runtime),
    )


def test_specialization_without_a_family_is_unsupported():
    runtime = bootstrap_parameterized()
    workspace = Workspace(runtime)
    a_id = runtime.request.parameters[0]
    a = T.symbol(a_id, "a")
    source = workspace.intake(square_source(runtime, a), "F")
    before = runtime.store.stats()
    outcome = workspace.specialize(source, {a_id: 1})
    assert outcome.status is OperationStatus.UNSUPPORTED
    assert "differentiate" in outcome.detail
    assert runtime.store.stats() == before
    assert len(workspace.expressions()) == 1


def test_a_family_must_be_visible_for_the_input():
    runtime, workspace, a_id, a, source, differentiated = setup()
    fabricated = GenericResult.assemble(
        result=differentiated.result.term,
        valid_on=region_from_proposition(
            equation(runtime, a, T.number(1))
        ),
        excluded_cases=(),
        correctness_specification=differentiated.verifications[0].specification,
        parameter_mode=ParameterMode.ALL_PARAMETER_VALUES,
    )
    before = runtime.store.stats()
    outcome = workspace.apply(
        "specialize",
        (source,),
        target=runtime.variable,
        parameters=(
            ("family", GenericResultInput(fabricated)),
            ("values", ValueMappingInput({a_id: 1})),
        ),
    )
    assert outcome.status is OperationStatus.INVALID
    assert "visible" in outcome.detail
    assert runtime.store.stats() == before


def test_an_incomplete_or_foreign_point_is_invalid():
    runtime, workspace, a_id, _, source, _ = setup()
    before = runtime.store.stats()
    missing = workspace.specialize(source, {})
    assert missing.status is OperationStatus.INVALID
    extra = workspace.specialize(
        source, {a_id: 1, runtime.variable: 2}
    )
    assert extra.status is OperationStatus.INVALID
    assert runtime.store.stats() == before


def test_a_point_outside_the_generic_validity_recomputes():
    runtime, _, a_id, a, source, differentiated = setup()
    family = GenericResult.assemble(
        result=differentiated.result.term,
        valid_on=region_from_proposition(
            equation(runtime, a, T.number(1))
        ),
        excluded_cases=(),
        correctness_specification=differentiated.verifications[0].specification,
        parameter_mode=ParameterMode.ALL_PARAMETER_VALUES,
    )
    _, outside, _ = propose_with_family(runtime, source, a_id, family, 2)
    assert outside.trace == ("recomputed",)
    assert outside.result == head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(4),
        variable(runtime),
    )

    _, inside, _ = propose_with_family(runtime, source, a_id, family, 1)
    assert inside.trace == ("generic_formula",)


def test_an_excluded_point_recomputes_instead_of_substituting():
    runtime, _, a_id, a, source, differentiated = setup()
    true = runtime_proposition(runtime, T.TRUE)
    excluded = equation(runtime, a, T.number(0))
    family = GenericResult.assemble(
        result=T.number(-999),
        valid_on=region_from_proposition(true),
        excluded_cases=(region_from_proposition(excluded),),
        correctness_specification=differentiated.verifications[0].specification,
        parameter_mode=ParameterMode.ALL_PARAMETER_VALUES,
    )
    assert family.coverage_claim is CoverageClaim.PARTIAL

    _, recomputed, _ = propose_with_family(runtime, source, a_id, family, 0)
    assert recomputed.trace == ("recomputed",)
    assert recomputed.result == T.number(0)

    operation, substituted, problem = propose_with_family(
        runtime, source, a_id, family, 2
    )
    assert substituted.trace == ("generic_formula",)
    assert substituted.result == T.number(-999)
    binding = operation.checker_bindings[0]
    outcome = commit_now(
        runtime.store,
        CommitProposal(
            runtime.frame.id,
            substituted.specifications,
            binding.checker_id,
            binding.problem_kind,
            substituted.specification_kind,
            certificate=substituted.certificate,
            problem=problem,
            candidate=substituted.result,
            candidate_role=CandidateRole.RESULT,
            algebra=specialized_algebra(runtime),
        ),
    )
    assert isinstance(outcome, Rejected)
    assert outcome.refutation is not None


def test_a_hidden_source_cannot_be_specialized():
    runtime, workspace, a_id, _, source, _ = setup()
    assert workspace.undo()
    assert workspace.undo()
    outcome = workspace.specialize(source, {a_id: 1})
    assert outcome.status is OperationStatus.INVALID
    assert "visible" in outcome.detail


def test_multiple_parameters_must_all_be_supplied():
    runtime = bootstrap_parameterized(("a", "b"))
    workspace = Workspace(runtime)
    a_id, b_id = runtime.request.parameters
    a = T.symbol(a_id, "a")
    b = T.symbol(b_id, "b")
    x = variable(runtime)
    source_term = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        head_app(runtime.signature, StructuralHead.PLUS, a, b),
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(2)),
    )
    source = workspace.intake(source_term, "F")
    assert workspace.differentiate(
        source, runtime.variable
    ).status is OperationStatus.VERIFIED

    assert workspace.specialize(source, {a_id: 1}).status is OperationStatus.INVALID
    complete = workspace.specialize(source, {a_id: 1, b_id: 2})
    assert complete.status is OperationStatus.VERIFIED
    assert complete.result is not None
    assert complete.result.term == head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(6),
        variable(runtime),
    )


def test_undo_hides_a_family_and_redo_restores_it():
    runtime, workspace, a_id, _, source, differentiated = setup()
    family = differentiated.generic
    assert workspace.undo()
    assert workspace.generic_result(source) is None
    before = runtime.store.stats()
    assert workspace.specialize(source, {a_id: 3}).status is OperationStatus.UNSUPPORTED
    assert runtime.store.stats() == before
    assert workspace.redo()
    assert workspace.generic_result(source) is family
    assert workspace.specialize(source, {a_id: 3}).status is OperationStatus.VERIFIED


def test_undo_recovers_the_previous_visible_family():
    runtime, workspace, _, _, source, first = setup()
    second = workspace.differentiate(source, runtime.variable)
    assert second.generic is not first.generic
    assert workspace.generic_result(source) is second.generic
    assert workspace.undo()
    assert workspace.generic_result(source) is first.generic
    assert workspace.redo()
    assert workspace.generic_result(source) is second.generic
    assert workspace.undo()
    workspace.intake(T.number(7))
    assert not workspace.redo()
    assert workspace.generic_result(source) is first.generic


def commit_proposal(runtime, operation, proposal, problem):
    binding = operation.checker_bindings[0]
    return commit_now(
        runtime.store,
        CommitProposal(
            runtime.frame.id,
            proposal.specifications,
            binding.checker_id,
            binding.problem_kind,
            proposal.specification_kind,
            certificate=proposal.certificate,
            problem=problem,
            candidate=proposal.result,
            candidate_role=CandidateRole.RESULT,
            algebra=specialized_algebra(runtime),
        ),
    )


def test_the_certificate_binds_the_generic_source_and_mapping():
    runtime, workspace, a_id, _, source, _ = setup()
    family = workspace.generic_result(source)
    assert family is not None
    operation, proposal, problem = propose_with_family(
        runtime, source, a_id, family, 3
    )
    certificate = proposal.certificate
    assert isinstance(certificate, DerivativeCertificate)
    assert certificate.generic_source == source.term
    assert certificate.specialization == Specialization({a_id: 3})
    outcome = commit_proposal(runtime, operation, proposal, problem)
    assert isinstance(outcome, Committed)


def test_a_tampered_specialization_source_is_refused():
    runtime, workspace, a_id, _, source, _ = setup()
    family = workspace.generic_result(source)
    assert family is not None
    operation, proposal, problem = propose_with_family(
        runtime, source, a_id, family, 3
    )
    certificate = proposal.certificate
    assert isinstance(certificate, DerivativeCertificate)
    tampered = replace(certificate, generic_source=T.number(0))
    outcome = commit_now(
        runtime.store,
        CommitProposal(
            runtime.frame.id,
            proposal.specifications,
            operation.checker_bindings[0].checker_id,
            operation.checker_bindings[0].problem_kind,
            proposal.specification_kind,
            certificate=tampered,
            problem=problem,
            candidate=proposal.result,
            candidate_role=CandidateRole.RESULT,
            algebra=specialized_algebra(runtime),
        ),
    )
    assert isinstance(outcome, Rejected)
    assert "generic source" in outcome.detail
