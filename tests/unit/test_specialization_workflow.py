"""Specialization through the workspace: candidates, commits and refusals."""

from fractions import Fraction

from support import equation, head_app, runtime_proposition, variable

from cas.language.problems import ParameterMode
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime import bootstrap_parameterized
from cas.semantics.specialization import (
    CoverageClaim,
    GenericResult,
)
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, SpecializationPath
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


def test_differentiation_records_the_parameter_family():
    runtime, workspace, _, _, source, differentiated = setup()
    generic = workspace.generic_result(source)
    assert generic is not None
    assert generic is differentiated.generic
    assert generic.coverage_claim is CoverageClaim.ALL_VALUES
    assert generic.is_unconditional
    assert generic.excluded_cases == ()
    assert generic.result == differentiated.result.term
    assert generic.correctness_specification == differentiated.verification.specification
    assert runtime.store.stats()["judgments"] == 1


def test_a_point_reuses_the_generic_formula_and_is_reverified():
    runtime, workspace, a_id, _, source, _ = setup()
    outcome = workspace.specialize(source, {a_id: 3})
    assert outcome.status is OperationStatus.VERIFIED
    assert outcome.path is SpecializationPath.GENERIC_FORMULA
    assert outcome.detail == ""
    assert outcome.candidate is not None
    assert outcome.verification is not None
    assert outcome.result is not None
    assert outcome.verification.judgment is not None
    assert workspace.applicability(
        outcome.verification.judgment
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
        runtime.vocabulary, outcome.verification.specification.term
    )
    assert claim is not None
    assert not B.free_symbols(claim.source) & set(runtime.request.parameters)
    assert not B.free_symbols(claim.candidate) & set(
        runtime.request.parameters
    )
    assert runtime.variable in B.free_symbols(claim.source)
    assert runtime.variable in B.free_symbols(claim.candidate)

    inference = runtime.store.inference_of(outcome.verification.judgment)
    assert inference.checker_id == "calculus.derivative.specialized"

    specialized = runtime.specialization
    assert specialized is not None
    source_value = specialized.bridge.to_value(claim.source)
    candidate_value = specialized.bridge.to_value(claim.candidate)
    assert source_value is not None
    assert candidate_value is not None
    assert specialized.ring.equal(
        candidate_value, specialized.differential.deriv(source_value)
    )
    assert [event.operation for event in workspace.events()] == [
        "Intake",
        "Differentiate",
        "Specialize",
    ]


def test_zero_and_fractional_points_are_verified():
    runtime, workspace, a_id, _, source, _ = setup()
    zero = workspace.specialize(source, {a_id: 0})
    assert zero.status is OperationStatus.VERIFIED
    assert zero.result is not None
    assert zero.result.term == T.number(0)
    assert zero.path is SpecializationPath.GENERIC_FORMULA

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
    runtime, workspace, a_id, a, source, differentiated = setup()
    family = GenericResult.assemble(
        result=differentiated.result.term,
        valid_on=equation(runtime, a, T.number(1)),
        excluded_cases=(),
        correctness_specification=differentiated.verification.specification,
        parameter_mode=ParameterMode.ALL_PARAMETER_VALUES,
    )
    outside = workspace.specialize(source, {a_id: 2}, generic=family)
    assert outside.status is OperationStatus.VERIFIED
    assert outside.path is SpecializationPath.RECOMPUTED
    assert outside.result is not None
    assert outside.result.term == head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.number(4),
        variable(runtime),
    )

    inside = workspace.specialize(source, {a_id: 1}, generic=family)
    assert inside.status is OperationStatus.VERIFIED
    assert inside.path is SpecializationPath.GENERIC_FORMULA


def test_an_excluded_point_recomputes_instead_of_substituting():
    runtime, workspace, a_id, a, source, differentiated = setup()
    true = runtime_proposition(runtime, T.TRUE)
    excluded = equation(runtime, a, T.number(0))
    family = GenericResult.assemble(
        result=T.number(-999),
        valid_on=true,
        excluded_cases=(excluded,),
        correctness_specification=differentiated.verification.specification,
        parameter_mode=ParameterMode.ALL_PARAMETER_VALUES,
    )
    assert family.coverage_claim is CoverageClaim.PARTIAL

    recomputed = workspace.specialize(source, {a_id: 0}, generic=family)
    assert recomputed.status is OperationStatus.VERIFIED
    assert recomputed.path is SpecializationPath.RECOMPUTED
    assert recomputed.result is not None
    assert recomputed.result.term == T.number(0)

    bad_substitution = workspace.specialize(source, {a_id: 2}, generic=family)
    assert bad_substitution.status is OperationStatus.REFUTED
    assert bad_substitution.result is None
    assert bad_substitution.verification is not None
    assert bad_substitution.verification.judgment is None


def test_a_hidden_source_cannot_be_specialized():
    runtime, workspace, a_id, _, source, _ = setup()
    assert workspace.undo()
    assert workspace.undo()
    outcome = workspace.specialize(source, {a_id: 1})
    assert outcome.status is OperationStatus.UNSUPPORTED
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
