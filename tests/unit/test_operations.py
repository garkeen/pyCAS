"""The open operation protocol and the generic workspace application path."""

from dataclasses import dataclass, replace

import pytest
from support import head_app, runtime_proposition, variable

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.propositions import Proposition
from cas.language.signatures import StructuralHead
from cas.operations.protocols import (
    CheckerBinding,
    MathematicalProposal,
    OperationRequest,
    ProblemBuilt,
    ProposalUnsupported,
    Proposed,
    ValueMappingInput,
)
from cas.operations.registry import OperationError, OperationRegistry
from cas.runtime import bootstrap
from cas.semantics.frames import FrameStore
from cas.semantics.specialization import CoverageClaim
from cas.syntax import term as T
from cas.workflow.records import OperationStatus
from cas.workflow.workspace import Workspace


@dataclass(frozen=True, slots=True)
class HypothesisOperation:
    """A non-derivative operation used to prove the workflow is generic."""

    frames: FrameStore
    coverage: Coverage = Coverage.ONE_VERIFIED
    proposal_coverage: Coverage = Coverage.ONE_VERIFIED
    result_language: ResultLanguage = ResultLanguage.EXPRESSION
    externalizable: tuple[Proposition, ...] = ()
    wrong_inputs: bool = False
    wrong_target: bool = False
    wrong_problem_kind: bool = False
    id: str = "test.hypothesis"
    version: str = "1"
    problem_kind: str = "assume"
    specification_kind: str = "Hypothesis"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    "kernel.hypothesis",
                ),
            ),
        )

    def build_problem(self, request: OperationRequest):
        return ProblemBuilt(
            ProblemSpec(
                operation=(
                    "wrong"
                    if self.wrong_problem_kind
                    else "assume"
                ),
                inputs=(
                    (T.number(0),)
                    if self.wrong_inputs
                    else request.inputs
                ),
                target=(
                    SymbolId(10_000)
                    if self.wrong_target
                    else request.target
                ),
                region=request.region,
                result_language=self.result_language,
                parameter_mode=ParameterMode.SPECIFIED_VALUES,
                coverage=self.coverage,
                externalizable=self.externalizable,
            )
        )

    def propose(self, request: OperationRequest, problem: ProblemSpec):
        del problem
        assumptions = self.frames.assumptions(request.frame)
        if not assumptions:
            return ProposalUnsupported(
                Reason.GUARDED, "the frame has no assumption"
            )
        proposition = assumptions[-1]
        return Proposed(
            MathematicalProposal(
                proposition.term,
                (proposition,),
                self.specification_kind,
                certificate=None,
                answer_coverage=self.proposal_coverage,
            )
        )


def test_the_workflow_applies_a_registered_non_derivative_operation():
    runtime = bootstrap()
    operation = HypothesisOperation(runtime.frames)
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    assumption = workspace.assume(
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        )
    )
    assert assumption.status is OperationStatus.VERIFIED

    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.VERIFIED
    assert result.candidate is not None
    assert len(result.verifications) == 1
    judgment = result.verifications[0].judgment
    assert judgment is not None
    assert runtime.store.get_judgment(judgment).proposition == (
        assumption.proposition
    )
    assert result.result is not None


def test_a_problem_is_derived_from_the_operation_algebra_view():
    runtime = bootstrap()
    operation = runtime.operations.get("differentiate")
    assert operation is not None
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (variable(runtime),),
            runtime.request.target,
        )
    )
    assert isinstance(outcome, ProblemBuilt)
    assert outcome.problem.target == runtime.request.target
    assert (
        outcome.problem.parameter_mode
        is runtime.request.parameter_mode
    )


def test_a_proposal_must_meet_the_requested_coverage():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames, coverage=Coverage.COMPLETE_SET
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    workspace.assume(
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        )
    )
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.INVALID
    assert "coverage" in result.detail
    assert runtime.store.stats() == before


def test_a_matching_set_coverage_is_refused_until_sets_exist():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames,
        coverage=Coverage.COMPLETE_SET,
        proposal_coverage=Coverage.COMPLETE_SET,
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    workspace.assume(
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        )
    )
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert "one-verified" in result.detail
    assert runtime.store.stats() == before


def test_externalizable_premises_are_refused_honestly():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames,
        externalizable=(runtime_proposition(runtime, T.TRUE),),
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert "externalizable" in result.detail
    assert runtime.store.stats() == before


def test_non_expression_result_languages_are_refused_honestly():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames, result_language=ResultLanguage.SET
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert "expression" in result.detail
    assert runtime.store.stats() == before


def test_a_problem_must_describe_the_requested_inputs():
    runtime = bootstrap()
    operation = HypothesisOperation(runtime.frames, wrong_inputs=True)
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    workspace.assume(
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        )
    )
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.INVALID
    assert "inputs" in result.detail
    assert runtime.store.stats() == before


def test_a_problem_kind_must_match_the_checker_binding():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames, wrong_problem_kind=True
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    workspace.assume(
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        )
    )
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.INVALID
    assert "problem kind" in result.detail
    assert runtime.store.stats() == before


def test_a_problem_must_describe_the_requested_target():
    runtime = bootstrap()
    operation = HypothesisOperation(runtime.frames, wrong_target=True)
    runtime = replace(
        runtime,
        operations=OperationRegistry({operation.id: operation}),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    workspace.assume(
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        )
    )
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.INVALID
    assert "target" in result.detail
    assert runtime.store.stats() == before


def test_an_invisible_request_region_is_refused():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    sibling = runtime.frames.create(runtime.frame.id)
    foreign = runtime_proposition(runtime, T.TRUE, sibling.id)
    before = runtime.store.stats()
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=foreign,
    )
    assert result.status is OperationStatus.INVALID
    assert "region" in result.detail
    assert runtime.store.stats() == before


def test_an_unknown_operation_is_refused_without_writing():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    before = runtime.store.stats()
    result = workspace.apply("missing", (source,))
    assert result.status is OperationStatus.UNSUPPORTED
    assert "not registered" in result.detail
    assert runtime.store.stats() == before


def test_the_registry_refuses_inconsistent_registrations():
    runtime = bootstrap()
    operation = HypothesisOperation(runtime.frames)
    with pytest.raises(OperationError):
        OperationRegistry({"other": operation})

    @dataclass(frozen=True, slots=True)
    class Unbound:
        id: str = "test.hypothesis"
        version: str = "1"
        checker_bindings: tuple[CheckerBinding, ...] = ()

        def build_problem(self, request):
            raise AssertionError("unreachable")

        def propose(self, request, problem):
            raise AssertionError("unreachable")

    with pytest.raises(OperationError):
        OperationRegistry({"test.hypothesis": Unbound()})

    @dataclass(frozen=True, slots=True)
    class BadBinding:
        id: str = "test.hypothesis"
        version: str = "1"
        checker_bindings: tuple[object, ...] = ("not a binding",)

        def build_problem(self, request):
            raise AssertionError("unreachable")

        def propose(self, request, problem):
            raise AssertionError("unreachable")

    with pytest.raises(OperationError):
        OperationRegistry({"test.hypothesis": BadBinding()})


def test_an_operation_request_needs_inputs_and_unique_parameters():
    runtime = bootstrap()
    with pytest.raises(ValueError):
        OperationRequest(runtime.frame.id, ())
    with pytest.raises(TypeError):
        OperationRequest(runtime.frame.id, (1,))
    with pytest.raises(TypeError):
        OperationRequest(
            runtime.frame.id,
            (T.number(1),),
            parameters=(("a", "not-an-input"),),
        )
    with pytest.raises(ValueError):
        OperationRequest(
            runtime.frame.id,
            (T.number(1),),
            parameters=(
                ("a", ValueMappingInput({})),
                ("a", ValueMappingInput({})),
            ),
        )


def test_a_proposal_requires_specifications_and_coherent_coverage():
    runtime = bootstrap()
    true = runtime_proposition(runtime, T.TRUE)
    false = runtime_proposition(runtime, T.FALSE)
    with pytest.raises(ValueError):
        MathematicalProposal(T.number(1), (), "HasDerivative", None)
    with pytest.raises(TypeError):
        MathematicalProposal("1", (true,), "HasDerivative", None)
    with pytest.raises(ValueError):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            valid_on=true,
        )
    with pytest.raises(TypeError):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            result_region=T.TRUE,
        )
    with pytest.raises(TypeError):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            coverage="all_values",
        )
    with pytest.raises(TypeError):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            coverage=CoverageClaim.ALL_VALUES,
            valid_on=true,
            excluded_cases=(T.TRUE,),
        )
    with pytest.raises(ValueError):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            coverage=CoverageClaim.ALL_VALUES,
            valid_on=None,
        )
    with pytest.raises(ValueError):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            coverage=CoverageClaim.ALL_VALUES,
            valid_on=false,
        )
    with pytest.raises(ValueError):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            coverage=CoverageClaim.ALL_VALUES,
            valid_on=true,
            excluded_cases=(false,),
        )
