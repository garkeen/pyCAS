"""The open operation protocol and the generic workspace application path."""

from dataclasses import dataclass, replace

import pytest
from support import head_app, runtime_proposition, variable

from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.signatures import StructuralHead
from cas.operations.protocols import (
    CheckerBinding,
    MathematicalProposal,
    OperationRequest,
    ProblemBuilt,
    ProposalUnsupported,
    Proposed,
    RationalInput,
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
                operation="hypothesis",
                inputs=request.inputs,
                target=request.target,
                target_sort=S.REAL,
                region=request.region,
                result_language=ResultLanguage.EXPRESSION,
                parameter_mode=ParameterMode.SPECIFIED_VALUES,
                coverage=Coverage.ONE_VERIFIED,
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


def test_an_operation_request_needs_inputs_and_unique_parameters():
    runtime = bootstrap()
    with pytest.raises(ValueError):
        OperationRequest(runtime.frame.id, ())
    with pytest.raises(ValueError):
        OperationRequest(
            runtime.frame.id,
            (T.number(1),),
            parameters=(
                ("a", RationalInput(1)),
                ("a", RationalInput(2)),
            ),
        )


def test_a_proposal_requires_specifications_and_coherent_coverage():
    runtime = bootstrap()
    true = runtime_proposition(runtime, T.TRUE)
    false = runtime_proposition(runtime, T.FALSE)
    with pytest.raises(ValueError):
        MathematicalProposal(T.number(1), (), "HasDerivative", None)
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
