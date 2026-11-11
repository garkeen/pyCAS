"""The open operation protocol and the generic workspace application path."""

from dataclasses import dataclass, replace

import pytest
from support import (
    head_app,
    runtime_proposition,
    structural,
    typed_in,
    variable,
)

from cas.foundation.ids import SymbolId
from cas.frontend import parse
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    VariableRoles,
)
from cas.language.propositions import Proposition
from cas.language.sets import set_term
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.operations.capabilities import Capability
from cas.operations.parameters import EMPTY_PARAMETER_SCHEMA
from cas.operations.protocols import (
    Admitted,
    CheckerBinding,
    ExecutionRequest,
    InputSchema,
    MathematicalProposal,
    OperationRequest,
    ParameterSchema,
    ProblemBuilt,
    ProblemUnsupported,
    ProposalUnsupported,
    Proposed,
    ResultSchema,
    ResultShape,
    StructuredResult,
    ValueMappingInput,
)
from cas.operations.registry import OperationError, OperationRegistry
from cas.runtime import bootstrap, bootstrap_elementary, bootstrap_parameterized
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.semantics.specialization import CoverageClaim
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState
from cas.workflow.workspace import Workspace


@dataclass(frozen=True, slots=True)
class HypothesisOperation:
    """A non-derivative operation used to prove the workflow is generic."""

    frames: FrameStore
    signature: LanguageSignature
    algebra: AlgebraRequest | None = None
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
    bindings: tuple[CheckerBinding, ...] | None = None

    def __post_init__(self) -> None:
        if self.bindings is not None:
            object.__setattr__(self, "checker_bindings", self.bindings)
            return
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

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("test/hypothesis", lambda request: Admitted())

    @property
    def parameter_schema(self) -> ParameterSchema[None]:
        return EMPTY_PARAMETER_SCHEMA

    @property
    def result_schema(self) -> ResultSchema:
        shape = {
            ResultLanguage.EXPRESSION: ResultShape.EXPRESSION,
            ResultLanguage.PROPOSITION: ResultShape.PROPOSITION,
            ResultLanguage.SET: ResultShape.SET,
            ResultLanguage.DECOMPOSITION: ResultShape.DECOMPOSITION,
        }[self.result_language]
        return ResultSchema(frozenset({self.result_language}), shape)

    @property
    def capability_requirements(self) -> frozenset[Capability]:
        return frozenset()

    def build_problem(self, request: OperationRequest):
        if self.wrong_inputs:
            inputs = (
                typed_in(
                    self.frames,
                    request.frame,
                    self.signature,
                    T.number(0),
                ),
            )
        else:
            inputs = tuple(
                typed_in(
                    self.frames, request.frame, self.signature, term
                )
                for term in request.inputs
            )
        algebra = None if self.wrong_target else self.algebra
        target = None if self.wrong_target else request.target
        domain_requirement = (
            None
            if algebra is None
            else DomainRequirement(
                coefficient=algebra.coefficient_domain,
                values=algebra.value_domain,
            )
        )
        return ProblemBuilt(
            ProblemSpec(
                operation=(
                    "wrong"
                    if self.wrong_problem_kind
                    else "assume"
                ),
                inputs=inputs,
                roles=VariableRoles(
                    target,
                    (),
                    ParameterMode.SPECIFIED_VALUES,
                    self.frames.world.id,
                    S.REAL if target is not None else None,
                ),
                region=request.region,
                result_language=self.result_schema.single_language(),
                coverage=self.coverage,
                externalizable=self.externalizable,
                interpretation_requirement=(
                    algebra.interpretation_requirement
                    if algebra is not None
                    else None
                ),
                domain_requirement=domain_requirement,
            ),
            algebra=algebra,
        )

    def propose(self, execution: ExecutionRequest):
        request = execution.request
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
    operation = HypothesisOperation(
        runtime.frames, runtime.signature, algebra=runtime.request
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
        runtime.frames,
        runtime.signature,
        algebra=runtime.request,
        coverage=Coverage.COMPLETE_SET,
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
        runtime.signature,
        algebra=runtime.request,
        coverage=Coverage.COMPLETE_SET,
        proposal_coverage=Coverage.COMPLETE_SET,
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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


def test_the_request_externalizable_set_reaches_the_fixed_problem():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames, runtime.signature, algebra=runtime.request
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
    premise = runtime_proposition(runtime, T.TRUE)
    result = workspace.apply(
        operation.id,
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )
    assert result.status is OperationStatus.VERIFIED
    assert result.candidate is not None
    assert result.candidate.problem.externalizable == (premise,)
    assert result.task is not None
    assert result.task.problem.externalizable == (premise,)
    assert result.task.state is TaskState.COMPLETED


def test_an_operation_built_externalizable_set_is_not_trusted():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames,
        runtime.signature,
        algebra=runtime.request,
        externalizable=(runtime_proposition(runtime, T.TRUE),),
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
    result = workspace.apply(
        operation.id, (source,), target=runtime.variable
    )
    assert result.status is OperationStatus.VERIFIED
    assert result.task is not None
    assert result.task.problem.externalizable == ()


def test_a_complete_set_request_cannot_externalize_premises():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames,
        runtime.signature,
        algebra=runtime.request,
        result_language=ResultLanguage.SET,
        coverage=Coverage.COMPLETE_SET,
        proposal_coverage=Coverage.COMPLETE_SET,
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
    )
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    premise = runtime_proposition(runtime, T.TRUE)
    before = runtime.store.stats()
    result = workspace.apply(
        operation.id,
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )
    assert result.status is OperationStatus.INVALID
    assert "a complete-set request cannot externalize" in result.detail
    assert result.candidate is None
    assert result.result is None
    assert result.task is None
    assert runtime.store.stats() == before


def test_a_set_problem_needs_a_set_result():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames,
        runtime.signature,
        algebra=runtime.request,
        result_language=ResultLanguage.SET,
        coverage=Coverage.SOUND_SET,
        proposal_coverage=Coverage.SOUND_SET,
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
    assert result.detail == "a set problem needs a Set result"
    assert runtime.store.stats() == before


def test_a_decomposition_problem_needs_a_structured_result():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames,
        runtime.signature,
        algebra=runtime.request,
        result_language=ResultLanguage.DECOMPOSITION,
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
    assert (
        result.detail
        == "a decomposition problem needs a structured result"
    )
    assert runtime.store.stats() == before


def test_a_problem_must_describe_the_requested_inputs():
    runtime = bootstrap()
    operation = HypothesisOperation(
        runtime.frames, runtime.signature, algebra=runtime.request,
        wrong_inputs=True
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
        runtime.frames, runtime.signature, algebra=runtime.request,
        wrong_problem_kind=True
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
    operation = HypothesisOperation(
        runtime.frames, runtime.signature, algebra=runtime.request,
        wrong_target=True
    )
    runtime = replace(
        runtime,
        operations=OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        ),
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
    operation = HypothesisOperation(
        runtime.frames, runtime.signature, algebra=runtime.request
    )
    with pytest.raises(OperationError):
        OperationRegistry(
            {"other": operation},
            provided_capabilities=frozenset(Capability),
        )

    @dataclass(frozen=True, slots=True)
    class Unbound:
        id: str = "test.hypothesis"
        version: str = "1"
        checker_bindings: tuple[CheckerBinding, ...] = ()

        def build_problem(self, request):
            raise AssertionError("unreachable")

        def propose(self, execution):
            raise AssertionError("unreachable")

    with pytest.raises(OperationError):
        OperationRegistry(
            {"test.hypothesis": Unbound()},
            provided_capabilities=frozenset(Capability),
        )

    @dataclass(frozen=True, slots=True)
    class BadBinding:
        id: str = "test.hypothesis"
        version: str = "1"
        checker_bindings: tuple[object, ...] = ("not a binding",)

        @property
        def input_schema(self) -> InputSchema:
            return InputSchema(
                "test/hypothesis", lambda request: Admitted()
            )

        @property
        def parameter_schema(self) -> ParameterSchema[None]:
            return EMPTY_PARAMETER_SCHEMA

        @property
        def result_schema(self) -> ResultSchema:
            return ResultSchema(
                frozenset({ResultLanguage.EXPRESSION}),
                ResultShape.EXPRESSION,
            )

        @property
        def capability_requirements(self) -> frozenset[Capability]:
            return frozenset()

        def build_problem(self, request):
            raise AssertionError("unreachable")

        def propose(self, execution):
            raise AssertionError("unreachable")

    with pytest.raises(OperationError):
        OperationRegistry(
            {"test.hypothesis": BadBinding()},
            provided_capabilities=frozenset(Capability),
        )


def test_the_registry_refuses_an_ambiguous_generic_and_specific_binding():
    runtime = bootstrap()
    generic = CheckerBinding(
        "Hypothesis", "assume", "kernel.hypothesis"
    )
    specific = CheckerBinding(
        "Hypothesis",
        "assume",
        "kernel.hypothesis",
        target=runtime.variable,
    )
    operation = HypothesisOperation(
        runtime.frames,
        runtime.signature,
        bindings=(generic, specific),
    )
    with pytest.raises(OperationError, match="ambiguous"):
        OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        )


def test_the_registry_accepts_distinct_target_bindings():
    runtime = bootstrap()
    first = CheckerBinding(
        "Hypothesis", "assume", "kernel.hypothesis", target=SymbolId(1)
    )
    second = CheckerBinding(
        "Hypothesis", "assume", "kernel.hypothesis", target=SymbolId(2)
    )
    operation = HypothesisOperation(
        runtime.frames,
        runtime.signature,
        bindings=(first, second),
    )
    registry = OperationRegistry(
        {operation.id: operation},
        provided_capabilities=frozenset(Capability),
    )
    assert registry.get(operation.id) is operation


def test_the_registry_requires_input_and_result_schemas():
    @dataclass(frozen=True, slots=True)
    class NoSchemas:
        id: str = "test.hypothesis"
        version: str = "1"
        checker_bindings: tuple[CheckerBinding, ...] = (
            CheckerBinding("Hypothesis", "assume", "kernel.hypothesis"),
        )

        @property
        def input_schema(self) -> object:
            return object()

        @property
        def parameter_schema(self) -> ParameterSchema[None]:
            return EMPTY_PARAMETER_SCHEMA

        @property
        def result_schema(self) -> ResultSchema:
            return ResultSchema(
                frozenset({ResultLanguage.EXPRESSION}),
                ResultShape.EXPRESSION,
            )

        def build_problem(self, request):
            raise AssertionError("unreachable")

        def propose(self, execution):
            raise AssertionError("unreachable")

    with pytest.raises(OperationError, match="input schema"):
        OperationRegistry(
            {"test.hypothesis": NoSchemas()},
            provided_capabilities=frozenset(Capability),
        )


def test_result_schemas_accept_their_declared_shapes(runtime):
    x = variable(runtime)
    proposition = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            x,
            T.number(0),
        ),
    )
    set_view = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        set_term(runtime.signature, (x,)),
    )
    structured = StructuredResult(
        "hermite", (("polynomial_part", x),)
    )
    assert ResultSchema(
        frozenset({ResultLanguage.EXPRESSION}), ResultShape.EXPRESSION
    ).validate(result=x, structured=None, typed=None) is None
    assert ResultSchema(
        frozenset({ResultLanguage.PROPOSITION}), ResultShape.PROPOSITION
    ).validate(
        result=proposition.term, structured=None, typed=proposition
    ) is None
    assert ResultSchema(
        frozenset({ResultLanguage.SET}), ResultShape.SET
    ).validate(
        result=set_view.term,
        structured=None,
        typed=set_view,
        set_term=True,
    ) is None
    assert ResultSchema(
        frozenset({ResultLanguage.DECOMPOSITION}),
        ResultShape.DECOMPOSITION,
    ).validate(result=x, structured=structured, typed=None) is None


def test_a_set_result_requires_an_explicit_structural_check(runtime):
    x = variable(runtime)
    set_view = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        set_term(runtime.signature, (x,)),
    )
    set_schema = ResultSchema(
        frozenset({ResultLanguage.SET}), ResultShape.SET
    )
    refusal = "a Set result needs an explicit structural Set check"
    assert set_schema.validate(
        result=set_view.term, structured=None, typed=set_view
    ) == refusal
    assert set_schema.validate(
        result=set_view.term,
        structured=None,
        typed=set_view,
        set_term=None,
    ) == refusal
    assert set_schema.validate(
        result=set_view.term,
        structured=None,
        typed=set_view,
        set_term=True,
    ) is None
    assert set_schema.validate(
        result=x, structured=None, typed=None, set_term=False
    ) == "a set problem needs a Set result"


def test_result_shapes_refuse_mismatched_payloads(runtime):
    x = variable(runtime)
    scalar = typed_in(
        runtime.frames, runtime.frame.id, runtime.signature, x
    )
    structured = StructuredResult(
        "hermite", (("polynomial_part", x),)
    )
    proposition_schema = ResultSchema(
        frozenset({ResultLanguage.PROPOSITION}), ResultShape.PROPOSITION
    )
    assert proposition_schema.validate(
        result=x, structured=None, typed=scalar
    ) == "a proposition result must be a proposition"
    assert proposition_schema.validate(
        result=x, structured=None, typed=None
    ) == "a proposition result must be a proposition"
    set_schema = ResultSchema(
        frozenset({ResultLanguage.SET}), ResultShape.SET
    )
    assert set_schema.validate(
        result=x, structured=None, typed=scalar, set_term=True
    ) == "a Set result must have a set sort"
    assert set_schema.validate(
        result=x, structured=None, typed=scalar, set_term=False
    ) == "a set problem needs a Set result"
    assert set_schema.validate(
        result=x, structured=None, typed=None, set_term=True
    ) == "a Set result must be a Set term with a set sort"
    assert set_schema.validate(
        result=x, structured=None, typed=None, set_term=None
    ) == "a Set result needs an explicit structural Set check"
    decomposition_schema = ResultSchema(
        frozenset({ResultLanguage.DECOMPOSITION}),
        ResultShape.DECOMPOSITION,
    )
    assert decomposition_schema.validate(
        result=x, structured=None, typed=None
    ) == "a decomposition problem needs a structured result"
    expression_schema = ResultSchema(
        frozenset({ResultLanguage.EXPRESSION}), ResultShape.EXPRESSION
    )
    assert expression_schema.validate(
        result=x, structured=structured, typed=None
    ) == "an expression problem cannot carry a decomposition"


def test_a_result_schema_refuses_a_shape_language_mismatch():
    with pytest.raises(ValueError, match="result shape"):
        ResultSchema(
            frozenset({ResultLanguage.SET}), ResultShape.EXPRESSION
        )
    with pytest.raises(ValueError, match="result shape"):
        ResultSchema(
            frozenset(
                {ResultLanguage.EXPRESSION, ResultLanguage.PROPOSITION}
            ),
            ResultShape.EXPRESSION,
        )


def test_an_out_of_fragment_input_is_refused_by_the_problem_builder():
    runtime = bootstrap()
    operation = runtime.operations.get("polynomial_gcd")
    assert operation is not None
    x = variable(runtime)
    reciprocal = T.app(
        structural(runtime.signature, StructuralHead.POWER),
        x,
        T.number(-1),
    )
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (x, reciprocal),
            runtime.variable,
        )
    )
    assert isinstance(outcome, ProblemUnsupported)
    assert outcome.problem is not None
    assert "univariate_polynomial_representation" in outcome.missing


def test_an_out_of_fragment_input_creates_a_blocked_task():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    x = variable(runtime)
    left = workspace.intake(x)
    reciprocal = workspace.intake(
        T.app(
            structural(runtime.signature, StructuralHead.POWER),
            x,
            T.number(-1),
        )
    )
    before = runtime.store.stats()
    result = workspace.gcd(left, reciprocal, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.task is not None
    assert result.task.state is TaskState.BLOCKED
    assert result.blocker is not None
    assert "univariate_polynomial_representation" in result.blocker.missing
    assert runtime.store.stats() == before


def test_an_operation_request_needs_inputs_and_unique_parameters():
    runtime = bootstrap()
    with pytest.raises(ValueError):
        OperationRequest(runtime.frame.id, ())
    with pytest.raises(TypeError):
        OperationRequest(runtime.frame.id, (1,))
    request = OperationRequest(
        runtime.frame.id,
        (T.number(1),),
        parameters=(("a", "not-an-input"),),
    )
    assert request.parameters == (("a", "not-an-input"),)
    with pytest.raises(TypeError):
        OperationRequest(
            runtime.frame.id,
            (T.number(1),),
            parameters=[("a", ValueMappingInput({}))],  # type: ignore[arg-type]
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
    with pytest.raises(ValueError):
        OperationRequest(
            runtime.frame.id,
            (T.number(1),),
            parameters=(("", ValueMappingInput({})),),
        )


def _partial_condition(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            head_app(
                runtime.signature,
                StructuralHead.POWER,
                variable(runtime),
                T.number(-1),
            ),
            T.number(1),
        ),
    )


def test_an_operation_request_region_must_be_total(runtime):
    partial = _partial_condition(runtime)
    assert partial.definedness
    with pytest.raises(ValueError, match="total condition"):
        OperationRequest(
            runtime.frame.id, (T.number(1),), region=partial
        )
    total = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )
    request = OperationRequest(
        runtime.frame.id, (T.number(1),), region=total
    )
    assert request.region is total


def test_a_proposal_region_payload_must_be_total(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    partial = _partial_condition(runtime)
    assert partial.definedness
    with pytest.raises(ValueError, match="total condition"):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            result_region=partial,
        )
    with pytest.raises(ValueError, match="total condition"):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            coverage=CoverageClaim.PARTIAL,
            valid_on=partial,
        )
    with pytest.raises(ValueError, match="total condition"):
        MathematicalProposal(
            T.number(1),
            (true,),
            "HasDerivative",
            None,
            coverage=CoverageClaim.PARTIAL,
            valid_on=true,
            excluded_cases=(partial,),
        )
    proposal = MathematicalProposal(
        T.number(1),
        (true,),
        "HasDerivative",
        None,
        result_region=true,
    )
    assert proposal.result_region is true


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


@pytest.mark.parametrize("factory, expression", [(bootstrap, "x^2"), (bootstrap_elementary, "sqrt(x)")])
def test_differentiation_preserves_and_verifies_the_requested_region(factory, expression):
    runtime = factory()
    workspace = Workspace(runtime)
    source = workspace.intake(parse(expression, runtime.table, runtime.signature))
    region = runtime_proposition(runtime, parse("x > 2", runtime.table, runtime.signature))
    result = workspace.apply("differentiate", (source,), target=runtime.variable, region=region)
    assert result.status is OperationStatus.CONDITIONAL
    assert result.candidate is not None
    assert result.candidate.problem.region == region
    assert result.region == region
    assert result.verifications[0].condition == region
    assert result.verifications[0].judgment is not None


@pytest.mark.parametrize("region_text", ["x >= 0", "x < 0", "true"])
def test_a_request_not_covered_by_the_derivative_region_is_refused(region_text):
    runtime = bootstrap_elementary()
    workspace = Workspace(runtime)
    source = workspace.intake(parse("sqrt(x)", runtime.table, runtime.signature))
    region = runtime_proposition(runtime, parse(region_text, runtime.table, runtime.signature))
    before = runtime.store.stats()
    result = workspace.apply("differentiate", (source,), target=runtime.variable, region=region)
    assert result.status is OperationStatus.UNKNOWN
    assert "region" in result.detail
    assert result.blocker is not None
    assert result.blocker.reason is Reason.GUARDED
    assert "region_coverage" in result.blocker.missing
    assert runtime.store.stats() == before
    assert result.candidate is None


def test_target_region_does_not_reduce_parameter_coverage():
    runtime = bootstrap_parameterized()
    workspace = Workspace(runtime)
    source = workspace.intake(parse("a*x^2", runtime.table, runtime.signature))
    region = runtime_proposition(runtime, parse("x > 2", runtime.table, runtime.signature))
    result = workspace.apply("differentiate", (source,), target=runtime.variable, region=region)
    assert result.status is OperationStatus.CONDITIONAL
    assert result.candidate.problem.region == region
    assert result.generic is not None
    assert result.generic.coverage_claim is CoverageClaim.ALL_VALUES
    assert result.generic.valid_on.condition.term == T.TRUE


def _assert_request_refused(result, runtime, before):
    assert result.status in (
        OperationStatus.UNSUPPORTED,
        OperationStatus.UNKNOWN,
    )
    assert result.candidate is None
    assert result.blocker is not None
    assert result.task is None or result.task.state is TaskState.BLOCKED
    assert runtime.store.stats() == before


def test_differentiate_refuses_complete_set_coverage():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    before = runtime.store.stats()
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    _assert_request_refused(result, runtime, before)


def test_integrate_refuses_complete_set_coverage():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(
        parse("x^2", runtime.table, runtime.signature)
    )
    before = runtime.store.stats()
    result = workspace.apply(
        "integrate",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    _assert_request_refused(result, runtime, before)


def test_polynomial_gcd_refuses_complete_set_coverage():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    left = workspace.intake(parse("x^2 - 1", runtime.table, runtime.signature))
    right = workspace.intake(parse("x - 1", runtime.table, runtime.signature))
    before = runtime.store.stats()
    result = workspace.apply(
        "polynomial_gcd",
        (left, right),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    _assert_request_refused(result, runtime, before)


def test_resultant_refuses_complete_set_coverage():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    left = workspace.intake(parse("x^2 - 1", runtime.table, runtime.signature))
    right = workspace.intake(parse("x - 1", runtime.table, runtime.signature))
    before = runtime.store.stats()
    result = workspace.apply(
        "resultant",
        (left, right),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    _assert_request_refused(result, runtime, before)


def test_hermite_refuses_complete_set_coverage():
    runtime = bootstrap_elementary()
    workspace = Workspace(runtime)
    source = workspace.intake(parse("1/x", runtime.table, runtime.signature))
    before = runtime.store.stats()
    result = workspace.apply(
        "hermite_reduce",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    _assert_request_refused(result, runtime, before)


def test_differentiate_refuses_a_set_result_language():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    before = runtime.store.stats()
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
    )
    _assert_request_refused(result, runtime, before)


def test_differentiate_refuses_a_parameter_mode_outside_its_view():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    before = runtime.store.stats()
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        parameter_mode=ParameterMode.GENERIC_PARAMETERS,
    )
    _assert_request_refused(result, runtime, before)


def test_a_blocked_execution_keeps_the_requested_coverage():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    assert result.task is not None
    assert result.task.problem.coverage is Coverage.COMPLETE_SET


def test_a_blocked_execution_keeps_the_requested_result_language():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
    )
    assert result.task is not None
    assert result.task.problem.result_language is ResultLanguage.SET
