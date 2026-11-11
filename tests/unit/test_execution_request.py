"""Execution requests: one fixed problem, algebra view and strategy."""

from dataclasses import dataclass, field, replace
from typing import cast

import pytest
from support import head_app, multivariate_setup, typed_in, variable

from cas.foundation.ids import CandidateId, FrameId, SymbolId, TaskId
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.execution import (
    BudgetTicket,
    ConditionPolicy,
    ExecutionBudget,
)
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    InterpretationRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
    VariableRoles,
)
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.calculus.differentiation.specification import parse_has_derivative
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
    ProposalOutcome,
    ProposalUnsupported,
    Proposed,
    ResultSchema,
    ResultShape,
)
from cas.operations.registry import OperationRegistry
from cas.runtime import bootstrap
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T
from cas.workflow.records import Candidate, OperationStatus
from cas.workflow.workspace import Workspace


@dataclass(frozen=True, slots=True)
class RecordingOperation:
    """A test double that records the execution request it receives."""

    frames: FrameStore
    signature: LanguageSignature
    seen: list[ExecutionRequest] = field(
        default_factory=list, compare=False, repr=False
    )
    algebra: AlgebraRequest | None = None
    id: str = "test.recording"
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

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("test/recording", lambda request: Admitted())

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

    def build_problem(self, request: OperationRequest) -> ProblemBuilt:
        roles = VariableRoles(
            request.target,
            (),
            ParameterMode.SPECIFIED_VALUES,
            self.frames.world.id,
            (
                S.REAL
                if request.target is not None
                else None
            ),
        )
        domain_requirement = (
            None
            if self.algebra is None
            else DomainRequirement(
                coefficient=self.algebra.coefficient_domain,
                values=self.algebra.value_domain,
            )
        )
        return ProblemBuilt(
            ProblemSpec(
                operation=self.problem_kind,
                inputs=(
                    typed_in(
                        self.frames,
                        request.frame,
                        self.signature,
                        request.inputs[0],
                    ),
                ),
                roles=roles,
                region=request.region,
                result_language=self.result_schema.single_language(),
                coverage=Coverage.ONE_VERIFIED,
                interpretation_requirement=(
                    self.algebra.interpretation_requirement
                    if self.algebra is not None
                    else None
                ),
                domain_requirement=domain_requirement,
            ),
            algebra=self.algebra,
        )

    def propose(self, execution: ExecutionRequest) -> ProposalOutcome:
        self.seen.append(execution)
        assumptions = self.frames.assumptions(execution.request.frame)
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


def test_execution_request_fixes_problem_algebra_frame_and_strategy():
    runtime = bootstrap()
    operation = runtime.operations.get("differentiate")
    assert operation is not None
    request = OperationRequest(
        runtime.frame.id,
        (variable(runtime),),
        runtime.request.target,
    )
    outcome = operation.build_problem(request)
    assert isinstance(outcome, ProblemBuilt)
    assert outcome.algebra is not None
    budget = ExecutionBudget(max_nodes=10, max_depth=3)
    execution = ExecutionRequest(
        request,
        outcome.problem,
        outcome.algebra,
        request.frame,
        ConditionPolicy.ALLOW_CONDITIONAL,
        budget,
    )
    assert execution.request is request
    assert execution.problem is outcome.problem
    assert execution.algebra is outcome.algebra
    assert execution.frame == request.frame
    assert execution.policy is ConditionPolicy.ALLOW_CONDITIONAL
    assert execution.budget is budget

    with pytest.raises(ValueError, match="interpretation"):
        ExecutionRequest(
            request,
            outcome.problem,
            None,
            request.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )

    other_roles = VariableRoles(
        SymbolId(999_999),
        (),
        ParameterMode.SPECIFIED_VALUES,
        runtime.world.id,
        S.REAL,
    )
    other_problem = replace(outcome.problem, roles=other_roles)
    with pytest.raises(ValueError):
        ExecutionRequest(
            request,
            other_problem,
            outcome.algebra,
            request.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )
    with pytest.raises(ValueError):
        ExecutionRequest(
            request,
            outcome.problem,
            outcome.algebra,
            FrameId(request.frame + 1),
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )
    with pytest.raises(ValueError):
        ProblemBuilt(other_problem, algebra=outcome.algebra)


def test_execution_budget_accepts_only_positive_integer_limits():
    assert ExecutionBudget() == ExecutionBudget(None, None)
    with pytest.raises(TypeError):
        ExecutionBudget(max_nodes="3")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        ExecutionBudget(max_depth=True)
    with pytest.raises(ValueError):
        ExecutionBudget(max_nodes=0)
    with pytest.raises(ValueError):
        ExecutionBudget(max_depth=-1)


def test_a_budget_ticket_spends_only_within_its_limits():
    budget = ExecutionBudget(max_nodes=5, max_depth=3)
    ticket = BudgetTicket(budget)
    assert ticket.budget is budget
    assert ticket.consumed_nodes == 0
    assert ticket.consumed_depth == 0

    first = ticket.spend(3, 1)
    assert isinstance(first, BudgetTicket)
    assert first.budget is budget
    assert first.consumed_nodes == 3
    assert first.consumed_depth == 1

    second = first.spend(2, 2)
    assert isinstance(second, BudgetTicket)
    assert second.consumed_nodes == 5
    assert second.consumed_depth == 3

    assert second.spend(1, 0) is None
    assert second.spend(0, 1) is None
    assert first.spend(3, 0) is None
    assert first.spend(0, 3) is None


def test_a_budget_ticket_without_limits_accepts_any_charge():
    ticket = BudgetTicket(ExecutionBudget())
    spent = ticket.spend(1_000_000, 1_000_000)
    assert isinstance(spent, BudgetTicket)
    assert spent.consumed_nodes == 1_000_000
    assert spent.consumed_depth == 1_000_000


def test_a_budget_ticket_validates_its_budget_and_charges():
    with pytest.raises(TypeError):
        BudgetTicket(cast(ExecutionBudget, object()))
    with pytest.raises(TypeError):
        BudgetTicket(
            ExecutionBudget(), consumed_nodes=cast(int, "1")
        )
    with pytest.raises(ValueError):
        BudgetTicket(ExecutionBudget(), consumed_nodes=-1)
    with pytest.raises(ValueError):
        BudgetTicket(ExecutionBudget(), consumed_depth=-1)
    ticket = BudgetTicket(ExecutionBudget(max_nodes=1))
    with pytest.raises(TypeError):
        ticket.spend(True, 0)
    with pytest.raises(ValueError):
        ticket.spend(-1, 0)
    with pytest.raises(ValueError):
        ticket.spend(0, -1)


def test_workspace_differentiate_commits_the_fixed_problem():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime), "x")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.task is not None
    assert result.candidate is not None
    problem = result.task.problem
    assert problem.operation == "differentiate"
    assert problem.roles == runtime.request.roles
    assert problem.target == runtime.variable
    assert problem.inputs[0].term == source.term
    assert result.candidate.problem is problem
    assert result.verifications[0].specification == (
        result.candidate.specifications[0]
    )
    claim = parse_has_derivative(
        runtime.vocabulary, result.candidate.specifications[0].term
    )
    assert claim is not None
    assert claim.source == problem.inputs[0].term
    assert claim.variable.symbol_id == problem.target


def test_workspace_passes_the_fixed_execution_request_to_the_operation():
    runtime = bootstrap()
    operation = RecordingOperation(runtime.frames, runtime.signature)
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
    result = workspace.apply(operation.id, (source,))
    assert result.status is OperationStatus.VERIFIED
    assert len(operation.seen) == 1
    execution = operation.seen[0]
    assert isinstance(execution, ExecutionRequest)
    assert execution.request.inputs == (source.term,)
    assert result.task is not None
    assert execution.problem is result.task.problem
    assert execution.problem.operation == "assume"
    assert execution.frame == workspace.frame
    assert execution.policy is ConditionPolicy.REQUIRE_PROVED
    assert execution.budget == ExecutionBudget()
    assert execution.algebra is None


def test_workspace_passes_the_built_algebra_view_to_the_operation():
    runtime = bootstrap()
    operation = RecordingOperation(
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
    assert len(operation.seen) == 1
    assert operation.seen[0].algebra is runtime.request


def test_problem_built_binds_the_interpretation_requirement():
    runtime = bootstrap()
    operation = runtime.operations.get("differentiate")
    assert operation is not None
    request = OperationRequest(
        runtime.frame.id,
        (variable(runtime),),
        runtime.variable,
    )
    built = operation.build_problem(request)
    assert isinstance(built, ProblemBuilt)
    with pytest.raises(ValueError, match="without an algebra"):
        ProblemBuilt(built.problem, algebra=None)
    without_requirement = replace(
        built.problem, interpretation_requirement=None
    )
    with pytest.raises(ValueError, match="interpretation"):
        ProblemBuilt(without_requirement, algebra=runtime.request)


def test_an_algebra_execution_requires_its_algebra_view():
    runtime = bootstrap()
    operation = runtime.operations.get("differentiate")
    assert operation is not None
    request = OperationRequest(
        runtime.frame.id,
        (variable(runtime),),
        runtime.variable,
    )
    built = operation.build_problem(request)
    assert isinstance(built, ProblemBuilt)
    with pytest.raises(ValueError, match="interpretation"):
        ExecutionRequest(
            request,
            built.problem,
            None,
            request.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )


def test_problem_built_binds_the_domain_requirement():
    runtime = bootstrap()
    operation = runtime.operations.get("differentiate")
    assert operation is not None
    request = OperationRequest(
        runtime.frame.id,
        (variable(runtime),),
        runtime.variable,
    )
    built = operation.build_problem(request)
    assert isinstance(built, ProblemBuilt)
    assert built.problem.domain_requirement == DomainRequirement(
        ValueDomain.RATIONAL, ValueDomain.REAL
    )
    with pytest.raises(ValueError, match="coefficient domain"):
        ProblemBuilt(
            built.problem,
            algebra=replace(
                runtime.request,
                coefficient_domain=ValueDomain.INTEGER,
            ),
        )
    with pytest.raises(ValueError, match="value domain"):
        forged = replace(built.problem)
        object.__setattr__(
            forged,
            "domain_requirement",
            DomainRequirement(ValueDomain.RATIONAL, ValueDomain.INTEGER),
        )
        ProblemBuilt(forged, algebra=runtime.request)
    missing = replace(built.problem)
    object.__setattr__(missing, "domain_requirement", None)
    with pytest.raises(ValueError, match="domain requirement"):
        ProblemBuilt(missing, algebra=runtime.request)
    with pytest.raises(ValueError, match="domain requirement"):
        ExecutionRequest(
            request,
            missing,
            runtime.request,
            request.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )


def _generator_problem(runtime):
    setup = multivariate_setup(runtime)
    symbol = setup.symbols[0]
    name = runtime.table.name_of(symbol)
    source = typed_in(
        runtime.frames,
        setup.frame,
        runtime.signature,
        T.symbol(symbol, name),
    )
    problem = ProblemSpec(
        operation="groebner_basis",
        inputs=(source,),
        roles=setup.request.roles,
        region=None,
        result_language=ResultLanguage.PROPOSITION,
        coverage=Coverage.ONE_VERIFIED,
        interpretation_requirement=InterpretationRequirement.FORMAL,
        domain_requirement=DomainRequirement(
            ValueDomain.RATIONAL, ValueDomain.REAL
        ),
    )
    request = OperationRequest(
        setup.frame, (T.symbol(symbol, name),)
    )
    return setup, problem, request


def test_problem_built_and_execution_accept_generator_mode(runtime):
    setup, problem, request = _generator_problem(runtime)
    assert problem.target is None
    assert problem.variables == setup.symbols
    built = ProblemBuilt(problem, algebra=setup.request)
    assert built.algebra is setup.request
    execution = ExecutionRequest(
        request,
        problem,
        setup.request,
        request.frame,
        ConditionPolicy.REQUIRE_PROVED,
        ExecutionBudget(),
    )
    assert execution.algebra is setup.request
    assert execution.problem.roles == setup.request.roles


def test_generator_role_equality_is_the_single_role_authority(runtime):
    setup, problem, request = _generator_problem(runtime)
    other_roles = replace(
        setup.request.roles,
        variables=tuple(reversed(setup.symbols)),
        variable_sorts=(S.REAL, S.REAL),
    )
    other_algebra = replace(setup.request, roles=other_roles)
    assert problem.roles.target is None
    assert other_algebra.roles.target is None
    with pytest.raises(ValueError, match="role"):
        ProblemBuilt(problem, algebra=other_algebra)
    with pytest.raises(ValueError, match="role"):
        ExecutionRequest(
            request,
            problem,
            other_algebra,
            request.frame,
            ConditionPolicy.REQUIRE_PROVED,
            ExecutionBudget(),
        )


def test_a_generator_candidate_keeps_its_algebra_snapshot(runtime):
    setup, problem, _ = _generator_problem(runtime)
    symbol = setup.symbols[0]
    term = T.symbol(symbol, runtime.table.name_of(symbol))
    candidate = Candidate(
        CandidateId(1),
        TaskId(1),
        problem,
        term,
        setup.frame,
        algebra=setup.request,
    )
    assert candidate.algebra is setup.request
    other_roles = replace(
        setup.request.roles,
        variables=tuple(reversed(setup.symbols)),
        variable_sorts=(S.REAL, S.REAL),
    )
    with pytest.raises(ValueError, match="roles"):
        Candidate(
            CandidateId(2),
            TaskId(1),
            problem,
            term,
            setup.frame,
            algebra=replace(setup.request, roles=other_roles),
        )

