"""The task-state table from architecture §18.1 is a pure derivation."""

from dataclasses import replace

import pytest
from support import head_app, runtime_proposition, variable

from cas.foundation.ids import (
    CandidateId,
    ExecutionAttemptId,
    JudgmentId,
    SymbolId,
    TaskId,
)
from cas.language import sorts as S
from cas.language.decisions import Blocker, Reason
from cas.language.problems import (
    Coverage,
    ParameterMode,
    VariableRoles,
)
from cas.language.signatures import StructuralHead
from cas.syntax import term as T
from cas.workflow.records import (
    Candidate,
    CandidateApplicability,
    CandidateCoverage,
    CandidateState,
    ExecutionAttempt,
    ExecutionState,
    OperationStatus,
    ResultLanguageFit,
    TaskState,
    VerificationLink,
    derive_task_state,
)
from cas.workflow.workspace import Workspace


def _problem(runtime):
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    return workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
    ).problem


def _candidate(
    runtime,
    problem,
    *,
    state: CandidateState = CandidateState.UNCHECKED,
    coverage: CandidateCoverage = CandidateCoverage.COMPLETE,
    applicability: CandidateApplicability | None = None,
) -> Candidate:
    return Candidate(
        CandidateId(1),
        TaskId(1),
        problem,
        T.number(1),
        runtime.frame.id,
        state,
        coverage=coverage,
        applicability=(
            CandidateApplicability.APPLICABLE
            if applicability is None
            else applicability
        ),
    )


def _link(
    runtime,
    problem,
    candidate: Candidate,
    *,
    status: OperationStatus = OperationStatus.VERIFIED,
    coverage: Coverage | None = None,
    condition=None,
    obligations=(),
) -> VerificationLink:
    return VerificationLink(
        candidate=candidate.id,
        specification=runtime_proposition(runtime, T.TRUE),
        judgment=JudgmentId(1),
        status=status,
        specification_kind="HasDerivative",
        frame=runtime.frame.id,
        coverage=problem.coverage if coverage is None else coverage,
        condition=condition,
        obligations=obligations,
    )


def _comparison(runtime, head, bound):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            head,
            variable(runtime),
            T.number(bound),
        ),
    )


def test_a_fixed_problem_without_attempts_is_ready(runtime):
    problem = _problem(runtime)
    assert (
        derive_task_state(problem, (), (), None, ()) is TaskState.READY
    )


def test_a_blocker_without_a_verified_link_blocks_the_task(runtime):
    problem = _problem(runtime)
    blocker = Blocker(Reason.FRAGMENT, "the fragment is missing")
    assert (
        derive_task_state(problem, (), (), blocker, ())
        is TaskState.BLOCKED
    )


def test_an_unchecked_candidate_without_a_link_is_partially_solved(runtime):
    problem = _problem(runtime)
    candidate = _candidate(runtime, problem)
    assert (
        derive_task_state(problem, (candidate,), (), None, ())
        is TaskState.PARTIALLY_SOLVED
    )


def test_one_verified_link_completes_a_one_verified_request(runtime):
    problem = _problem(runtime)
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate)
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED
    )


def test_an_out_of_scope_candidate_does_not_complete_the_task(runtime):
    problem = _problem(runtime)
    candidate = _candidate(
        runtime,
        problem,
        applicability=CandidateApplicability.OUT_OF_SCOPE,
    )
    link = _link(
        runtime,
        problem,
        candidate,
        status=OperationStatus.VERIFIED,
    )
    assert link.status is OperationStatus.VERIFIED
    assert candidate.language_fit is ResultLanguageFit.SATISFIES
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.PARTIALLY_SOLVED
    )


def test_a_blocked_applicability_keeps_an_earlier_verified_link(runtime):
    problem = _problem(runtime)
    candidate = _candidate(
        runtime,
        problem,
        state=CandidateState.UNVERIFIED,
        applicability=CandidateApplicability.BLOCKED,
    )
    link = _link(
        runtime,
        problem,
        candidate,
        status=OperationStatus.VERIFIED,
    )
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED
    )


def test_a_sound_set_link_completes_a_sound_set_request(runtime):
    problem = replace(_problem(runtime), coverage=Coverage.SOUND_SET)
    candidate = _candidate(runtime, problem)
    link = _link(
        runtime,
        problem,
        candidate,
        coverage=Coverage.SOUND_SET,
    )
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED
    )


def test_a_sound_set_link_does_not_complete_a_complete_set_request(runtime):
    problem = replace(_problem(runtime), coverage=Coverage.COMPLETE_SET)
    candidate = _candidate(runtime, problem)
    link = _link(
        runtime,
        problem,
        candidate,
        coverage=Coverage.SOUND_SET,
    )
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.PARTIALLY_SOLVED
    )


def test_a_complete_set_link_completes_a_complete_set_request(runtime):
    problem = replace(_problem(runtime), coverage=Coverage.COMPLETE_SET)
    candidate = _candidate(runtime, problem)
    link = _link(
        runtime,
        problem,
        candidate,
        coverage=Coverage.COMPLETE_SET,
    )
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED
    )


def test_a_result_region_proved_by_the_problem_region_completes(runtime):
    condition = _comparison(runtime, StructuralHead.GT, 0)
    region = _comparison(runtime, StructuralHead.GT, 1)
    problem = replace(_problem(runtime), region=region)
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate, condition=condition)
    assert (
        derive_task_state(
            problem,
            (candidate,),
            (link,),
            None,
            (),
            signature=runtime.signature,
        )
        is TaskState.COMPLETED
    )


def test_a_true_result_condition_is_closed(runtime):
    condition = runtime_proposition(runtime, T.TRUE)
    problem = _problem(runtime)
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate, condition=condition)
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED
    )


def test_an_externalized_result_region_does_not_complete_the_task(runtime):
    condition = _comparison(runtime, StructuralHead.GT, 0)
    problem = replace(
        _problem(runtime),
        externalizable=(condition,),
    )
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate, condition=condition)
    assert (
        derive_task_state(
            problem,
            (candidate,),
            (link,),
            None,
            (),
            signature=runtime.signature,
        )
        is TaskState.PARTIALLY_SOLVED
    )


def test_without_a_signature_only_exact_result_region_equality_closes(runtime):
    condition = _comparison(runtime, StructuralHead.GT, 0)
    region = _comparison(runtime, StructuralHead.GT, 1)
    problem = replace(_problem(runtime), region=region)
    candidate = _candidate(runtime, problem)
    exact = _link(runtime, problem, candidate, condition=region)
    weaker = _link(runtime, problem, candidate, condition=condition)
    assert (
        derive_task_state(problem, (candidate,), (exact,), None, ())
        is TaskState.COMPLETED
    )
    assert (
        derive_task_state(problem, (candidate,), (weaker,), None, ())
        is TaskState.PARTIALLY_SOLVED
    )


def test_a_disallowed_open_condition_leaves_the_task_partial(runtime):
    condition = _comparison(runtime, StructuralHead.GT, 0)
    problem = _problem(runtime)
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate, condition=condition)
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.PARTIALLY_SOLVED
    )


def test_an_allowed_kernel_obligation_completes_conditionally(runtime):
    condition = runtime_proposition(runtime, T.TRUE)
    problem = replace(
        _problem(runtime),
        externalizable=(condition,),
    )
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate, obligations=(condition,))
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED_CONDITIONAL
    )


def test_a_disallowed_kernel_obligation_leaves_the_task_partial(runtime):
    condition = runtime_proposition(runtime, T.TRUE)
    problem = _problem(runtime)
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate, obligations=(condition,))
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.PARTIALLY_SOLVED
    )


def test_cancellation_wins_over_existing_results(runtime):
    problem = _problem(runtime)
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate)
    assert (
        derive_task_state(
            problem,
            (candidate,),
            (link,),
            None,
            (),
            cancelled=True,
        )
        is TaskState.CANCELLED
    )


def _parameter_problem(runtime, mode: ParameterMode):
    problem = _problem(runtime)
    return replace(
        problem,
        roles=VariableRoles(
            problem.target,
            (SymbolId(999),),
            mode,
            runtime.world.id,
            problem.roles.target_sort,
            (S.REAL,),
        ),
    )


def test_a_generic_answer_does_not_complete_an_all_parameter_request(runtime):
    problem = _parameter_problem(runtime, ParameterMode.ALL_PARAMETER_VALUES)
    candidate = _candidate(
        runtime, problem, coverage=CandidateCoverage.GENERIC
    )
    link = _link(runtime, problem, candidate)
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.PARTIALLY_SOLVED
    )


def test_a_generic_answer_completes_a_generic_parameter_request(runtime):
    problem = _parameter_problem(runtime, ParameterMode.GENERIC_PARAMETERS)
    candidate = _candidate(
        runtime, problem, coverage=CandidateCoverage.GENERIC
    )
    link = _link(runtime, problem, candidate)
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED
    )


def test_a_sound_set_candidate_completes_a_sound_set_request(runtime):
    problem = replace(_problem(runtime), coverage=Coverage.SOUND_SET)
    candidate = _candidate(
        runtime, problem, coverage=CandidateCoverage.PARTIAL
    )
    link = _link(runtime, problem, candidate, coverage=Coverage.SOUND_SET)
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.COMPLETED
    )


def test_an_attempt_without_a_candidate_or_blocker_is_inconsistent(runtime):
    problem = _problem(runtime)
    attempt = ExecutionAttempt(
        ExecutionAttemptId(1),
        TaskId(1),
        ExecutionState.BLOCKED,
    )
    with pytest.raises(ValueError, match="candidate or a blocker"):
        derive_task_state(problem, (), (), None, (attempt,))


def test_a_cancelled_attempt_derives_cancellation(runtime):
    problem = _problem(runtime)
    candidate = _candidate(runtime, problem)
    link = _link(runtime, problem, candidate)
    attempt = ExecutionAttempt(
        ExecutionAttemptId(1),
        TaskId(1),
        ExecutionState.CANCELLED,
    )
    assert (
        derive_task_state(problem, (candidate,), (link,), None, (attempt,))
        is TaskState.CANCELLED
    )


def test_a_sound_set_candidate_does_not_complete_a_complete_set_request(
    runtime,
):
    problem = replace(_problem(runtime), coverage=Coverage.COMPLETE_SET)
    candidate = _candidate(
        runtime, problem, coverage=CandidateCoverage.PARTIAL
    )
    link = _link(runtime, problem, candidate, coverage=Coverage.COMPLETE_SET)
    assert (
        derive_task_state(problem, (candidate,), (link,), None, ())
        is TaskState.PARTIALLY_SOLVED
    )
