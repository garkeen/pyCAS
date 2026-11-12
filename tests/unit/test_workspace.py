"""Workspace: expression objects, candidates, verification links and history."""

from dataclasses import replace
from fractions import Fraction

import pytest
from support import (
    head_app,
    runtime_proposition,
    variable,
    view_of,
)

from cas.foundation.ids import CandidateId, JudgmentId, ObjectVersionId
from cas.frontend import parse
from cas.kernel.commit import Deferred, Rejected
from cas.language import sorts as S
from cas.language.decisions import Blocker, Reason
from cas.language.execution import ExecutionBudget
from cas.language.functions import FunctionParameter
from cas.language.problems import Coverage, ResultLanguage
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime.bootstrap import bootstrap_elementary, new_workspace
from cas.semantics.frames import Definition
from cas.syntax import term as T
from cas.workflow.records import (
    ActorKind,
    Artifact,
    CandidateApplicability,
    CandidateCoverage,
    CandidateFocus,
    CandidateState,
    ConstructionRelation,
    FunctionDefined,
    FunctionRefused,
    ObjectFocus,
    OccurrenceFocus,
    OperationStatus,
    ResultLanguageFit,
    RewriteRelation,
    TaskFocus,
    TaskState,
    VerificationLink,
)


def source_term(runtime) -> T.Apply:
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature, StructuralHead.POWER, x, T.number(3)
        ),
        head_app(
            runtime.signature, StructuralHead.TIMES, T.number(-3), x
        ),
    )


def unsupported_term(runtime) -> T.Apply:
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(-1),
    )


def linear_term(runtime) -> T.Apply:
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            T.number(2),
            x,
        ),
        T.number(4),
    )


def nonnegative_region(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GE,
            variable(runtime),
            T.number(0),
        ),
    )


def square_term(runtime) -> T.Apply:
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(2),
    )


def product_term(runtime) -> T.Apply:
    return head_app(
        runtime.signature,
        StructuralHead.TIMES,
        variable(runtime),
        variable(runtime),
    )


def shifted_term(runtime) -> T.Apply:
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        variable(runtime),
        T.number(1),
    )


def define_real_function(workspace, runtime, term, domain, label):
    outcome = workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        term,
        domain,
        label,
    )
    assert isinstance(outcome, FunctionDefined)
    return outcome.function


def expected_derivative(runtime):
    ring = runtime.ring
    return ring.sub(
        ring.mul_int(ring.monomial((2,), Fraction(1)), 3),
        ring.constant(Fraction(3)),
    )


def test_the_workspace_starts_with_an_empty_revision(runtime):
    workspace = new_workspace(runtime)
    assert workspace.expressions() == ()
    assert workspace.links() == ()
    assert workspace.events() == ()
    assert not workspace.undo()
    assert not workspace.redo()


def test_intake_records_an_expression_without_a_judgment(runtime):
    workspace = new_workspace(runtime)
    term = source_term(runtime)
    expression = workspace.intake(term, "source")
    assert expression.term is term
    assert expression.frame == runtime.frame.id
    assert expression.label == "source"
    assert expression.source_operation == "Intake"
    assert workspace.expressions() == (expression,)
    assert workspace.links() == ()
    assert [event.operation for event in workspace.events()] == ["Intake"]
    assert workspace.revision.label == "intake source"
    assert runtime.store.stats()["judgments"] == 0


def test_expression_exposes_artifact_and_object_version_views(runtime):
    workspace = new_workspace(runtime)
    expression = replace(
        workspace.intake(source_term(runtime), "source"),
        presentation=(("style", "bold"),),
    )
    artifact = expression.artifact
    assert artifact.term is expression.term
    assert artifact.function is None
    view = expression.object_version
    assert view.object_id == expression.id
    assert view.version_id == expression.version
    assert view.artifact.term is expression.term
    assert view.artifact.function is None
    assert view.created_in_frame == expression.frame
    assert view.source_operation == expression.source_operation
    assert view.presentation == (("style", "bold"),)


def test_function_object_exposes_artifact_and_object_version_views(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative_region(runtime)
    function = define_real_function(
        workspace, runtime, square_term(runtime), domain, "f"
    )
    artifact = function.artifact
    assert artifact.function is function.value
    assert artifact.term is None
    view = function.object_version
    assert view.object_id == function.id
    assert view.version_id == function.version
    assert view.artifact.function is function.value
    assert view.artifact.term is None
    assert view.created_in_frame == function.frame
    assert view.source_operation == "DefineFunction"
    assert view.presentation == function.presentation


def test_artifact_requires_exactly_one_payload(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative_region(runtime)
    function = define_real_function(
        workspace, runtime, square_term(runtime), domain, "f"
    )
    with pytest.raises(ValueError):
        Artifact()
    with pytest.raises(ValueError):
        Artifact(term=variable(runtime), function=function.value)


def test_object_version_validates_identity_and_presentation(runtime):
    workspace = new_workspace(runtime)
    expression = workspace.intake(variable(runtime), "source")
    view = expression.object_version
    with pytest.raises(TypeError):
        replace(view, object_id=True)
    with pytest.raises(TypeError):
        replace(view, version_id=True)
    with pytest.raises(TypeError):
        replace(view, created_in_frame=True)
    with pytest.raises(TypeError):
        replace(view, source_operation=7)
    with pytest.raises(TypeError):
        replace(view, presentation=[("style", "bold")])
    with pytest.raises(ValueError):
        replace(
            view,
            presentation=(("style", "bold"), ("style", "italic")),
        )


def test_object_version_returns_visible_expression_and_function_views(runtime):
    workspace = new_workspace(runtime)
    expression = workspace.intake(variable(runtime), "source")
    function = define_real_function(
        workspace,
        runtime,
        square_term(runtime),
        nonnegative_region(runtime),
        "f",
    )
    assert (
        workspace.object_version(expression.version)
        == expression.object_version
    )
    assert (
        workspace.object_version(function.version)
        == function.object_version
    )


def test_object_version_hides_versions_outside_the_current_revision(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.result is not None
    hidden = result.result.version
    assert workspace.object_version(hidden) == result.result.object_version
    assert workspace.undo()
    assert workspace.object_version(hidden) is None
    assert workspace.object_version(source.version) == source.object_version
    function = define_real_function(
        workspace,
        runtime,
        square_term(runtime),
        nonnegative_region(runtime),
        "f",
    )
    assert workspace.object_version(function.version) is not None
    assert workspace.undo()
    assert workspace.object_version(function.version) is None
    assert workspace.object_version(ObjectVersionId(10_000)) is None


def test_differentiation_produces_a_verified_candidate_and_result(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.detail == ""
    assert result.candidate is not None
    assert result.verifications
    assert result.result is not None
    assert result.result.source_operation == "differentiate"
    link = result.verifications[0]
    assert link.status is OperationStatus.VERIFIED
    assert link.judgment is not None
    assert link.candidate == result.candidate.id
    assert workspace.candidate(link.candidate) is result.candidate
    assert workspace.applicability(link.judgment).is_applicable()
    assert runtime.store.stats()["judgments"] == 1

    candidate = result.candidate
    assert candidate.problem.operation == "differentiate"
    assert tuple(item.term for item in candidate.problem.inputs) == (
        source.term,
    )
    assert candidate.problem.target == runtime.variable
    assert candidate.problem.coverage.value == "one_verified"
    assert candidate.problem.result_language.value == "expression"
    assert candidate.frame == runtime.frame.id

    claim = parse_has_derivative(
        runtime.vocabulary, link.specification.term
    )
    assert claim is not None
    assert claim.region == T.TRUE
    assert claim.source == source.term
    assert claim.variable.symbol_id == runtime.variable
    assert claim.candidate == result.result.term
    assert link.specification.meaning == runtime.frame.meaning

    value = view_of(runtime, result.result.term).value
    assert runtime.ring.equal(value, expected_derivative(runtime))
    assert [event.operation for event in workspace.events()] == [
        "Intake",
        "differentiate",
    ]
    assert len(workspace.links()) == 1


def test_a_verification_link_judgment_is_recorded_by_its_event(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.verifications
    event = workspace.events()[-1]
    recorded = set(event.judgments)
    for link in workspace.links():
        if link.judgment is not None:
            assert link.judgment in recorded


def test_outside_the_fragment_the_workspace_refuses_without_writing(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(unsupported_term(runtime), "reciprocal")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.candidate is None
    assert not result.verifications
    assert result.result is None
    assert result.task is not None
    assert result.task.state is TaskState.BLOCKED
    assert "polynomial fragment" in result.detail
    assert runtime.store.stats()["judgments"] == 0
    assert [event.operation for event in workspace.events()] == [
        "Intake",
        "differentiate",
    ]


def test_another_variable_is_refused_without_writing(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    y = runtime.table.intern("y")
    result = workspace.differentiate(source, y)
    assert result.status is OperationStatus.UNSUPPORTED
    assert "target variable" in result.detail
    assert result.candidate is None
    assert runtime.store.stats()["judgments"] == 0


def test_an_alias_input_matches_the_expanded_problem(runtime):
    alias = runtime.table.intern("u")
    frame = runtime.frames.create(
        runtime.frame.id,
        definitions=(Definition(alias, "u", variable(runtime)),),
    )
    workspace = new_workspace(replace(runtime, frame=frame))
    source = workspace.intake(T.symbol(alias, "u"), "alias")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.candidate is not None
    assert tuple(item.term for item in result.candidate.problem.inputs) == (
        variable(runtime),
    )


def test_a_checker_refusal_keeps_its_missing_capabilities(runtime):
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    library = runtime.elementary
    assert library is not None
    pi = library.constants["pi"]
    e = library.constants["e"]
    domain = runtime_proposition(runtime, T.TRUE)
    parameters = (FunctionParameter(runtime.variable, S.REAL),)
    left = workspace.define_function(
        parameters,
        domain,
        S.REAL,
        T.symbol(pi.symbol, pi.name),
        domain,
        "pi",
    )
    right = workspace.define_function(
        parameters,
        domain,
        S.REAL,
        T.symbol(e.symbol, e.name),
        domain,
        "e",
    )
    assert isinstance(left, FunctionDefined)
    assert isinstance(right, FunctionDefined)
    result = workspace.compare_functions(
        left.function, right.function, region=domain
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.reason is Reason.FRAGMENT
    assert "symbol_mapping" in result.blocker.missing


def test_revision_ids_are_not_reused_after_undo(runtime):
    workspace = new_workspace(runtime)
    workspace.intake(variable(runtime))
    deleted = workspace.revision.id
    assert workspace.undo()
    workspace.intake(variable(runtime))
    assert workspace.revision.id != deleted
    assert int(workspace.revision.id) > int(deleted)


def test_a_revision_records_its_immediate_parent(runtime):
    workspace = new_workspace(runtime)
    start = workspace.revision
    workspace.intake(variable(runtime))
    first = workspace.revision
    assert first.parents == (start.id,)
    workspace.intake(variable(runtime))
    assert workspace.revision.parents == (first.id,)


def test_undo_and_redo_move_the_view_but_not_the_ledger(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert len(workspace.expressions()) == 2
    judgment = result.verifications[0].judgment

    assert workspace.undo()
    assert workspace.expressions() == (source,)
    assert workspace.links() == ()
    assert runtime.store.get_judgment(judgment).proposition is not None

    assert workspace.undo()
    assert workspace.expressions() == ()
    assert not workspace.undo()

    assert workspace.redo()
    assert workspace.redo()
    assert len(workspace.expressions()) == 2
    assert len(workspace.links()) == 1
    assert not workspace.redo()
    assert runtime.store.stats()["judgments"] == 1


def test_undo_and_redo_restore_task_and_candidate_snapshots(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    first = workspace.differentiate(source, runtime.variable)
    assert first.task is not None
    assert first.candidate is not None
    task_id = first.task.id
    candidate_id = first.candidate.id
    before = workspace.revision

    edited = workspace.edit_candidate(candidate_id, T.number(7))
    assert edited.candidate is not None
    edited_id = edited.candidate.id
    after = workspace.revision
    assert workspace.task(task_id).candidates == (
        candidate_id,
        edited_id,
    )
    assert workspace.candidate(edited_id) == edited.candidate

    assert workspace.undo()
    assert workspace.revision.id == before.id
    assert workspace.tasks() == (first.task,)
    assert workspace.task(task_id) == first.task
    assert workspace.candidates() == (first.candidate,)
    with pytest.raises(KeyError):
        workspace.candidate(edited_id)

    assert workspace.redo()
    assert workspace.revision.id == after.id
    assert workspace.task(task_id).candidates == (
        candidate_id,
        edited_id,
    )
    assert workspace.candidate(edited_id) == edited.candidate


def test_a_task_from_a_later_revision_is_not_visible_after_undo(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    first = workspace.differentiate(source, runtime.variable)
    assert first.task is not None
    first_revision = workspace.revision
    second = workspace.differentiate(source, runtime.variable)
    assert second.task is not None
    assert workspace.undo()
    assert workspace.revision.id == first_revision.id
    with pytest.raises(KeyError):
        workspace.task(second.task.id)
    assert workspace.tasks() == (first.task,)


def test_a_cancelled_task_is_not_revived_by_check_or_edit():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = workspace.intake(
        parse("sqrt(x)", runtime.table, runtime.signature), "source"
    )
    conditional = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
    )
    assert conditional.status is OperationStatus.CONDITIONAL
    assert conditional.task is not None
    assert conditional.candidate is not None
    assert conditional.task.state is TaskState.PARTIALLY_SOLVED
    task_id = conditional.task.id
    candidate_id = conditional.candidate.id

    cancelled = workspace.cancel_task(task_id)
    assert cancelled.task is not None
    assert cancelled.task.state is TaskState.CANCELLED

    checked = workspace.check_candidate(candidate_id)
    assert checked.task is not None
    assert checked.task.state is TaskState.CANCELLED
    assert workspace.task(task_id).state is TaskState.CANCELLED

    edited = workspace.edit_candidate(candidate_id, T.number(7))
    assert edited.candidate is not None
    assert workspace.task(task_id).state is TaskState.CANCELLED


def test_a_stale_occurrence_is_refused(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            variable(runtime),
            T.number(1),
        ),
        "source",
    )
    other = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            T.number(2),
            T.number(1),
        ),
        "other",
    )
    replacement = workspace.intake(T.number(9), "replacement")
    found = workspace.occurrences(source, variable(runtime))
    assert len(found) == 1
    assert found[0].expected == variable(runtime)
    result = workspace.rewrite(
        other, found[0], replacement, RewriteRelation.EQUIVALENT
    )
    assert result.status is OperationStatus.INVALID
    assert "expected subterm" in result.detail


def test_occurrences_do_not_traverse_quoted_data(runtime):
    workspace = new_workspace(runtime)
    quoted = workspace.intake(
        T.quote(source_term(runtime)), "quoted"
    )
    assert workspace.occurrences(quoted, variable(runtime)) == ()


def test_a_new_operation_after_undo_truncates_the_redo_branch(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    workspace.differentiate(source, runtime.variable)
    assert workspace.undo()
    replacement = workspace.intake(T.number(7), "replacement")
    assert not workspace.redo()
    assert workspace.expressions() == (source, replacement)
    assert workspace.links() == ()
    assert [event.operation for event in workspace.events()] == [
        "Intake",
        "Intake",
    ]
    assert runtime.store.stats()["judgments"] == 1


def test_each_differentiation_gets_its_own_candidate_and_judgment(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    first = workspace.differentiate(source, runtime.variable)
    second = workspace.differentiate(source, runtime.variable)
    assert first.candidate.id != second.candidate.id
    assert first.verifications[0].judgment != second.verifications[0].judgment
    assert runtime.store.stats()["judgments"] == 2
    assert len(workspace.links()) == 2
    assert len(workspace.expressions()) == 3


def test_an_object_from_another_workspace_is_not_an_input_handle(runtime):
    first = new_workspace(runtime)
    second = new_workspace(runtime)
    foreign = first.intake(T.number(2))
    local = second.intake(T.number(3))
    assert local.version == foreign.version
    before = runtime.store.stats()
    result = second.differentiate(foreign, runtime.variable)
    assert result.status is OperationStatus.INVALID
    assert runtime.store.stats() == before


def test_a_verified_operation_records_a_completed_task_and_candidate(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED
    assert result.task.candidates == (result.candidate.id,)
    assert result.candidate.state is CandidateState.VERIFIED
    assert result.candidate.applicability is CandidateApplicability.APPLICABLE
    assert result.candidate.coverage is CandidateCoverage.COMPLETE
    assert result.candidate.language_fit is ResultLanguageFit.SATISFIES
    link = result.verifications[0]
    assert link.specification_kind == "HasDerivative"
    assert link.frame == result.candidate.frame
    assert link.coverage is Coverage.ONE_VERIFIED
    assert workspace.task(result.task.id) is result.task
    assert workspace.tasks() == (result.task,)
    assert workspace.candidates() == (result.candidate,)


def test_solve_linear_records_complete_set_coverage(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear_term(runtime), "linear")
    result = workspace.solve_linear(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.candidate is not None
    assert result.candidate.coverage is CandidateCoverage.COMPLETE
    assert result.verifications[0].coverage is Coverage.COMPLETE_SET
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED


def test_editing_a_set_candidate_to_a_scalar_is_out_of_scope(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear_term(runtime), "linear")
    result = workspace.solve_linear(source, runtime.variable)
    assert result.candidate is not None
    edited = workspace.edit_candidate(result.candidate.id, T.number(7))
    assert edited.candidate is not None
    assert (
        edited.candidate.language_fit
        is ResultLanguageFit.DOES_NOT_SATISFY
    )
    assert (
        edited.candidate.applicability
        is CandidateApplicability.OUT_OF_SCOPE
    )
    assert (
        workspace.task(result.candidate.task).state
        is TaskState.COMPLETED
    )


def test_branch_and_switch_keep_the_old_branch_visible(runtime):
    workspace = new_workspace(runtime)
    first = workspace.intake(T.number(1), "first")
    parent = workspace.revision
    branch = workspace.branch("left")
    left = workspace.intake(T.number(2), "left")
    left_head = workspace.revision
    assert workspace.undo()
    right = workspace.intake(T.number(3), "right")
    right_head = workspace.revision
    assert workspace.revision.id != left_head.id
    assert workspace.expressions() == (first, right)
    workspace.switch_to(left_head.id)
    assert workspace.expressions() == (first, left)
    workspace.switch_to(parent.id)
    assert workspace.expressions() == (first,)
    assert workspace.redo()
    assert workspace.revision.id == branch.id
    assert workspace.redo()
    assert workspace.revision.id == right_head.id
    assert branch.id in workspace._revisions


def test_merge_unions_visible_records_and_keeps_parents(runtime):
    workspace = new_workspace(runtime)
    first = workspace.intake(T.number(1), "first")
    parent = workspace.revision
    workspace.branch("left")
    left_item = workspace.intake(T.number(2), "left")
    left_head = workspace.revision
    workspace.switch_to(parent.id)
    right_item = workspace.intake(T.number(3), "right")
    right_head = workspace.revision
    merged = workspace.merge(left_head.id, "join")
    assert merged.parents == (right_head.id, left_head.id)
    assert workspace.expressions() == (first, right_item, left_item)
    assert workspace.revision.id == merged.id
    assert workspace.undo()
    assert workspace.revision.id == right_head.id
    assert workspace.redo()
    assert workspace.revision.id == merged.id


def test_merge_keeps_other_frame_objects_but_does_not_make_them_usable(runtime):
    workspace = new_workspace(runtime)
    workspace.intake(T.number(1), "parent")
    parent = workspace.revision
    workspace.branch("assumption")
    assumption = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )
    assumed = workspace.assume(assumption.term)
    assert assumed.status is OperationStatus.VERIFIED
    child_object = workspace.intake(T.number(2), "child")
    child_head = workspace.revision
    workspace.switch_to(parent.id)
    merged = workspace.merge(child_head.id, "cross-frame")
    assert merged.frame == parent.frame
    assert child_object in workspace.expressions()
    result = workspace.differentiate(child_object, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED
    assert "outside the current frame" in result.detail


def test_transaction_rolls_back_multiple_actions(runtime):
    workspace = new_workspace(runtime)
    before_stats = runtime.store.stats()
    before_revisions = dict(workspace._revisions)
    with pytest.raises(RuntimeError, match="abort"):
        with workspace.transaction():
            source = workspace.intake(source_term(runtime), "source")
            workspace.differentiate(source, runtime.variable)
            raise RuntimeError("abort")
    assert workspace.expressions() == ()
    assert workspace.tasks() == ()
    assert workspace.links() == ()
    assert runtime.store.stats() == before_stats
    assert workspace._revisions == before_revisions
    assert workspace.revision.id == next(iter(before_revisions))


def test_manual_check_reuses_the_recorded_certificate(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    first = workspace.differentiate(source, runtime.variable)
    assert first.candidate is not None
    checked = workspace.check_candidate(first.candidate.id)
    assert checked.status is OperationStatus.VERIFIED
    assert checked.result is not None
    assert checked.task is not None
    assert checked.task.state is TaskState.COMPLETED
    assert checked.candidate is not None
    assert checked.candidate.state is CandidateState.VERIFIED


def test_a_candidate_snapshots_the_execution_algebra(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    first = workspace.differentiate(source, runtime.variable)
    assert first.candidate is not None
    assert first.candidate.algebra is runtime.request
    checked = workspace.check_candidate(first.candidate.id)
    assert checked.status is OperationStatus.VERIFIED
    edited = workspace.edit_candidate(first.candidate.id, T.number(7))
    assert edited.candidate is not None
    assert edited.candidate.algebra is runtime.request
    assert edited.candidate.state is CandidateState.UNCHECKED


def test_candidates_record_the_declared_role_and_recheck_uses_it(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    differentiated = workspace.differentiate(source, runtime.variable)
    assert differentiated.candidate is not None
    assert differentiated.candidate.candidate_role is CandidateRole.RESULT
    checked = workspace.check_candidate(differentiated.candidate.id)
    assert checked.status is OperationStatus.VERIFIED
    assert checked.candidate is not None
    assert checked.candidate.candidate_role is CandidateRole.RESULT

    linear = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            head_app(
                runtime.signature,
                StructuralHead.TIMES,
                T.number(2),
                variable(runtime),
            ),
            T.number(4),
        ),
        "linear",
    )
    solved = workspace.solve_linear(linear, runtime.variable)
    assert solved.candidate is not None
    assert solved.candidate.candidate_role is CandidateRole.SET
    rechecked = workspace.check_candidate(solved.candidate.id)
    assert rechecked.status is OperationStatus.VERIFIED
    assert rechecked.candidate is not None
    assert rechecked.candidate.candidate_role is CandidateRole.SET


def test_editing_a_candidate_clears_its_certificate(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    first = workspace.differentiate(source, runtime.variable)
    assert first.candidate is not None
    edited = workspace.edit_candidate(
        first.candidate.id, T.number(7)
    )
    assert edited.status is OperationStatus.EDITED
    assert edited.candidate is not None
    assert edited.candidate.id != first.candidate.id
    assert edited.candidate.state is CandidateState.UNCHECKED
    assert edited.candidate.applicability is CandidateApplicability.APPLICABLE
    assert edited.candidate.coverage is CandidateCoverage.UNCLAIMED
    assert edited.candidate.language_fit is ResultLanguageFit.SATISFIES
    assert edited.candidate.candidate_role is CandidateRole.RESULT
    # Editing adds a new unchecked alternative; the old verified candidate and
    # its link remain visible, so the fixed task stays completed.
    assert (
        workspace.task(first.candidate.task).state
        is TaskState.COMPLETED
    )
    refused = workspace.check_candidate(edited.candidate.id)
    assert refused.status is OperationStatus.INVALID
    assert "no certificate" in refused.detail
    old = workspace.check_candidate(first.candidate.id)
    assert old.status is OperationStatus.VERIFIED
    assert workspace.task(first.candidate.task).state is TaskState.COMPLETED


def test_manual_check_refuses_an_unknown_candidate(runtime):
    workspace = new_workspace(runtime)
    result = workspace.check_candidate(CandidateId(999))
    assert result.status is OperationStatus.INVALID


def test_a_failed_workspace_record_rolls_back_the_kernel(runtime, monkeypatch):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    before_stats = runtime.store.stats()
    before_expressions = workspace.expressions()
    before_revision = workspace.revision

    def fail(*args, **kwargs):
        raise RuntimeError("workspace storage failed")

    monkeypatch.setattr(workspace, "_append_revision", fail)
    with pytest.raises(RuntimeError, match="workspace storage failed"):
        workspace.differentiate(source, runtime.variable)

    assert runtime.store.stats() == before_stats
    assert workspace.expressions() == before_expressions
    assert workspace.links() == ()
    assert workspace.revision is before_revision


def test_a_conditional_result_is_closed_by_the_same_problem_region(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    region = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=region,
    )
    assert result.status is OperationStatus.CONDITIONAL
    assert result.candidate is not None
    assert (
        result.candidate.applicability
        is CandidateApplicability.CONDITIONAL
    )
    assert result.verifications[0].condition == region
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED


def test_a_later_deferred_check_does_not_downgrade_a_verified_task(
    runtime, monkeypatch
):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED

    monkeypatch.setattr(
        workspace,
        "_commit",
        lambda proposal: Deferred(
            Reason.FRAGMENT, "the checker is unavailable"
        ),
    )
    checked = workspace.check_candidate(result.candidate.id)
    assert checked.status is OperationStatus.UNSUPPORTED
    assert checked.candidate is not None
    assert checked.candidate.state is CandidateState.UNVERIFIED
    assert (
        checked.candidate.applicability is CandidateApplicability.BLOCKED
    )
    assert checked.task is not None
    assert checked.task.state is TaskState.COMPLETED
    assert checked.task.blocker is None
    assert checked.task.detail == result.task.detail
    assert len(workspace.links()) == 2


def test_task_links_ignore_a_link_from_a_sibling_frame(runtime):
    workspace = new_workspace(runtime)
    # This candidate has no recorded links, so only the extra link is weighed.
    candidate_id = CandidateId(999)
    sibling = runtime.frames.create(runtime.frame.id)
    specification = runtime_proposition(runtime, T.TRUE)
    sibling_link = VerificationLink(
        candidate=candidate_id,
        specification=specification,
        judgment=JudgmentId(1),
        status=OperationStatus.VERIFIED,
        specification_kind="HasDerivative",
        frame=sibling.id,
        coverage=Coverage.ONE_VERIFIED,
    )
    assert workspace._task_links((candidate_id,), (sibling_link,)) == ()
    visible_link = replace(sibling_link, frame=runtime.frame.id)
    assert workspace._task_links((candidate_id,), (visible_link,)) == (
        visible_link,
    )


def test_task_links_refuse_a_mismatched_specification_kind(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    assert result.candidate.specifications
    candidate = result.candidate
    link = VerificationLink(
        candidate=candidate.id,
        specification=candidate.specifications[0],
        judgment=JudgmentId(1),
        status=OperationStatus.VERIFIED,
        specification_kind="OtherSpecification",
        frame=runtime.frame.id,
        coverage=Coverage.ONE_VERIFIED,
    )
    with pytest.raises(ValueError, match="specification kind"):
        workspace._task_links((candidate.id,), (link,))


def _region_above_zero(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )


def test_an_unsupported_execution_blocker_carries_its_target_and_budget(
    runtime,
):
    workspace = new_workspace(runtime)
    source = workspace.intake(unsupported_term(runtime), "reciprocal")
    region = _region_above_zero(runtime)
    budget = ExecutionBudget(max_nodes=11, max_depth=4)
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=region,
        budget=budget,
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.target == region
    assert result.blocker.budget == budget


@pytest.mark.parametrize(
    ("outcome", "status"),
    [
        (
            Deferred(Reason.GUARDED, "the checker needs a premise"),
            OperationStatus.UNKNOWN,
        ),
        (
            Rejected("the checker rejected the proposed evidence"),
            OperationStatus.INVALID,
        ),
    ],
)
def test_an_unverified_execution_blocker_carries_the_specification_and_budget(
    runtime, monkeypatch, outcome, status
):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    budget = ExecutionBudget(max_nodes=7, max_depth=3)
    captured = []

    def commit(proposal):
        captured.append(proposal.conclusions[0])
        return outcome

    monkeypatch.setattr(workspace, "_commit", commit)
    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        budget=budget,
    )
    assert result.status is status
    assert result.blocker is not None
    assert captured
    assert result.blocker.target == captured[0]
    assert result.blocker.budget == budget


def test_a_definition_blocker_carries_the_problem_region(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    region = _region_above_zero(runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=region,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None
    assert task.blocker.target == region


def test_a_run_task_blocker_carries_the_task_problem_region():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = workspace.intake(
        parse("sqrt(x)", runtime.table, runtime.signature),
        "root",
    )
    region = runtime_proposition(
        runtime,
        parse("x < 0", runtime.table, runtime.signature),
    )
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=region,
    )
    assert task.state is TaskState.READY
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.UNKNOWN
    assert result.task is not None
    assert result.task.blocker is not None
    assert result.task.blocker.target == region


def test_a_blocked_manual_task_carries_the_task_problem_region(
    runtime, monkeypatch
):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    region = _region_above_zero(runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=region,
    )
    assert task.state is TaskState.READY

    def fail(*args, **kwargs):
        return workspace._failure(
            "differentiate",
            OperationStatus.UNSUPPORTED,
            "the execution did not start",
        )

    monkeypatch.setattr(workspace, "_apply", fail)
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.INVALID
    assert result.blocker is not None
    assert result.blocker.target == region
    assert result.task is not None
    assert result.task.blocker is not None
    assert result.task.blocker.target == region


def test_a_blocked_manual_task_keeps_a_more_specific_target(
    runtime, monkeypatch
):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    region = _region_above_zero(runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=region,
    )
    specific = runtime_proposition(runtime, T.TRUE)

    def fail(*args, **kwargs):
        return workspace._failure(
            "differentiate",
            OperationStatus.UNSUPPORTED,
            "the execution did not start",
            blocker=Blocker(
                Reason.FRAGMENT,
                "the checker is missing",
                target=specific,
            ),
        )

    monkeypatch.setattr(workspace, "_apply", fail)
    result = workspace.run_task(task.id)
    assert result.blocker is not None
    assert result.blocker.target == specific


@pytest.mark.parametrize(
    ("outcome", "status"),
    [
        (
            Deferred(Reason.FRAGMENT, "the checker is unavailable"),
            OperationStatus.UNSUPPORTED,
        ),
        (
            Rejected("the checker rejected the proposed evidence"),
            OperationStatus.INVALID,
        ),
    ],
)
def test_a_manual_check_blocker_carries_the_candidate_specification(
    runtime, monkeypatch, outcome, status
):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    specification = result.candidate.specifications[0]
    monkeypatch.setattr(workspace, "_commit", lambda proposal: outcome)
    checked = workspace.check_candidate(result.candidate.id)
    assert checked.status is status
    assert checked.blocker is not None
    assert checked.blocker.target == specification
    assert checked.blocker.budget is None


def test_an_intake_event_records_its_output_revision(runtime):
    workspace = new_workspace(runtime)
    start = workspace.revision
    expression = workspace.intake(T.number(1), "one")
    revision = workspace.revision
    event = workspace.events()[-1]
    assert event.operation == "Intake"
    assert event.input_revision == start.id
    assert event.frame == runtime.frame.id
    assert event.inputs == ()
    assert event.parameters == ()
    assert event.execution_report is None
    assert event.objects == (expression.version,)
    assert event.actor_kind is ActorKind.USER
    assert event.operation_version == ""
    assert event.output_revision == revision.id
    assert revision.world == runtime.world.id
    assert revision.producing_event == event.id
    assert dict(revision.object_names)[expression.version] == (
        f"v{expression.version}"
    )


def test_a_differentiation_event_records_its_request_and_result(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    before = workspace.revision
    result = workspace.differentiate(source, runtime.variable)
    assert result.result is not None
    event = workspace.events()[-1]
    revision = workspace.revision
    assert event.operation == "differentiate"
    assert event.actor_kind is ActorKind.USER
    assert event.operation_version
    assert event.input_revision == before.id
    assert event.frame == runtime.frame.id
    assert event.inputs == (source.version,)
    assert event.parameters == ()
    assert event.execution_report is OperationStatus.VERIFIED
    assert event.objects == (result.result.version,)
    assert event.output_revision == revision.id
    assert revision.world == runtime.world.id
    assert revision.producing_event == event.id


def test_a_solve_linear_event_records_its_parameters_and_output_revision(
    runtime,
):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear_term(runtime), "linear")
    result = workspace.solve_linear(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    event = workspace.events()[-1]
    assert event.operation == "solve_linear"
    assert event.inputs == (source.version,)
    assert event.parameters == ()
    assert event.execution_report is OperationStatus.VERIFIED
    assert event.output_revision == workspace.revision.id


def test_a_manual_check_event_records_the_task_inputs(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    workspace.check_candidate(result.candidate.id)
    event = workspace.events()[-1]
    assert event.operation == "Check"
    assert event.inputs == (source.version,)
    assert event.parameters == ()
    assert event.execution_report is OperationStatus.VERIFIED
    assert event.output_revision == workspace.revision.id


def test_a_blocked_operation_event_records_its_request_and_report(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(unsupported_term(runtime), "reciprocal")
    workspace.differentiate(source, runtime.variable)
    event = workspace.events()[-1]
    assert event.operation == "differentiate"
    assert event.inputs == (source.version,)
    assert event.parameters == ()
    assert event.execution_report is OperationStatus.UNSUPPORTED
    assert event.output_revision == workspace.revision.id


def test_branch_and_merge_revisions_record_their_producing_event(runtime):
    workspace = new_workspace(runtime)
    workspace.intake(T.number(1), "first")
    parent = workspace.revision
    branch = workspace.branch("left")
    branch_event = workspace.events()[-1]
    assert branch.world == runtime.world.id
    assert branch.producing_event == branch_event.id
    assert branch_event.operation == "Branch"
    assert branch_event.input_revision == parent.id
    assert branch_event.output_revision == branch.id
    workspace.intake(T.number(2), "left")
    left_head = workspace.revision
    workspace.switch_to(parent.id)
    workspace.intake(T.number(3), "right")
    right_head = workspace.revision
    merged = workspace.merge(left_head.id, "join")
    merge_event = workspace.events()[-1]
    assert merged.world == runtime.world.id
    assert merged.producing_event == merge_event.id
    assert merge_event.operation == "Merge"
    assert merge_event.input_revision == right_head.id
    assert merge_event.output_revision == merged.id
    assert workspace.undo()
    assert workspace.revision.producing_event == right_head.producing_event
    assert workspace.redo()
    assert workspace.revision.producing_event == merge_event.id


def test_intake_and_differentiation_focus_their_result_objects(runtime):
    workspace = new_workspace(runtime)
    assert workspace.focus is None
    source = workspace.intake(source_term(runtime), "source")
    assert workspace.focus == ObjectFocus(source.version)
    result = workspace.differentiate(source, runtime.variable)
    assert result.result is not None
    assert workspace.focus == ObjectFocus(result.result.version)


def test_a_refused_operation_preserves_the_current_focus(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(unsupported_term(runtime), "reciprocal")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED
    assert workspace.focus == ObjectFocus(source.version)


def test_editing_a_candidate_focuses_the_edited_candidate(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    edited = workspace.edit_candidate(result.candidate.id, T.number(7))
    assert edited.candidate is not None
    assert workspace.focus == CandidateFocus(edited.candidate.id)


def test_manual_tasks_focus_the_task(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear_term(runtime), "linear")
    task = workspace.define_problem(
        "solve_linear",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
        coverage=Coverage.COMPLETE_SET,
    )
    assert workspace.focus == TaskFocus(task.id)
    executed = workspace.run_task(task.id)
    assert executed.task is not None
    assert workspace.focus == TaskFocus(executed.task.id)
    cancelled = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
    )
    assert workspace.focus == TaskFocus(cancelled.id)
    assert workspace.cancel_task(cancelled.id).status is OperationStatus.APPLIED
    assert workspace.focus == TaskFocus(cancelled.id)


def test_context_extensions_preserve_the_focus(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "source")
    focus = ObjectFocus(source.version)
    assert workspace.focus == focus
    assumed = workspace.assume(_region_above_zero(runtime).term)
    assert assumed.status is OperationStatus.VERIFIED
    assert workspace.focus == focus
    declared = workspace.declare("a", S.REAL)
    assert declared.status is OperationStatus.VERIFIED
    assert workspace.focus == focus
    defined = workspace.define("f", T.number(1))
    assert defined.status is OperationStatus.VERIFIED
    assert workspace.focus == focus


def test_rewrite_focuses_the_occurrence_and_substitute_the_result(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            variable(runtime),
            T.number(1),
        ),
        "source",
    )
    replacement = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.POWER,
            variable(runtime),
            T.number(2),
        ),
        "replacement",
    )
    found = workspace.occurrences(source, variable(runtime))
    assert len(found) == 1
    rewritten = workspace.rewrite(
        source, found[0], replacement, RewriteRelation.EQUIVALENT
    )
    assert rewritten.result is not None
    assert workspace.focus == OccurrenceFocus(
        rewritten.result.version, found[0]
    )
    substituted = workspace.substitute(
        source, runtime.variable, replacement
    )
    assert substituted.result is not None
    assert workspace.focus == ObjectFocus(substituted.result.version)


def test_branch_switch_and_merge_keep_the_revision_focus(runtime):
    workspace = new_workspace(runtime)
    first = workspace.intake(T.number(1), "first")
    parent = workspace.revision
    branch = workspace.branch("left")
    assert branch.focus == ObjectFocus(first.version)
    left = workspace.intake(T.number(2), "left")
    left_head = workspace.revision
    workspace.switch_to(parent.id)
    assert workspace.focus == ObjectFocus(first.version)
    workspace.switch_to(left_head.id)
    assert workspace.focus == ObjectFocus(left.version)
    workspace.switch_to(parent.id)
    right = workspace.intake(T.number(3), "right")
    right_head = workspace.revision
    merged = workspace.merge(left_head.id, "join")
    assert merged.parents == (right_head.id, left_head.id)
    assert merged.focus == ObjectFocus(right.version)


def test_merge_cases_keeps_the_base_focus(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "source")
    base = workspace.revision
    split = workspace.case_split(_region_above_zero(runtime).term)
    assert split.split is not None
    assert workspace.focus == base.focus
    merged = workspace.merge_cases(split.split)
    assert merged.revision is not None
    assert merged.revision.focus == ObjectFocus(source.version)


def test_new_revisions_and_events_record_the_frame_digest(runtime):
    workspace = new_workspace(runtime)
    expected = runtime.frames.digest(runtime.frame.id)
    workspace.intake(variable(runtime))
    revision = workspace.revision
    event = workspace.events()[-1]
    assert revision.frame_digest == expected
    assert event.frame_digest == expected


def test_a_context_extension_changes_the_recorded_revision_digest(runtime):
    workspace = new_workspace(runtime)
    before = runtime.frames.digest(workspace.frame)
    declared = workspace.declare("a", S.REAL)
    assert declared.status is OperationStatus.VERIFIED
    after = runtime.frames.digest(workspace.frame)
    assert after != before
    assert workspace.revision.frame_digest == after


def test_revision_and_event_reject_a_forged_frame_digest(runtime):
    workspace = new_workspace(runtime)
    workspace.intake(variable(runtime))
    revision = workspace.revision
    event = workspace.events()[-1]
    assert replace(revision, frame_digest="0" * 64).frame_digest == "0" * 64
    with pytest.raises(ValueError):
        replace(revision, frame_digest="not-a-digest")
    with pytest.raises(ValueError):
        replace(event, frame_digest="A" * 64)
    with pytest.raises(ValueError):
        replace(event, frame_digest="0" * 63)


def test_extension_records_a_verified_construction_relation(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative_region(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    function = define_real_function(
        workspace, runtime, square_term(runtime), domain, "f"
    )
    representation = workspace.intake(product_term(runtime), "extension")
    outcome = workspace.extend_function(function, representation, true, true)
    assert isinstance(outcome, FunctionDefined)
    relations = workspace.construction_relations()
    assert len(relations) == 1
    relation = relations[0]
    assert relation.kind == "function_extension"
    assert relation.source == function.version
    assert relation.target == outcome.function.version
    assert relation.frame == workspace.frame
    links = workspace.links()
    assert len(links) == 1
    assert links[0].status is OperationStatus.VERIFIED
    assert links[0].judgment is not None
    assert relation.specification == links[0].specification
    assert isinstance(relation.specification.term, T.Apply)
    operator = relation.specification.term.operator
    assert isinstance(operator, T.SymbolRef)
    assert runtime.table.name_of(operator.symbol_id) == "EqualOn"


def test_a_refused_extension_records_no_construction_relation(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative_region(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    function = define_real_function(
        workspace, runtime, square_term(runtime), domain, "f"
    )
    bad = workspace.intake(shifted_term(runtime), "bad extension")
    refused = workspace.extend_function(function, bad, true, true)
    assert isinstance(refused, FunctionRefused)
    assert workspace.construction_relations() == ()
    assert workspace.functions() == (function,)


def test_undo_hides_a_construction_relation_and_redo_restores_it(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative_region(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    function = define_real_function(
        workspace, runtime, square_term(runtime), domain, "f"
    )
    representation = workspace.intake(product_term(runtime), "extension")
    outcome = workspace.extend_function(function, representation, true, true)
    assert isinstance(outcome, FunctionDefined)
    relation = workspace.construction_relations()[0]
    assert workspace.undo()
    assert workspace.construction_relations() == ()
    assert workspace.redo()
    assert workspace.construction_relations() == (relation,)


def test_merge_preserves_and_deduplicates_construction_relations(runtime):
    workspace = new_workspace(runtime)
    domain = nonnegative_region(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    function = define_real_function(
        workspace, runtime, square_term(runtime), domain, "f"
    )
    first = workspace.extend_function(
        function,
        workspace.intake(product_term(runtime), "first extension"),
        true,
        true,
    )
    assert isinstance(first, FunctionDefined)
    inherited = workspace.construction_relations()
    assert len(inherited) == 1
    parent = workspace.revision
    workspace.branch("left")
    second = workspace.extend_function(
        first.function,
        workspace.intake(square_term(runtime), "second extension"),
        true,
        true,
    )
    assert isinstance(second, FunctionDefined)
    left_relations = workspace.construction_relations()
    assert len(left_relations) == 2
    left_head = workspace.revision
    workspace.switch_to(parent.id)
    workspace.branch("right")
    merged = workspace.merge(left_head.id, "join")
    assert merged.construction_relations == left_relations
    assert len(merged.construction_relations) == 2


def test_merge_cases_preserves_and_deduplicates_construction_relations(
    runtime,
):
    workspace = new_workspace(runtime)
    domain = nonnegative_region(runtime)
    true = runtime_proposition(runtime, T.TRUE)
    function = define_real_function(
        workspace, runtime, square_term(runtime), domain, "f"
    )
    first = workspace.extend_function(
        function,
        workspace.intake(product_term(runtime), "first extension"),
        true,
        true,
    )
    assert isinstance(first, FunctionDefined)
    inherited = workspace.construction_relations()
    assert len(inherited) == 1
    split = workspace.case_split(_region_above_zero(runtime).term)
    assert split.split is not None
    workspace.switch_to(split.split.positive_revision)
    second = workspace.extend_function(
        first.function,
        workspace.intake(square_term(runtime), "second extension"),
        true,
        true,
    )
    assert isinstance(second, FunctionDefined)
    branch_relations = workspace.construction_relations()
    assert len(branch_relations) == 2
    merged = workspace.merge_cases(split.split)
    assert merged.revision is not None
    assert merged.revision.construction_relations == branch_relations
    assert len(merged.revision.construction_relations) == 2


def test_construction_relation_records_are_validated(runtime):
    workspace = new_workspace(runtime)
    revision = workspace.revision
    proposition = runtime_proposition(runtime, T.TRUE)
    other = nonnegative_region(runtime)
    frame = runtime.frame.id
    relation = ConstructionRelation(
        1, 2, "function_extension", proposition, frame
    )
    assert relation.source == 1
    with pytest.raises(ValueError):
        ConstructionRelation(1, 1, "function_extension", proposition, frame)
    with pytest.raises(TypeError):
        ConstructionRelation(
            True, 2, "function_extension", proposition, frame
        )
    with pytest.raises(TypeError):
        ConstructionRelation(1, 2, "function_extension", T.TRUE, frame)
    with pytest.raises(TypeError):
        ConstructionRelation(1, 2, "function_extension", proposition, True)
    with pytest.raises(TypeError):
        ConstructionRelation(1, 2, 7, proposition, frame)
    with pytest.raises(ValueError):
        ConstructionRelation(1, 2, "", proposition, frame)
    accepted = replace(revision, construction_relations=(relation,))
    assert accepted.construction_relations == (relation,)
    conflicting = ConstructionRelation(
        1, 2, "function_extension", other, frame
    )
    with pytest.raises(ValueError):
        replace(
            revision,
            construction_relations=(relation, conflicting),
        )
    with pytest.raises(ValueError):
        replace(
            revision,
            construction_relations=(relation, relation),
        )
    with pytest.raises(TypeError):
        replace(revision, construction_relations=(T.TRUE,))
