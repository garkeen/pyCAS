"""Manual problems, execution attempts, rewrites and case splits."""

from dataclasses import replace

import pytest
from support import head_app, runtime_proposition, variable

from cas.frontend import parse
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    Exactness,
    InterpretationRequirement,
    ParameterMode,
    ResultLanguage,
    ValueDomain,
)
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import (
    bootstrap,
    bootstrap_elementary,
    new_workspace,
)
from cas.syntax import term as T
from cas.syntax.occurrences import Occurrence
from cas.workflow.records import (
    ExecutionState,
    OperationStatus,
    RewriteRelation,
    TaskOrigin,
    TaskState,
)


def linear(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            T.number(2),
            variable(runtime),
        ),
        T.number(4),
    )


def test_a_manual_problem_runs_only_when_the_operation_builds_it(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear(runtime), "linear")
    task = workspace.define_problem(
        "solve_linear",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.READY
    assert task.origin is TaskOrigin.MANUAL
    assert task.inputs == (source.version,)
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED
    assert result.task is not None
    assert result.task.id == task.id
    assert result.task.state is TaskState.COMPLETED
    assert result.result is not None
    execution = next(
        item
        for item in workspace.tasks()
        if item.origin is TaskOrigin.EXECUTION
    )
    assert execution.parent == task.id
    graph = dict(workspace.task_graph())
    assert graph[execution.id] == (task.id,)
    assert workspace.attempt(execution.attempts[0]).state is ExecutionState.FINISHED


def _positive_region(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )


def _sqrt_expression(workspace, runtime):
    return workspace.intake(
        parse("sqrt(x)", runtime.table, runtime.signature), "sqrt(x)"
    )


def test_a_manual_problem_with_an_externalizable_premise_keeps_a_result_region_partial():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    premise = _positive_region(runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )
    assert task.state is TaskState.READY
    assert task.problem.externalizable == (premise,)

    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.CONDITIONAL
    assert result.region == premise
    assert result.verifications
    assert result.verifications[0].condition == premise
    assert result.task is not None
    assert result.task.state is TaskState.PARTIALLY_SOLVED
    assert result.task.problem.externalizable == (premise,)
    assert workspace.task(task.id).state is TaskState.PARTIALLY_SOLVED


def test_checking_a_conditional_candidate_keeps_a_result_region_partial():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    premise = _positive_region(runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )
    result = workspace.run_task(task.id)
    assert result.candidate is not None
    assert result.task is not None
    assert result.task.state is TaskState.PARTIALLY_SOLVED

    checked = workspace.check_candidate(result.candidate.id)
    assert checked.status is OperationStatus.CONDITIONAL
    assert checked.verifications
    assert checked.verifications[0].condition == premise
    assert checked.task is not None
    assert checked.task.state is TaskState.PARTIALLY_SOLVED


@pytest.mark.parametrize("other_premise", [False, True])
def test_a_manual_problem_with_a_different_externalizable_set_stays_partial(
    other_premise,
):
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    premise = _positive_region(runtime)
    externalizable = ()
    if other_premise:
        externalizable = (
            runtime_proposition(
                runtime,
                head_app(
                    runtime.signature,
                    StructuralHead.GT,
                    variable(runtime),
                    T.number(1),
                ),
            ),
        )
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        externalizable=externalizable,
    )

    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.CONDITIONAL
    assert result.region == premise
    assert result.task is not None
    assert result.task.state is TaskState.PARTIALLY_SOLVED
    assert result.task.problem.externalizable == externalizable


def test_an_unconditional_manual_result_completes_with_allowed_premises():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = workspace.intake(
        parse("x^2", runtime.table, runtime.signature), "x^2"
    )
    premise = _positive_region(runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )

    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED
    assert result.region is None
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED


def test_apply_carries_the_externalizable_set_into_candidate_and_task():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    premise = _positive_region(runtime)

    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )
    assert result.status is OperationStatus.CONDITIONAL
    assert result.candidate is not None
    assert result.candidate.problem.externalizable == (premise,)
    assert result.task is not None
    assert result.task.problem.externalizable == (premise,)
    assert result.task.state is TaskState.PARTIALLY_SOLVED


def test_same_problem_rejects_a_rebuilt_externalizable_set():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    premise = _positive_region(runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )

    rebuilt = replace(task.problem, externalizable=())
    assert workspace._same_problem(task.problem, task.problem)
    assert not workspace._same_problem(task.problem, rebuilt)


def test_same_problem_rejects_a_rebuilt_request_contract():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
    )
    problem = task.problem
    assert problem.interpretation_requirement is (
        InterpretationRequirement.FORMAL
    )
    assert problem.domain_requirement == DomainRequirement(
        ValueDomain.RATIONAL, ValueDomain.REAL
    )
    assert workspace._same_problem(problem, replace(problem))

    other_interpretation = replace(
        problem,
        interpretation_requirement=InterpretationRequirement.EMBEDDED,
    )
    assert not workspace._same_problem(problem, other_interpretation)

    other_domain = replace(
        problem,
        domain_requirement=DomainRequirement(
            ValueDomain.INTEGER, ValueDomain.REAL
        ),
    )
    assert not workspace._same_problem(problem, other_domain)

    with pytest.raises(ValueError, match="approximate"):
        replace(problem, exactness=Exactness.APPROXIMATE)
    approximate = replace(problem)
    object.__setattr__(approximate, "exactness", Exactness.APPROXIMATE)
    assert not workspace._same_problem(problem, approximate)


def _premise_from_a_hidden_child_frame(workspace, runtime):
    assumption = workspace.assume(_positive_region(runtime).term)
    assert assumption.frame is not None
    assert assumption.frame != runtime.frame.id
    premise = runtime_proposition(runtime, T.TRUE, assumption.frame)
    assert workspace.undo()
    assert workspace.revision.frame == runtime.frame.id
    return premise


def test_apply_refuses_an_externalizable_premise_outside_the_frame():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    premise = _premise_from_a_hidden_child_frame(workspace, runtime)

    result = workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        externalizable=(premise,),
    )
    assert result.status is OperationStatus.INVALID
    assert "externalizable" in result.detail


def test_define_problem_refuses_an_externalizable_premise_outside_the_frame():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = _sqrt_expression(workspace, runtime)
    premise = _premise_from_a_hidden_child_frame(workspace, runtime)

    with pytest.raises(ValueError, match="externalizable"):
        workspace.define_problem(
            "differentiate",
            (source,),
            target=runtime.variable,
            externalizable=(premise,),
        )


def test_a_manual_problem_with_a_different_shape_is_blocked_at_definition(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear(runtime), "linear")
    task = workspace.define_problem(
        "solve_linear",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.EXPRESSION,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None


def test_a_manual_problem_with_an_unsupported_parameter_mode_is_blocked_at_definition(
    runtime,
):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear(runtime), "linear")
    task = workspace.define_problem(
        "solve_linear",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
        coverage=Coverage.COMPLETE_SET,
        parameter_mode=ParameterMode.GENERIC_PARAMETERS,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None


def test_a_manual_problem_with_an_out_of_fragment_input_is_blocked_at_definition(
    runtime,
):
    workspace = new_workspace(runtime)
    x = variable(runtime)
    left = workspace.intake(x, "x")
    reciprocal = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.POWER,
            x,
            T.number(-1),
        ),
        "x^-1",
    )
    task = workspace.define_problem(
        "polynomial_gcd",
        (left, reciprocal),
        target=runtime.variable,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None
    assert "univariate_polynomial_representation" in task.blocker.missing


def _assert_definition_not_ready(workspace, *args, **kwargs):
    try:
        task = workspace.define_problem(*args, **kwargs)
    except ValueError:
        return
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None


@pytest.mark.parametrize(
    ("factory", "operation", "sources", "result_language"),
    [
        (bootstrap, "differentiate", ("x^2",), ResultLanguage.SET),
        (bootstrap, "integrate", ("x^2",), ResultLanguage.SET),
        (
            bootstrap,
            "polynomial_gcd",
            ("x^2 - 1", "x - 1"),
            ResultLanguage.SET,
        ),
        (
            bootstrap,
            "resultant",
            ("x^2 - 1", "x - 1"),
            ResultLanguage.SET,
        ),
        (
            bootstrap_elementary,
            "hermite_reduce",
            ("1/x",),
            ResultLanguage.EXPRESSION,
        ),
    ],
)
def test_define_problem_blocks_result_language_mismatch(
    factory, operation, sources, result_language
):
    runtime = factory()
    workspace = new_workspace(runtime)
    inputs = tuple(
        workspace.intake(parse(text, runtime.table, runtime.signature))
        for text in sources
    )
    _assert_definition_not_ready(
        workspace,
        operation,
        inputs,
        target=runtime.variable,
        result_language=result_language,
    )


@pytest.mark.parametrize(
    ("factory", "operation", "sources", "result_language"),
    [
        (bootstrap, "differentiate", ("x^2",), ResultLanguage.EXPRESSION),
        (bootstrap, "integrate", ("x^2",), ResultLanguage.EXPRESSION),
        (
            bootstrap,
            "polynomial_gcd",
            ("x^2 - 1", "x - 1"),
            ResultLanguage.EXPRESSION,
        ),
        (
            bootstrap,
            "resultant",
            ("x^2 - 1", "x - 1"),
            ResultLanguage.EXPRESSION,
        ),
        (
            bootstrap_elementary,
            "hermite_reduce",
            ("1/x",),
            ResultLanguage.DECOMPOSITION,
        ),
    ],
)
def test_define_problem_blocks_parameter_mode_mismatch(
    factory, operation, sources, result_language
):
    runtime = factory()
    workspace = new_workspace(runtime)
    inputs = tuple(
        workspace.intake(parse(text, runtime.table, runtime.signature))
        for text in sources
    )
    _assert_definition_not_ready(
        workspace,
        operation,
        inputs,
        target=runtime.variable,
        result_language=result_language,
        coverage=Coverage.ONE_VERIFIED,
        parameter_mode=ParameterMode.GENERIC_PARAMETERS,
    )


def test_define_problem_blocks_solve_linear_one_verified(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear(runtime), "linear")
    _assert_definition_not_ready(
        workspace,
        "solve_linear",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
        coverage=Coverage.ONE_VERIFIED,
    )


def test_run_task_refuses_a_problem_blocked_at_definition(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "x")
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.BLOCKED
    before = runtime.store.stats()
    result = workspace.run_task(task.id)
    assert result.status is not OperationStatus.VERIFIED
    assert result.candidate is None
    assert runtime.store.stats() == before


def test_a_blocked_definition_keeps_the_requested_coverage(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "x")
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.BLOCKED
    assert task.problem.coverage is Coverage.COMPLETE_SET


def test_a_blocked_definition_keeps_the_requested_result_language(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "x")
    task = workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
    )
    assert task.state is TaskState.BLOCKED
    assert task.problem.result_language is ResultLanguage.SET


def test_a_manual_task_defined_in_an_ancestor_frame_runs_in_a_descendant(
    runtime,
):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "x")
    task = workspace.define_problem(
        "differentiate", (source,), target=runtime.variable
    )
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
    assert assumed.frame != runtime.frame.id
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED
    assert result.candidate is not None


def test_cancel_task_keeps_completed_results(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear(runtime), "linear")
    task = workspace.define_problem(
        "solve_linear",
        (source,),
        target=runtime.variable,
        result_language=ResultLanguage.SET,
        coverage=Coverage.COMPLETE_SET,
    )
    cancelled = workspace.cancel_task(task.id)
    assert cancelled.status is OperationStatus.APPLIED
    assert cancelled.task is not None
    assert cancelled.task.state is TaskState.CANCELLED
    assert workspace.attempt(cancelled.task.attempts[0]).state is (
        ExecutionState.CANCELLED
    )
    refused = workspace.run_task(task.id)
    assert refused.status is OperationStatus.INVALID
    done = workspace.run_task(
        workspace.define_problem(
            "solve_linear",
            (source,),
            target=runtime.variable,
            result_language=ResultLanguage.SET,
            coverage=Coverage.COMPLETE_SET,
        ).id
    )
    assert done.task is not None
    assert workspace.cancel_task(done.task.id).status is OperationStatus.INVALID


def test_rewrite_records_the_occurrence_and_relation(runtime):
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
    result = workspace.rewrite(
        source, found[0], replacement, RewriteRelation.EQUIVALENT
    )
    assert result.status is OperationStatus.APPLIED
    assert result.result is not None
    assert result.result.id == source.id
    assert result.result.version != source.version
    assert result.record is not None
    assert result.record.occurrence == found[0]
    assert workspace.rewrites() == (result.record,)
    bad = workspace.rewrite(
        source,
        Occurrence((99,)),
        replacement,
        RewriteRelation.EQUIVALENT,
    )
    assert bad.status is OperationStatus.INVALID


def test_substitution_records_a_substitution_relation(runtime):
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
    replacement = workspace.intake(T.number(2), "replacement")
    result = workspace.substitute(source, runtime.variable, replacement)
    assert result.status is OperationStatus.APPLIED
    assert result.result is not None
    assert result.result.term == head_app(
        runtime.signature,
        StructuralHead.PLUS,
        T.number(2),
        T.number(1),
    )
    assert result.record is not None
    assert result.record.relation is RewriteRelation.SUBSTITUTION
    assert result.record.occurrence is None


def test_case_split_and_merge_preserve_both_branches(runtime):
    workspace = new_workspace(runtime)
    assumption = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.status is OperationStatus.VERIFIED
    assert split.split is not None
    assert workspace.case_splits() == (split.split,)
    positive = workspace._revisions[split.split.positive_revision]
    negative = workspace._revisions[split.split.negative_revision]
    assert positive.frame == split.split.positive_frame
    assert negative.frame == split.split.negative_frame
    merged = workspace.merge_cases(split.split)
    assert merged.status is OperationStatus.VERIFIED
    assert merged.revision is not None
    assert merged.revision.parents == (
        base.id,
        positive.id,
        negative.id,
    )
    assert merged.revision.id == workspace.revision.id
    assert split.split in workspace.case_splits()
    assert workspace.merge_cases(split.split).status is (
        OperationStatus.INVALID
    )


def test_a_case_cannot_repeat_an_assumption(runtime):
    workspace = new_workspace(runtime)
    assumption = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )
    workspace.assume(assumption.term)
    split = workspace.case_split(assumption.term)
    assert split.status is OperationStatus.INVALID


def _case_assumption(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )


def test_merge_cases_includes_work_added_after_the_split(runtime):
    workspace = new_workspace(runtime)
    assumption = _case_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None

    workspace.switch_to(split.split.positive_revision)
    positive_source = workspace.intake(variable(runtime), "positive x")
    positive_result = workspace.differentiate(
        positive_source, runtime.variable
    )
    assert positive_result.task is not None
    positive_head = workspace.revision

    workspace.switch_to(split.split.negative_revision)
    negative_source = workspace.intake(variable(runtime), "negative x")
    negative_result = workspace.differentiate(
        negative_source, runtime.variable
    )
    assert negative_result.task is not None
    negative_head = workspace.revision

    merged = workspace.merge_cases(split.split)
    assert merged.status is OperationStatus.VERIFIED
    assert merged.revision is not None
    assert merged.revision.parents == (
        base.id,
        positive_head.id,
        negative_head.id,
    )
    assert positive_source in workspace.expressions()
    assert negative_source in workspace.expressions()
    assert workspace.task(positive_result.task.id) is positive_result.task
    assert workspace.task(negative_result.task.id) is negative_result.task
    assert positive_result.candidate is not None
    assert negative_result.candidate is not None
    assert workspace.candidate(positive_result.candidate.id) is (
        positive_result.candidate
    )
    assert workspace.candidate(negative_result.candidate.id) is (
        negative_result.candidate
    )


def test_merge_cases_refuses_a_hidden_or_forged_split(runtime):
    workspace = new_workspace(runtime)
    assumption = _case_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None

    assert workspace.undo()
    assert workspace.revision.id == base.id
    hidden = workspace.merge_cases(split.split)
    assert hidden.status is OperationStatus.INVALID
    assert "not visible" in hidden.detail

    workspace.switch_to(split.split.positive_revision)
    forged = replace(
        split.split,
        assumption=runtime_proposition(runtime, T.TRUE),
    )
    refused = workspace.merge_cases(forged)
    assert refused.status is OperationStatus.INVALID
    assert "recorded split" in refused.detail


def test_undo_and_redo_from_a_case_merge_follow_the_declared_parents(runtime):
    workspace = new_workspace(runtime)
    assumption = _case_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None
    positive = workspace._revisions[split.split.positive_revision]
    negative = workspace._revisions[split.split.negative_revision]
    merged = workspace.merge_cases(split.split)
    assert merged.revision is not None
    assert merged.revision.parents == (base.id, positive.id, negative.id)
    for parent in merged.revision.parents:
        assert merged.revision.id in workspace._children[parent]

    assert workspace.undo()
    assert workspace.revision.id == base.id
    assert workspace.redo()
    assert workspace.revision.id == merged.revision.id

    workspace.switch_to(positive.id)
    assert workspace.redo()
    assert workspace.revision.id == merged.revision.id


def test_a_case_conclusion_records_the_two_branch_premises(runtime):
    workspace = new_workspace(runtime)
    assumption = _case_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None

    workspace.switch_to(split.split.positive_revision)
    positive_source = workspace.intake(variable(runtime), "positive x")
    positive_result = workspace.differentiate(
        positive_source, runtime.variable
    )
    assert positive_result.verifications
    positive_judgment = positive_result.verifications[0].judgment
    assert positive_judgment is not None

    workspace.switch_to(split.split.negative_revision)
    negative_source = workspace.intake(variable(runtime), "negative x")
    negative_result = workspace.differentiate(
        negative_source, runtime.variable
    )
    assert negative_result.verifications
    negative_judgment = negative_result.verifications[0].judgment
    assert negative_judgment is not None

    workspace.switch_to(base.id)
    conclusion = workspace.merge_case_conclusion(
        split.split, positive_judgment, negative_judgment
    )
    assert conclusion.status is OperationStatus.VERIFIED
    assert conclusion.judgment is not None
    inference = runtime.store.inference_of(conclusion.judgment)
    assert inference.premises == (positive_judgment, negative_judgment)
    assert split.split in workspace.revision.case_splits
