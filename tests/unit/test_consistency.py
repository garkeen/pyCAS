"""Frame consistency: explicit states, the contradiction rule and assessment."""

import pytest
from support import head_app, proposition_in, variable

from cas.kernel.consistency import ContradictionChecker, assess_consistency
from cas.kernel.evidence import CheckRequest, Unverified, Verified
from cas.kernel.model import Inconsistent, Unassessed
from cas.kernel.store import KernelError
from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap
from cas.semantics.frames import Hypothesis
from cas.syntax import term as T
from cas.workflow.records import OperationStatus
from cas.workflow.workspace import Workspace


def gt_zero(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.GT,
        variable(runtime),
        T.number(0),
    )


def not_gt_zero(runtime):
    return head_app(runtime.signature, StructuralHead.NOT, gt_zero(runtime))


def square(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(2),
    )


def two_level_hypotheses(runtime, second_term):
    """A base, a child assuming x > 0 and a grandchild assuming `second_term`."""
    signature = runtime.signature
    first_proposition = proposition_in(
        runtime.frames,
        runtime.frame.id,
        signature,
        gt_zero(runtime),
    )
    first = runtime.frames.create(
        runtime.frame.id,
        hypotheses=(Hypothesis(first_proposition),),
    )
    second_proposition = proposition_in(
        runtime.frames, first.id, signature, second_term()
    )
    second = runtime.frames.create(
        first.id, hypotheses=(Hypothesis(second_proposition),)
    )
    return first, second


def test_visible_complementary_hypotheses_prove_false():
    runtime = bootstrap()
    _, frame = two_level_hypotheses(runtime, lambda: not_gt_zero(runtime))
    false = proposition_in(
        runtime.frames, frame.id, runtime.signature, T.FALSE
    )
    outcome = ContradictionChecker(
        runtime.frames, runtime.signature
    ).check(CheckRequest(frame.id, (false,), (), None))
    assert isinstance(outcome, Verified)
    assert outcome.checked == (false,)


def test_a_false_assumption_is_itself_a_contradiction():
    runtime = bootstrap()
    false = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        T.FALSE,
    )
    child = runtime.frames.create(
        runtime.frame.id, hypotheses=(Hypothesis(false),)
    )
    target = proposition_in(
        runtime.frames, child.id, runtime.signature, T.FALSE
    )
    outcome = ContradictionChecker(
        runtime.frames, runtime.signature
    ).check(CheckRequest(child.id, (target,), (), None))
    assert isinstance(outcome, Verified)


def test_unrelated_hypotheses_are_not_a_contradiction():
    runtime = bootstrap()
    _, frame = two_level_hypotheses(
        runtime,
        lambda: head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(1),
        ),
    )
    false = proposition_in(
        runtime.frames, frame.id, runtime.signature, T.FALSE
    )
    outcome = ContradictionChecker(
        runtime.frames, runtime.signature
    ).check(CheckRequest(frame.id, (false,), (), None))
    assert isinstance(outcome, Unverified)


def test_the_contradiction_rule_proves_false_only():
    runtime = bootstrap()
    _, frame = two_level_hypotheses(runtime, lambda: not_gt_zero(runtime))
    other = proposition_in(
        runtime.frames, frame.id, runtime.signature, gt_zero(runtime)
    )
    outcome = ContradictionChecker(
        runtime.frames, runtime.signature
    ).check(CheckRequest(frame.id, (other,), (), None))
    assert isinstance(outcome, Unverified)


def test_assessment_without_a_contradiction_writes_nothing():
    runtime = bootstrap()
    before = runtime.store.stats()
    state = assess_consistency(runtime.store, runtime.frame.id)
    assert isinstance(state, Unassessed)
    assert runtime.store.stats() == before
    assert isinstance(
        runtime.store.consistency(runtime.frame.id), Unassessed
    )


def test_contradictory_assumptions_mark_the_frame_inconsistent():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(square(runtime), "source")

    first = workspace.assume(gt_zero(runtime))
    assert first.status is OperationStatus.VERIFIED
    assert not first.consistency.is_inconsistent()
    assert isinstance(
        runtime.store.consistency(workspace.frame), Unassessed
    )

    second = workspace.assume(not_gt_zero(runtime))
    assert second.status is OperationStatus.INVALID
    assert isinstance(second.consistency, Inconsistent)
    witness = runtime.store.get_judgment(second.consistency.witness)
    assert witness.proposition.term == T.FALSE
    inference = runtime.store.inference_of(witness.id)
    assert inference.checker_id == ContradictionChecker.id
    assert runtime.store.applicability(
        witness.id, workspace.frame
    ).is_applicable()
    assert workspace.events()[-1].judgments == (
        second.judgment,
        witness.id,
    )

    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.INVALID
    assert "inconsistent" in result.detail

    assert workspace.undo()
    assert not runtime.store.consistency(
        workspace.frame
    ).is_inconsistent()
    assert workspace.differentiate(
        source, runtime.variable
    ).status is OperationStatus.VERIFIED


def test_inconsistency_is_inherited_and_stops_new_assumptions():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    workspace.assume(gt_zero(runtime))
    workspace.assume(not_gt_zero(runtime))
    inconsistent = workspace.frame
    child = runtime.frames.create(inconsistent)
    assert isinstance(
        runtime.store.consistency(child.id), Inconsistent
    )
    third = workspace.assume(gt_zero(runtime))
    assert third.status is OperationStatus.INVALID
    assert third.frame == inconsistent
    assert "inconsistent" in third.detail


def test_a_false_assumption_marks_the_frame_inconsistent():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    result = workspace.assume(T.FALSE)
    assert result.status is OperationStatus.INVALID
    assert isinstance(result.consistency, Inconsistent)


def test_a_contradiction_witness_must_state_false():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(square(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.verifications
    assert result.verifications[0].judgment is not None
    with pytest.raises(KernelError):
        runtime.store.record_inconsistency(
            workspace.frame, result.verifications[0].judgment
        )


def test_a_ground_false_assumption_is_a_contradiction():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    false_term = head_app(
        runtime.signature, StructuralHead.NOT, T.TRUE
    )
    result = workspace.assume(false_term)
    assert result.status is OperationStatus.INVALID
    assert isinstance(result.consistency, Inconsistent)
