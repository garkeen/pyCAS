"""Frame-scoped assumptions in the workspace and session."""

import pytest
from support import head_app, variable

from cas.frontend.errors import SessionError
from cas.frontend.session import Session
from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap
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


def square(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(2),
    )


def test_assume_creates_a_child_frame_and_a_hypothesis_judgment():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    result = workspace.assume(gt_zero(runtime))
    assert result.status is OperationStatus.VERIFIED
    assert result.judgment is not None
    assert result.frame != runtime.frame.id
    assert workspace.frame == result.frame
    assert result.proposition is not None
    assert result.proposition in runtime.frames.assumptions(workspace.frame)
    judgment = runtime.store.get_judgment(result.judgment)
    assert judgment.proposition == result.proposition
    inference = runtime.store.inference_of(result.judgment)
    assert inference.checker_id == "kernel.hypothesis"
    assert [event.operation for event in workspace.events()] == ["Assume"]


def test_operations_use_the_current_assumption_frame():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(square(runtime), "source")
    result = workspace.assume(gt_zero(runtime))
    differentiated = workspace.differentiate(source, runtime.variable)
    assert differentiated.status is OperationStatus.VERIFIED
    assert differentiated.candidate is not None
    assert differentiated.candidate.frame == result.frame
    assert differentiated.verification is not None
    assert (
        differentiated.verification.specification.meaning.frame
        == result.frame
    )
    assert differentiated.result is not None
    assert differentiated.result.frame == result.frame


def test_assume_rejects_non_propositions_and_keeps_the_frame():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    invalid = workspace.assume(T.number(1))
    assert invalid.status is OperationStatus.INVALID
    assert workspace.frame == runtime.frame.id

    first = workspace.assume(gt_zero(runtime))
    assert first.status is OperationStatus.VERIFIED
    assert workspace.frame == first.frame


def test_undo_and_redo_move_the_frame_but_keep_the_ledger():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    initial = workspace.frame
    result = workspace.assume(gt_zero(runtime))
    judgment = result.judgment
    assert workspace.undo()
    assert workspace.frame == initial
    assert runtime.store.get_judgment(judgment) is not None
    assert workspace.redo()
    assert workspace.frame == result.frame


def test_the_session_accepts_assumptions():
    runtime = bootstrap()
    session = Session(runtime)
    assert session.execute("assume x > 0") == "assumed: x > 0"
    frame = session.workspace.frame
    assert frame != runtime.frame.id
    assert session.execute("x^2") == "@E0: x^2"
    assert session.workspace.expressions()[0].frame == frame
    assert session.execute("diff") == "verified @E1: 2*x"

    with pytest.raises(SessionError):
        session.execute("assume")
    assert session.execute("assume x + 1") == (
        "invalid: the hypothesis is not a proposition"
    )
    # The same text in a child frame is a proposition with another meaning;
    # scope rules do not merge it by spelling.
    assert session.execute("assume x > 0") == "assumed: x > 0"
    assert session.workspace.frame != frame


def test_contradictory_assumptions_stop_the_session():
    runtime = bootstrap()
    session = Session(runtime)
    assert session.execute("assume x > 0") == "assumed: x > 0"
    consistent_frame = session.workspace.frame

    output = session.execute("assume not x > 0")
    assert output.startswith("invalid:")
    assert "contradiction" in output
    inconsistent_frame = session.workspace.frame
    assert runtime.store.consistency(
        inconsistent_frame
    ).is_inconsistent()
    assert session.execute("assume x > 0").startswith("invalid:")

    assert session.execute("x^2") == "@E0: x^2"
    before = runtime.store.stats()
    assert session.execute("diff").startswith("invalid:")
    assert runtime.store.stats() == before

    assert session.execute("undo") == "undo: empty view"
    assert session.workspace.frame == inconsistent_frame
    assert session.execute("undo") == "undo: empty view"
    assert session.workspace.frame == consistent_frame
    assert not runtime.store.consistency(
        consistent_frame
    ).is_inconsistent()
