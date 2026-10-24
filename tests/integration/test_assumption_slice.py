"""Assumptions scope a session while the ledger stays append-only."""

from cas.frontend.session import Session
from cas.runtime import bootstrap_elementary
from cas.workflow.records import OperationStatus


def test_an_assumption_scopes_later_operations_and_history():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    base = session.workspace.frame
    assert session.execute("assume x > 0") == "assumed: x > 0"
    child = session.workspace.frame
    assert child != base

    assert session.execute("x^2") == "@E0: x^2"
    result = session.differentiate(session.object("E0"))
    assert result.status is OperationStatus.VERIFIED
    assert result.verification is not None
    assert result.verification.specification.meaning.frame == child
    assert result.candidate is not None
    assert result.candidate.frame == child
    assert runtime.store.stats()["judgments"] == 2

    assert session.execute("undo") == "undo: @E0"
    assert session.execute("undo") == "undo: empty view"
    assert session.workspace.frame == child
    assert session.execute("undo") == "undo: empty view"
    assert session.workspace.frame == base
    assert runtime.store.stats()["judgments"] == 2

    assert session.execute("redo") == "redo: empty view"
    assert session.execute("redo") == "redo: @E0"
    assert session.execute("redo") == "redo: @E1"
    assert session.workspace.frame == child


def test_a_contradiction_is_published_before_the_session_stops():
    from cas.syntax import term as T

    runtime = bootstrap_elementary()
    session = Session(runtime)
    assert session.execute("assume x > 0") == "assumed: x > 0"
    output = session.execute("assume not x > 0")
    assert output.startswith("invalid:")
    assert runtime.store.stats()["judgments"] == 3

    frame = session.workspace.frame
    witnesses = [
        judgment
        for judgment in runtime.store.judgments_visible(frame)
        if judgment.proposition.term == T.FALSE
    ]
    assert len(witnesses) == 1
    assert runtime.store.applicability(
        witnesses[0].id, frame
    ).is_applicable()

    session.execute("x^2")
    before = runtime.store.stats()
    assert session.execute("diff").startswith("invalid:")
    assert runtime.store.stats() == before
