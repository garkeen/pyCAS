"""Session commands: labels, focus, differentiation, history and refusals."""

import pytest

from cas.frontend.errors import ParseError, SessionError
from cas.frontend.session import Session


def new_session(runtime) -> Session:
    return Session(runtime)


def labels(session: Session) -> list[str]:
    return [label for label, _ in session.visible()]


def test_a_new_session_is_empty(runtime):
    session = new_session(runtime)
    assert session.focus is None
    assert session.visible() == ()
    assert session.execute("") == ""
    assert session.execute("list") == "no expressions"
    assert not session.closed


def test_entering_an_expression_labels_it_without_trusting_it(runtime):
    session = new_session(runtime)
    assert session.execute("x + 1") == "@E0: x + 1"
    assert session.focus is not None
    assert session.label_of(session.focus) == "E0"
    assert labels(session) == ["E0"]
    assert runtime.store.stats()["judgments"] == 0


def test_auto_labels_increase_and_explicit_labels_are_kept(runtime):
    session = new_session(runtime)
    assert session.execute("x") == "@E0: x"
    assert session.execute("expr F := x^2") == "@F: x^2"
    assert session.execute("expr G:= x^3") == "@G: x^3"
    assert labels(session) == ["E0", "F", "G"]
    assert session.execute("expr := x + 1") == "@E1: x + 1"


def test_labels_must_be_unique_and_well_formed(runtime):
    session = new_session(runtime)
    session.intake("x", "F")
    with pytest.raises(SessionError):
        session.intake("y", "F")
    assert len(session.workspace.expressions()) == 1
    with pytest.raises(SessionError):
        session.intake("y", "1bad")
    assert len(session.workspace.expressions()) == 1


def test_parse_errors_do_not_change_the_workspace(runtime):
    session = new_session(runtime)
    with pytest.raises(ParseError):
        session.execute("x +")
    assert session.workspace.expressions() == ()
    assert session.workspace.events() == ()


def test_show_uses_the_focus_or_a_named_object(runtime):
    session = new_session(runtime)
    with pytest.raises(SessionError):
        session.execute("show")
    session.execute("x + 1")
    assert session.execute("show") == "@E0: x + 1"
    assert session.execute("show @E0") == "@E0: x + 1"
    with pytest.raises(SessionError):
        session.execute("show @missing")


def test_differentiation_verifies_and_moves_the_focus(runtime):
    session = new_session(runtime)
    assert session.execute("x^3 - 3*x") == "@E0: x^3 - 3*x"
    assert session.execute("diff") == "verified @E1: -3 + 3*x^2"
    assert session.focus is not None
    assert session.label_of(session.focus) == "E1"
    assert runtime.store.stats()["judgments"] == 1
    assert len(session.workspace.links()) == 1
    assert session.execute("diff") == "verified @E2: 6*x"
    assert runtime.store.stats()["judgments"] == 2


def test_diff_accepts_an_explicit_object_reference(runtime):
    session = new_session(runtime)
    session.execute("expr F := x^2")
    session.execute("x")
    assert session.execute("diff @F") == "verified @E1: 2*x"
    assert session.label_of(session.focus) == "E1"


def test_diff_needs_a_focus(runtime):
    session = new_session(runtime)
    with pytest.raises(SessionError):
        session.execute("diff")


def test_outside_the_fragment_the_session_refuses_honestly(runtime):
    session = new_session(runtime)
    session.execute("1/x")
    assert session.execute("diff") == (
        "unsupported: the source is outside the polynomial fragment"
    )
    assert session.label_of(session.focus) == "E0"
    assert runtime.store.stats()["judgments"] == 0
    assert session.execute("list") == "> @E0: x^-1"


def test_undo_and_redo_move_the_view_and_keep_the_ledger(runtime):
    session = new_session(runtime)
    session.execute("x^3")
    session.execute("diff")
    assert runtime.store.stats()["judgments"] == 1

    assert session.execute("undo") == "undo: @E0"
    assert labels(session) == ["E0"]
    assert session.label_of(session.focus) == "E0"
    assert runtime.store.stats()["judgments"] == 1

    assert session.execute("undo") == "undo: empty view"
    assert session.focus is None
    assert session.execute("undo") == "undo: at the beginning"

    assert session.execute("redo") == "redo: @E0"
    assert session.execute("redo") == "redo: @E1"
    assert session.execute("redo") == "redo: at the end"
    assert session.label_of(session.focus) == "E1"


def test_a_hidden_object_cannot_be_referenced(runtime):
    session = new_session(runtime)
    session.execute("x^3")
    session.execute("diff")
    session.execute("undo")
    with pytest.raises(SessionError) as caught:
        session.execute("show @E1")
    assert "not visible" in str(caught.value)


def test_a_new_operation_after_undo_truncates_redo(runtime):
    session = new_session(runtime)
    session.execute("x^3")
    session.execute("diff")
    session.execute("undo")
    assert session.execute("x^2") == "@E2: x^2"
    assert labels(session) == ["E0", "E2"]
    assert session.execute("redo") == "redo: at the end"
    assert runtime.store.stats()["judgments"] == 1
    with pytest.raises(SessionError):
        session.execute("show @E1")


def test_unknown_names_are_stored_but_refused_by_differentiation(runtime):
    session = new_session(runtime)
    session.execute("u")
    assert session.execute("diff").startswith("invalid:")
    assert runtime.store.stats()["judgments"] == 0


def test_command_usage_errors(runtime):
    session = new_session(runtime)
    with pytest.raises(SessionError):
        session.execute("list extra")
    with pytest.raises(SessionError):
        session.execute("undo extra")
    with pytest.raises(SessionError):
        session.execute("show x")
    with pytest.raises(SessionError):
        session.execute("expr F")


def test_help_and_quit(runtime):
    session = new_session(runtime)
    help_text = session.execute("help")
    assert "diff" in help_text
    assert "undo" in help_text
    assert session.execute("quit") == "bye"
    assert session.closed
