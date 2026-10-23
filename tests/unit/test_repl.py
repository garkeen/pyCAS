"""REPL: line dispatch, error reporting and stopping on quit."""

from cas.frontend.repl import run
from cas.frontend.session import Session


def test_run_executes_and_stops_at_quit(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(session, ["x^2", "diff", "quit", "x^3"], output.append)
    assert output == ["@E0: x^2", "verified @E1: 2*x", "bye"]
    assert session.closed
    # the line after quit never ran; the view holds the source and its result
    assert len(session.workspace.expressions()) == 2


def test_frontend_errors_are_reported_and_the_next_line_runs(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(session, ["x +", "x"], output.append)
    assert output[0].startswith("error: expected an expression")
    assert output[1] == "@E0: x"


def test_honest_refusal_is_a_result_not_a_frontend_error(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(session, ["1/x", "diff"], output.append)
    assert output[1].startswith("unsupported:")
    assert not any(line.startswith("error:") for line in output)
