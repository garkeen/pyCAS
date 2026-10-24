"""REPL: line dispatch, error reporting and stopping on quit."""

from cas.frontend.repl import run
from cas.frontend.session import Session
from cas.runtime import bootstrap_elementary


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


def test_the_repl_runs_the_elementary_runtime():
    session = Session(bootstrap_elementary())
    output: list[str] = []
    run(
        session,
        ["sin(x)", "diff", "sqrt(x)", "diff"],
        output.append,
    )
    assert output[0] == "@E0: sin(x)"
    assert output[1] == "verified @E1: cos(x)"
    assert output[2] == "@E2: sqrt(x)"
    assert output[3].startswith("verified on x > 0 ")
    assert output[3].endswith("@E3: 1/2*sqrt(x)^-1")
