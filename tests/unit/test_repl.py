"""REPL: line dispatch, error reporting and stopping on quit."""

from support import head_app, runtime_proposition, variable

from cas.frontend.repl import run
from cas.frontend.session import Session
from cas.language import sorts as S
from cas.language.functions import FunctionParameter
from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap_elementary
from cas.syntax import term as T
from cas.workflow.records import FunctionDefined


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
    assert output[3].endswith(
        "@E3: 1/2*sqrt(x)^-1 | condition: x > 0"
    )


def test_history_command_prints_the_session_history(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(session, ["x^2", "diff", "history"], output.append)
    assert output[-1] == "\n".join(session.history())
    assert "differentiate" in output[-1]
    assert "inputs=[@E0]" in output[-1]


def test_repl_embeds_object_references(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(
        session,
        ["expr F := x", "expr G := @F + 1", "show @G"],
        output.append,
    )
    assert output == ["@F: x", "@G: x + 1", "@G: x + 1"]
    assert session.object("G").term == session.parse("x + 1")


def test_repl_reports_a_missing_embedded_reference(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(session, ["expr G := @missing + 1", "x"], output.append)
    assert output[0].startswith("error: no object named @missing")
    assert output[1] == "@E0: x"


def test_repl_declares_and_defines_context(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(
        session,
        [
            "declare a : real",
            "define f := x + 1",
            "define f := f + 1",
        ],
        output.append,
    )
    assert output[0].startswith("declared a : real")
    assert output[1].startswith("defined f := x + 1")
    assert output[2].startswith("invalid:")
    assert session.workspace.frame != runtime.frame.id
    assert any("Declare" in line for line in session.history())
    assert any("Define" in line for line in session.history())


def test_repl_undo_and_redo_move_the_derived_focus(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(session, ["x^2", "diff"], output.append)
    assert session.focus is not None
    assert session.label_of(session.focus) == "E1"
    run(session, ["undo"], output.append)
    assert session.focus is not None
    assert session.label_of(session.focus) == "E0"
    run(session, ["redo"], output.append)
    assert session.focus is not None
    assert session.label_of(session.focus) == "E1"


def test_repl_lists_construction_relations(runtime):
    session = Session(runtime)
    output: list[str] = []
    run(session, ["relations"], output.append)
    assert output == ["no relations"]

    domain = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GE,
            variable(runtime),
            T.number(0),
        ),
    )
    true = runtime_proposition(runtime, T.TRUE)
    defined = session.workspace.define_function(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        head_app(
            runtime.signature,
            StructuralHead.POWER,
            variable(runtime),
            T.number(2),
        ),
        domain,
        "f",
    )
    assert isinstance(defined, FunctionDefined)
    representation = session.workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            variable(runtime),
            variable(runtime),
        ),
        "extension",
    )
    extended = session.workspace.extend_function(
        defined.function, representation, true, true
    )
    assert isinstance(extended, FunctionDefined)
    run(session, ["relations"], output.append)
    assert output[-1] != "no relations"
    assert "function_extension" in output[-1]
    assert f"v{defined.function.version}" in output[-1]
    assert f"v{extended.function.version}" in output[-1]
