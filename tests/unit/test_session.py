"""Session commands: labels, focus, differentiation, history and refusals."""

from dataclasses import replace

import pytest
from support import head_app, runtime_proposition, variable

from cas.frontend.errors import ParseError, SessionError
from cas.frontend.pprint import to_str
from cas.frontend.repl import run
from cas.frontend.session import Session
from cas.kernel.commit import Deferred
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.execution import ExecutionBudget
from cas.language.functions import FunctionParameter
from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap_elementary
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.workflow.records import (
    CandidateFocus,
    FunctionDefined,
    ObjectFocus,
    OperationStatus,
    RewriteRelation,
    TaskFocus,
)


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


def test_embedded_object_references_use_the_visible_snapshot(runtime):
    session = new_session(runtime)
    session.execute("expr F := x")
    assert session.execute("expr G := @F + 1") == "@G: x + 1"
    assert session.object("G").term == session.parse("x + 1")
    assert runtime.store.stats()["judgments"] == 0
    # The object label is not a mathematical name, and the reference spelling
    # never enters the symbol table.
    assert runtime.table.lookup("F") is None
    assert runtime.table.lookup("@F") is None


def test_embedded_references_are_structural_and_do_not_capture_names(runtime):
    session = new_session(runtime)
    session.execute("expr x := y")
    session.execute("expr F := x + 1")
    parsed = session.parse("@F*(@x + x)")
    assert parsed == session.parse("(x + 1)*(y + x)")
    assert runtime.table.lookup("x") == runtime.variable
    assert session.object("x").term == session.parse("y")
    y_symbol = runtime.table.lookup("y")
    assert y_symbol is not None
    assert B.free_symbols(parsed) == B.free_symbols(
        session.parse("(x + 1)*(y + x)")
    )


def test_a_user_name_that_looks_like_a_placeholder_stays_a_symbol(runtime):
    session = new_session(runtime)
    session.execute("expr F := x")
    lookalike = "__pycas_object_reference_0__"
    parsed = session.parse(f"{lookalike} + @F")
    symbol = runtime.table.lookup(lookalike)
    assert symbol is not None
    assert parsed == session.parse(f"{lookalike} + x")


def test_an_embedded_reference_to_a_missing_label_is_refused(runtime):
    session = new_session(runtime)
    symbols_before = len(runtime.table)
    with pytest.raises(SessionError) as caught:
        session.execute("expr G := @missing + 1")
    assert "no object named @missing" in str(caught.value)
    assert session.workspace.expressions() == ()
    assert session.history() == ()
    assert len(runtime.table) == symbols_before
    assert runtime.table.lookup("G") is None
    assert runtime.table.lookup("missing") is None


def test_an_embedded_reference_to_a_hidden_label_is_refused(runtime):
    session = new_session(runtime)
    session.execute("expr F := x")
    session.execute("expr G := y")
    session.execute("undo")
    symbols_before = len(runtime.table)
    with pytest.raises(SessionError) as caught:
        session.execute("expr H := @G + 1")
    assert "not visible" in str(caught.value)
    assert labels(session) == ["F"]
    assert len(runtime.table) == symbols_before
    assert runtime.table.lookup("H") is None


def test_an_embedded_reference_inside_quote_is_refused(runtime):
    session = new_session(runtime)
    session.execute("expr F := x")
    with pytest.raises(SessionError) as caught:
        session.parse("quote(@F)")
    assert "quote" in str(caught.value)


def test_adjacent_object_references_are_parse_errors(runtime):
    session = new_session(runtime)
    session.execute("expr F := x")
    with pytest.raises(ParseError):
        session.parse("@F@F")
    with pytest.raises(ParseError):
        session.parse("y@F")


def test_show_uses_the_focus_or_a_named_object(runtime):
    session = new_session(runtime)
    with pytest.raises(SessionError):
        session.execute("show")
    session.execute("x + 1")
    assert session.execute("show") == "@E0: x + 1"
    assert session.execute("show @E0") == "@E0: x + 1"
    with pytest.raises(SessionError):
        session.execute("show @missing")


def test_object_reports_the_artifact_kind_and_source_operation(runtime):
    session = new_session(runtime)
    session.execute("x + 1")
    focus = session.focus_ref
    revision = session.workspace.revision.id
    expressions = session.workspace.expressions()
    assert session.execute("object @E0") == (
        "@E0: x + 1 [artifact=term; operation=Intake]"
    )
    assert session.execute("show @E0") == "@E0: x + 1"
    assert session.focus_ref == focus
    assert session.workspace.revision.id == revision
    assert session.workspace.expressions() == expressions
    with pytest.raises(SessionError):
        session.execute("object E0")


def test_object_reports_a_function_artifact(runtime):
    session = new_session(runtime)
    domain = runtime_proposition(runtime, T.TRUE)
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
    focus = session.focus_ref
    revision = session.workspace.revision.id
    expressions = session.workspace.expressions()
    functions = session.workspace.functions()
    assert session.execute("object @f") == (
        "@f: x^2 [artifact=function; operation=DefineFunction]"
    )
    assert session.focus_ref == focus
    assert session.workspace.revision.id == revision
    assert session.workspace.expressions() == expressions
    assert session.workspace.functions() == functions
    assert session.execute("undo").startswith("undo: ")
    with pytest.raises(SessionError):
        session.execute("object @f")


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
        " | missing: derivative_rule"
    )
    assert session.label_of(session.focus) == "E0"
    assert runtime.store.stats()["judgments"] == 0
    assert session.execute("list") == "> @E0: x^-1"


def test_undo_and_redo_move_the_view_and_keep_the_ledger(runtime):
    session = new_session(runtime)
    session.execute("x^3")
    session.execute("diff")
    assert runtime.store.stats()["judgments"] == 1

    assert session.execute("undo") == "undo: @E0 (intake 0)"
    assert labels(session) == ["E0"]
    assert session.label_of(session.focus) == "E0"
    assert runtime.store.stats()["judgments"] == 1

    assert session.execute("undo") == "undo: empty view (start)"
    assert session.focus is None
    assert session.execute("undo") == "undo: at the beginning"

    assert session.execute("redo") == "redo: @E0 (intake 0)"
    assert session.execute("redo") == "redo: @E1 (differentiate 0)"
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


def test_candidates_check_and_edit_commands(runtime):
    session = new_session(runtime)
    session.execute("x^3 - 3*x")
    assert session.execute("diff").startswith("verified")
    listed = session.execute("candidates")
    assert "C0:" in listed
    assert (
        "[state=verified; applicability=applicable; "
        "coverage=complete; language=satisfies]" in listed
    )
    assert session.execute("check 0").startswith("verified")
    assert session.execute("edit 0 = x").startswith("edited C1:")
    assert session.execute("check 1").startswith("invalid:")
    listed = session.execute("candidates")
    assert "C1:" in listed
    assert (
        "[state=unchecked; applicability=applicable; "
        "coverage=unclaimed; language=satisfies]" in listed
    )


def test_decide_on_an_unchecked_edited_candidate_is_a_session_error(runtime):
    session = new_session(runtime)
    session.execute("expr A := x^3")
    assert session.execute("diff @A").startswith("verified")
    assert session.execute("edit C0 = 2*x").startswith("edited C1:")
    with pytest.raises(SessionError) as caught:
        session.execute("decide C1")
    assert "no certificate" in str(caught.value)
    assert "unchecked" in str(caught.value)


def test_decide_on_an_unknown_candidate_is_a_session_error(runtime):
    session = new_session(runtime)
    with pytest.raises(SessionError) as caught:
        session.execute("decide C9")
    assert "not visible" in str(caught.value)


def test_the_repl_survives_decide_on_an_uncheckable_candidate(runtime):
    session = new_session(runtime)
    session.execute("expr A := x^3")
    session.execute("diff @A")
    session.execute("edit C0 = 2*x")
    outputs: list[str] = []
    run(session, ("decide C1", "expr B := x"), outputs.append)
    assert outputs[0].startswith("error:")
    assert "certificate" in outputs[0]
    assert outputs[1] == "@B: x"
    assert not session.closed
    assert session.label_of(session.focus) == "B"


def test_candidates_displays_solve_coverage_and_out_of_scope_edit(runtime):
    session = new_session(runtime)
    session.execute("2*x + 4")
    assert session.execute("solve").startswith("verified")
    listed = session.execute("candidates")
    assert listed.startswith("C0: ")
    assert (
        "[state=verified; applicability=applicable; "
        "coverage=complete; language=satisfies]" in listed
    )
    assert session.execute("edit 0 = 7").startswith("edited C1:")
    listed = session.execute("candidates")
    assert "C1: 7" in listed
    assert (
        "[state=unchecked; applicability=out_of_scope; "
        "coverage=unclaimed; language=does_not_satisfy]" in listed
    )


def test_candidates_displays_a_blocked_applicability(runtime, monkeypatch):
    session = new_session(runtime)
    session.execute("x^3 - 3*x")
    assert session.execute("diff").startswith("verified")
    monkeypatch.setattr(
        session.workspace,
        "_commit",
        lambda proposal: Deferred(
            Reason.FRAGMENT, "the checker is unavailable"
        ),
    )
    assert session.execute("check 0").startswith("unsupported:")
    listed = session.execute("candidates")
    assert "state=unverified" in listed
    assert "applicability=blocked" in listed
    assert "coverage=complete" in listed
    assert "language=satisfies" in listed


def test_a_conditional_diff_reports_its_verification_condition():
    session = new_session(bootstrap_elementary())
    session.execute("sqrt(x)")
    output = session.execute("diff")
    assert "condition:" in output
    assert "x > 0" in output


def test_report_displays_a_link_condition_without_a_blocker():
    runtime = bootstrap_elementary()
    session = new_session(runtime)
    source = session.intake("sqrt(x)")
    requested = runtime_proposition(runtime, session.parse("x > 2"))
    result = session.workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=requested,
    )
    assert result.status is OperationStatus.CONDITIONAL
    assert result.blocker is None
    assert result.verifications
    condition = result.verifications[0].condition
    assert condition is not None
    assert condition.term == requested.term
    output = session._report(result)
    assert output.startswith("conditional")
    assert "condition:" in output
    assert "x > 2" in output


def test_report_displays_the_blocker_target_and_budget(runtime):
    session = new_session(runtime)
    source = session.intake("1/x")
    region = runtime_proposition(runtime, session.parse("x > 0"))
    budget = ExecutionBudget(max_nodes=9, max_depth=3)
    result = session.workspace.apply(
        "differentiate",
        (source,),
        target=runtime.variable,
        region=region,
        budget=budget,
    )
    assert result.blocker is not None
    output = session._report(result)
    assert output.startswith("unsupported:")
    assert "target: x > 0" in output
    assert "budget: max_nodes=9, max_depth=3" in output


def test_help_and_quit(runtime):
    session = new_session(runtime)
    help_text = session.execute("help")
    assert "diff" in help_text
    assert "isolate_roots" in help_text
    assert "undo" in help_text
    assert session.execute("quit") == "bye"
    assert session.closed


def test_history_shows_operations_inputs_reports_and_revisions(runtime):
    session = new_session(runtime)
    session.execute("expr F := x^3 - 3*x")
    session.execute("diff")
    lines = session.history()
    assert len(lines) == 2
    assert "Intake" in lines[0]
    assert "inputs=[]" in lines[0]
    assert "status=none" in lines[0]
    assert "differentiate" in lines[1]
    assert "inputs=[@F]" in lines[1]
    assert "parameters=[]" in lines[1]
    assert "status=verified" in lines[1]
    assert f"-> R{session.workspace.revision.id}" in lines[1]
    assert session.execute("history") == "\n".join(lines)


def test_history_shows_the_frame_content_digest(runtime):
    session = new_session(runtime)
    session.execute("x")
    digest = runtime.frames.digest(runtime.frame.id)
    assert session.workspace.revision.frame_digest == digest
    assert session.workspace.events()[0].frame_digest == digest
    assert f"digest={digest[:12]}" in session.history()[0]


def test_history_follows_undo_and_redo(runtime):
    session = new_session(runtime)
    session.execute("x^3")
    session.execute("diff")
    full = session.history()
    assert len(full) == 2
    assert session.execute("undo").startswith("undo: ")
    assert session.history() == (full[0],)
    assert session.execute("history") == full[0]
    assert session.execute("redo").startswith("redo: ")
    assert session.history() == full


def test_history_is_empty_before_any_event(runtime):
    session = new_session(runtime)
    assert session.history() == ()
    assert session.execute("history") == "no history"
    with pytest.raises(SessionError):
        session.execute("history extra")


def test_declare_command_creates_a_child_frame(runtime):
    session = new_session(runtime)
    output = session.execute("declare a : real")
    assert output.startswith("declared a : real")
    assert f"F{session.workspace.frame}" in output
    assert session.workspace.frame != runtime.frame.id
    symbol = runtime.table.lookup("a")
    assert symbol is not None
    assert runtime.frames.sort_of(session.workspace.frame, symbol) is S.REAL
    assert session.execute("a + 1") == "@E0: a + 1"
    assert session.workspace.expressions()[0].frame == session.workspace.frame

    lines = session.history()
    assert len(lines) == 2
    assert "Declare" in lines[0]
    assert "status=verified" in lines[0]
    assert "Intake" in lines[1]


def test_declare_accepts_every_advertised_sort(runtime):
    session = new_session(runtime)
    expected = {
        "integer": S.INTEGER,
        "rational": S.RATIONAL,
        "real": S.REAL,
        "complex": S.COMPLEX,
        "proposition": S.PROPOSITION,
        "scalar": S.UNKNOWN_SCALAR,
    }
    for name, sort in expected.items():
        assert session.execute(f"declare {name} : {name}").startswith(
            f"declared {name} : {name}"
        )
        symbol = runtime.table.lookup(name)
        assert symbol is not None
        assert runtime.frames.sort_of(session.workspace.frame, symbol) is sort


def test_declare_refuses_an_unknown_sort_and_malformed_forms(runtime):
    session = new_session(runtime)
    with pytest.raises(SessionError) as caught:
        session.execute("declare a : nonsense")
    message = str(caught.value)
    for name in (
        "integer",
        "rational",
        "real",
        "complex",
        "proposition",
        "scalar",
    ):
        assert name in message

    for line in (
        "declare a",
        "declare a : real : integer",
        "declare a b : real",
    ):
        with pytest.raises(SessionError):
            session.execute(line)
    assert session.workspace.frame == runtime.frame.id
    assert session.history() == ()


def test_define_command_creates_a_child_frame_and_expands_the_alias(runtime):
    session = new_session(runtime)
    output = session.execute("define f := x + 1")
    assert output.startswith("defined f := x + 1")
    assert f"F{session.workspace.frame}" in output
    assert session.workspace.frame != runtime.frame.id

    lines = session.history()
    assert len(lines) == 1
    assert "Define" in lines[0]
    assert "status=verified" in lines[0]

    assert session.execute("f") == "@E0: f"
    assert session.execute("diff") == "verified @E1: 1"


def test_define_refuses_self_reference_and_redefinition(runtime):
    session = new_session(runtime)
    output = session.execute("define f := f + 1")
    assert output.startswith("invalid:")
    assert session.workspace.frame == runtime.frame.id
    assert session.history() == ()

    assert session.execute("define f := x + 1").startswith("defined")
    frame = session.workspace.frame
    output = session.execute("define f := f + 1")
    assert output.startswith("invalid:")
    assert session.workspace.frame == frame
    assert len(session.history()) == 1


def test_session_focus_comes_from_the_visible_revision(runtime):
    session = new_session(runtime)
    expression = session.intake("x^2")
    assert session.workspace.revision.focus == ObjectFocus(expression.version)
    assert session.focus == expression


def test_a_task_focus_has_no_expression_source(runtime):
    session = new_session(runtime)
    source = session.intake("x")
    task = session.workspace.define_problem(
        "differentiate", (source,), target=runtime.variable
    )
    assert session.focus_ref == TaskFocus(task.id)
    assert session.focus is None
    with pytest.raises(SessionError):
        session.execute("diff")
    assert session.execute("diff @E0").startswith("verified")


def test_a_candidate_focus_has_no_expression_source(runtime):
    session = new_session(runtime)
    session.execute("x")
    assert session.execute("diff").startswith("verified")
    assert session.execute("edit 0 = x").startswith("edited C1:")
    edited = session.workspace.candidates()[-1]
    assert session.focus_ref == CandidateFocus(edited.id)
    assert session.focus is None
    with pytest.raises(SessionError):
        session.execute("show")
    assert session.execute("show @E0") == "@E0: x"


def test_undo_and_redo_restore_each_revisions_focus(runtime):
    session = new_session(runtime)
    source = session.intake("x")
    task = session.workspace.define_problem(
        "differentiate", (source,), target=runtime.variable
    )
    assert session.focus_ref == TaskFocus(task.id)
    assert session.focus is None
    assert session.execute("undo").startswith("undo: ")
    assert session.focus == source
    assert session.workspace.revision.focus == ObjectFocus(source.version)
    assert session.execute("redo").startswith("redo: ")
    assert session.focus is None
    assert session.focus_ref == TaskFocus(task.id)


def test_history_includes_the_focus_kind(runtime):
    session = new_session(runtime)
    session.execute("x")
    assert "focus=object:@E0" in session.history()[0]
    source = session.object("E0")
    task = session.workspace.define_problem(
        "differentiate", (source,), target=runtime.variable
    )
    assert f"focus=task:t{task.id}" in session.history()[-1]
    assert session.execute("diff @E0").startswith("verified")
    assert "focus=object:@E1" in session.history()[-1]
    assert session.execute("edit 0 = x").startswith("edited C1:")
    edited = session.workspace.candidates()[-1]
    assert f"focus=candidate:c{edited.id}" in session.history()[-1]


def test_history_shows_an_occurrence_focus(runtime):
    session = new_session(runtime)
    source = session.intake("x + 1")
    replacement = session.intake("x^2")
    found = session.workspace.occurrences(source, session.parse("x"))
    assert len(found) == 1
    result = session.workspace.rewrite(
        source, found[0], replacement, RewriteRelation.EQUIVALENT
    )
    assert result.result is not None
    path = ".".join(str(index) for index in found[0].path)
    assert (
        f"focus=occurrence:v{result.result.version}/{path}"
        in session.history()[-1]
    )


def test_visible_names_workspace_objects_without_a_session_label(runtime):
    session = new_session(runtime)
    expression = session.workspace.intake(session.parse("x"))
    assert session.visible() == ((f"v{expression.version}", expression),)
    assert (
        session.execute("list")
        == f"> @v{expression.version}: x"
    )


def test_a_revision_without_focus_has_no_implicit_expression(runtime):
    session = new_session(runtime)
    session.execute("x")
    workspace = session.workspace
    event = workspace._record_event("Checkpoint")
    workspace._append_revision("checkpoint", event, focus=None)
    assert workspace.revision.focus is None
    assert session.focus is None
    with pytest.raises(SessionError):
        session.execute("diff")
    assert session.execute("diff @E0").startswith("verified")


def test_relations_command_lists_visible_construction_relations(runtime):
    session = new_session(runtime)
    assert session.execute("relations") == "no relations"
    assert "relations" in session.execute("help")
    old, new = _extend_session_function(session)
    relation = session.workspace.construction_relations()[0]
    before_focus = session.focus_ref
    before_revision = session.workspace.revision.id
    before_expressions = session.workspace.expressions()
    output = session.execute("relations")
    assert output != "no relations"
    assert relation.kind in output
    assert f"v{old.version}" in output
    assert f"v{new.version}" in output
    assert to_str(relation.specification.term, runtime.signature) in output
    assert session.focus_ref == before_focus
    assert session.workspace.revision.id == before_revision
    assert session.workspace.expressions() == before_expressions
    with pytest.raises(SessionError):
        session.execute("relations extra")


def _extend_session_function(session):
    runtime = session.runtime
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
    return defined.function, extended.function


def _conditional_without_region(session, runtime, result):
    condition = runtime_proposition(runtime, session.parse("x > 0"))
    link = replace(result.verifications[0], condition=condition)
    return replace(
        result,
        status=OperationStatus.CONDITIONAL,
        region=None,
        verifications=(link,),
    )


def test_a_conditional_diff_without_a_region_reports_its_condition(
    runtime, monkeypatch
):
    session = new_session(runtime)
    source = session.intake("x^2")
    real = session.workspace.differentiate(source, runtime.variable)
    assert real.status is OperationStatus.VERIFIED
    conditional = _conditional_without_region(session, runtime, real)
    monkeypatch.setattr(
        session.workspace,
        "differentiate",
        lambda source, variable: conditional,
    )
    output = session.execute("diff")
    assert output.startswith("conditional")
    assert "condition:" in output
    assert "x > 0" in output


@pytest.mark.parametrize(
    ("command", "method", "sources"),
    [
        ("solve", "solve_linear", ("2*x + 4",)),
        ("gcd", "gcd", ("x^2 - 1", "x - 1")),
        ("resultant", "resultant", ("x^2 - 1", "x - 1")),
    ],
)
def test_conditional_commands_show_their_condition(
    runtime, monkeypatch, command, method, sources
):
    session = new_session(runtime)
    expressions = tuple(session.intake(text) for text in sources)
    real = getattr(session.workspace, method)(
        *expressions, runtime.variable
    )
    assert real.status is OperationStatus.VERIFIED
    conditional = _conditional_without_region(session, runtime, real)
    monkeypatch.setattr(
        session.workspace, method, lambda *args, **kwargs: conditional
    )
    argument = " ".join(
        "@" + session.label_of(expression) for expression in expressions
    )
    output = session.execute(f"{command} {argument}")
    assert output.startswith("conditional")
    assert "condition:" in output
    assert "x > 0" in output
