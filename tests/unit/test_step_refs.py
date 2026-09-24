"""Step references and session focus."""

from cas.frontend.parser import parse
from cas.frontend.repl import REPL, _take_refs
from cas.runtime import Runtime, new_workflow
from cas.syntax.term import S
from cas.workflow.command import Claim, Diff


def test_reference_tokens_are_split_off_the_arguments() -> None:
    assert _take_refs("add 1 #2") == ("add 1", (2,))
    assert _take_refs("x = 2") == ("x = 2", ())
    assert _take_refs("#0 #1") == ("", (0, 1))


def test_kernel_step_records_every_referenced_step(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    first = workflow.add(parse(runtime, "x^2"), Claim())
    second = workflow.add(parse(runtime, "y^2"), Claim())
    step = workflow.add(
        parse(runtime, "2*x"),
        Diff(premises=(first.id, second.id), var=S("x")),
    )
    assert step.status == "committed", step.note
    assert step.command.premises == (first.id, second.id)
    assert len(workflow.store.all_steps()[-1].premises) == 2


def test_explicit_reference_overrides_the_focus(
    runtime: Runtime,
    capsys,
) -> None:
    repl = REPL(runtime)
    repl.cmd_claim("x^2")
    repl.cmd_claim("y^2")
    repl.cmd_norm("#0")
    assert repl.session.focus == 2
    assert repl.session.workflow.get(2).command.premises == (0,)
    assert repl.session.workflow.get(2).content is parse(runtime, "x^2")


def test_focus_can_be_moved_and_shown(runtime: Runtime, capsys) -> None:
    repl = REPL(runtime)
    repl.cmd_claim("x^2")
    repl.cmd_claim("y^2")
    capsys.readouterr()
    repl.cmd_focus("#0")
    assert repl.session.focus == 0
    repl.cmd_show("#1")
    assert "# 1" in capsys.readouterr().out


def test_check_finds_the_problem_through_the_premise_graph(
    runtime: Runtime,
    capsys,
) -> None:
    repl = REPL(runtime)
    repl.cmd_claim("2*x + 3 == 7")
    repl.cmd_solve("x")
    capsys.readouterr()
    repl.cmd_check(None)
    output = capsys.readouterr().out
    assert "2*x + 3 == 7" in output
    assert "VERIFIED" in output


def test_focus_follows_undo(runtime: Runtime) -> None:
    repl = REPL(runtime)
    repl.cmd_claim("x^2")
    repl.cmd_claim("y^2")
    repl.cmd_undo(None)
    assert repl.session.focus == 0
