from cas.frontend.repl import REPL
from cas.runtime import Runtime


def test_registered_help_and_focus_workflow(runtime: Runtime, capsys) -> None:
    repl = REPL(runtime)
    repl.cmd_help("")
    output = capsys.readouterr().out
    assert "use" in output and "merge" in output and "checker" not in output
    repl.cmd_claim("A == B + C")
    repl.cmd_norm("#0")
    output = capsys.readouterr().out
    assert "# 1" in output and "committed" in output


def test_split_enters_real_branch_scopes(runtime: Runtime, capsys) -> None:
    repl = REPL(runtime)
    repl.cmd_split("x > 0")
    assert repl.session.branch_group is not None
    assert len(repl.session.branch_group.cases) == 2
    repl.cmd_enter("+")
    assert repl.session.workflow.scope == repl.session.branch_group.cases[0].scope
    assert "entered scope" in capsys.readouterr().out


def test_registered_calculus_commands_execute(runtime: Runtime, capsys) -> None:
    repl = REPL(runtime)
    repl.cmd_claim("x^2")
    repl.cmd_diff("x")
    assert "2*x" in capsys.readouterr().out
    repl.cmd_claim("x^2")
    repl.cmd_integrate("x")
    assert "x^3/3" in capsys.readouterr().out
