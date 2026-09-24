"""Scripted REPL smoke coverage for the registered command surface."""

from cas.frontend.repl import REPL


def test_registered_help_and_focus_workflow(capsys):
    repl = REPL()
    repl.cmd_help("")
    out = capsys.readouterr().out
    assert "use" in out and "merge" in out and "checker" not in out

    repl.cmd_claim("A == B + C")
    repl.cmd_norm("#0")
    out = capsys.readouterr().out
    assert "# 1" in out and "committed" in out


def test_split_enters_real_branch_scopes(capsys):
    repl = REPL()
    repl.cmd_split("x > 0")
    assert repl.branch_group is not None
    assert len(repl.branch_group.cases) == 2
    repl.cmd_enter("+")
    assert repl.wf.scope == repl.branch_group.cases[0].scope
    out = capsys.readouterr().out
    assert "entered scope" in out
