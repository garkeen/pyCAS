# -*- coding: utf-8 -*-
"""Step references: a step names the results it used.

`#N` names a *result*: its content is what a computation reads, its judgment is
what a verified step may depend on. The kernel records the referenced steps as
premises — a tuple, so a two-premise rule is expressible — while the focus is
only the default for a command that names nothing. `check` derives the equation a
solution answers from the premise graph instead of a cached pointer.
"""

from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.frontend.repl import REPL, _take_refs
from cas.syntax.term import S
from cas.workflow.command import Claim, Diff

install(bootstrap())


def test_reference_tokens_are_split_off_the_arguments():
    assert _take_refs("add 1 #2") == ("add 1", (2,))
    assert _take_refs("x = 2") == ("x = 2", ())
    assert _take_refs("#0 #1") == ("", (0, 1))


def test_kernel_step_records_every_referenced_step():
    wf = new_workflow()
    a = wf.add(parse("x^2"), Claim())
    b = wf.add(parse("y^2"), Claim())
    s = wf.add(parse("2*x"), Diff(premises=(a.id, b.id), var=S("x")))
    assert s.status == "committed", s.note
    # the command carries the references and the kernel records them as premises
    assert s.command.premises == (a.id, b.id)
    assert len(wf.store.all_steps()[-1].premises) == 2


def test_explicit_reference_overrides_the_focus(capsys):
    r = REPL()
    r.cmd_claim("x^2")          # #0
    r.cmd_claim("y^2")          # #1, and the focus
    r.cmd_norm("#0")
    assert r.focus == 2
    assert r.wf.get(2).command.premises == (0,)
    assert r.wf.get(2).content is parse("x^2")


def test_focus_can_be_moved_and_shown(capsys):
    r = REPL()
    r.cmd_claim("x^2")
    r.cmd_claim("y^2")
    capsys.readouterr()
    r.cmd_focus("#0")
    assert r.focus == 0
    r.cmd_show("#1")
    assert "# 1" in capsys.readouterr().out


def test_check_finds_the_problem_through_the_premise_graph(capsys):
    r = REPL()
    r.cmd_claim("2*x + 3 == 7")     # #0
    r.cmd_solve("x")                # #1: x == 2 (premise #0)
    capsys.readouterr()
    r.cmd_check(None)               # default target: the focus
    out = capsys.readouterr().out
    assert "2*x + 3 == 7" in out
    assert "VERIFIED" in out


def test_focus_follows_undo(capsys):
    r = REPL()
    r.cmd_claim("x^2")
    r.cmd_claim("y^2")
    r.cmd_undo(None)
    assert r.focus == 0
