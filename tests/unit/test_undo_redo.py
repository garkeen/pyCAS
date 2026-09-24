# -*- coding: utf-8 -*-
"""Undo/redo: the event view, the scope version and the visible step set move
together.

The event log and the step records stay append-only; an undo only moves the
branch pointer into the log. The view then holds one operation less, the scope
pointer returns to the version that was current at the resulting revision, and
the visible step set follows the view. Redo puts the operation back, while a
new operation after an undo is performed on the shortened view and therefore
discards the redo branch.
"""

from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.syntax.term import S
from cas.workflow.command import Claim, Diff

install(bootstrap())

X = S("x")


def _two_steps():
    """A claim plus a dependent step, with the ids of both records."""
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    s1 = wf.add(parse("2*x"), Diff(pred=s0.id, var=X))
    return wf, s0, s1


# ---------------------------------------------------------------------------
# The event view
# ---------------------------------------------------------------------------

def test_undo_hides_the_last_step_but_keeps_the_records():
    wf, s0, s1 = _two_steps()
    assert [s.id for s in wf.visible_steps()] == [0, 1]
    assert wf.undo() == 1
    # the step produced by the undone event is not visible any more
    assert [s.id for s in wf.visible_steps()] == [0]
    # ... while every record still holds it: undo never deletes
    assert [s.id for s in wf.all_steps()] == [0, 1]
    assert [int(ev.id) for ev in wf.events.events()] == [0, 1]
    assert len(wf.events.visible()) == 1
    assert wf.events.current_revision() == 1
    assert wf.redo() == 2
    assert [s.id for s in wf.visible_steps()] == [0, 1]


# ---------------------------------------------------------------------------
# The scope pointer follows the revision
# ---------------------------------------------------------------------------

def test_undo_restores_the_scope_version_a_claim_created():
    wf = new_workflow()
    root = wf.scope
    wf.add(parse("x^2"), Claim())
    scopes = wf.store.scopes
    grown = wf.scope
    assert grown != root
    assert [a.proposition for a in scopes.assumptions(wf.scope)] == [parse("x^2")]
    assert wf.undo() == 0
    assert wf.scope == root
    assert scopes.assumptions(wf.scope) == ()
    assert wf.redo() == 1
    assert wf.scope == grown
    assert [a.proposition for a in scopes.assumptions(wf.scope)] == [parse("x^2")]


def test_undo_reverts_a_declaration_and_redo_re_applies_it():
    wf = new_workflow()
    root = wf.scope
    scopes = wf.store.scopes
    wf.declare(S("u"), S("Real"))
    declared = wf.scope
    # the declaration is a recorded operation, not only a scope entry
    assert [ev.command for ev in wf.events.visible()] == ["Declare"]
    assert declared != root
    assert [d.symbol for d in scopes.declarations(wf.scope)] == [S("u")]
    assert wf.undo() == 0
    assert wf.scope == root
    assert scopes.declarations(wf.scope) == ()
    assert wf.events.visible() == ()
    assert wf.redo() == 1
    assert wf.scope == declared
    assert [d.symbol for d in scopes.declarations(wf.scope)] == [S("u")]


def test_undo_reverts_a_definition_and_redo_re_applies_it():
    wf = new_workflow()
    root = wf.scope
    scopes = wf.store.scopes
    body = parse("x^2")
    wf.define(S("u"), body)
    defined = wf.scope
    assert [ev.command for ev in wf.events.visible()] == ["Define"]
    assert scopes.lookup_definition(wf.scope, S("u")) is body
    assert wf.undo() == 0
    assert wf.scope == root
    assert scopes.lookup_definition(wf.scope, S("u")) is None
    assert wf.redo() == 1
    assert wf.scope == defined
    assert scopes.lookup_definition(wf.scope, S("u")) is body


# ---------------------------------------------------------------------------
# A branch after an undo
# ---------------------------------------------------------------------------

def test_operation_after_undo_branches_and_discards_the_redo_stack():
    wf = new_workflow()
    x2, u0, v0 = parse("x^2"), parse("u > 0"), parse("v > 0")
    wf.add(x2, Claim())
    wf.add(u0, Claim())
    assert wf.undo() == 1
    wf.add(v0, Claim())
    # the view is a branch, not a prefix of the event list
    assert [int(ev.id) for ev in wf.events.visible()] == [0, 2]
    assert [s.id for s in wf.visible_steps()] == [0, 2]
    assert [s.id for s in wf.all_steps()] == [0, 1, 2]
    # the redo branch was discarded: the redo stack is empty
    assert wf.redo() == 2
    assert [int(ev.id) for ev in wf.events.visible()] == [0, 2]
    # the scope follows the new branch: the undone claim's assumption is gone,
    # the new claim's assumption is present
    props = [a.proposition for a in wf.store.scopes.assumptions(wf.scope)]
    assert props == [x2, v0]


def test_parent_revision_records_where_the_operation_was_performed():
    wf, s0, s1 = _two_steps()
    rev = wf.undo()
    assert rev == 1
    wf.add(parse("2*x"), Diff(pred=s0.id, var=X))
    ev = wf.events.events()[-1]
    assert ev.parent_revision == rev
    assert wf.events.current_revision() == rev + 1
    # the two dependent steps now occupy the same revision on different branches
    assert [int(e.id) for e in wf.events.visible()] == [0, 2]
    assert wf.events.events()[1].parent_revision == 1


# ---------------------------------------------------------------------------
# The frontend consumer
# ---------------------------------------------------------------------------

def test_repl_step_listing_and_undo_follow_the_visible_view(capsys):
    from cas.frontend.repl import REPL
    r = REPL()
    r.cmd_claim("x^2")
    r.cmd_claim("y^2")
    assert [s.id for s in r.wf.visible_steps()] == [0, 1]
    r.cmd_undo(None)
    assert r.wf.events.current_revision() == 1
    assert [s.id for s in r.wf.visible_steps()] == [0]
    assert r.focus == 0
    # the listing is the visible view: the undone step is not printed
    capsys.readouterr()
    r.cmd_steps(None)
    shown = capsys.readouterr().out
    assert "# 0" in shown
    assert "# 1" not in shown
    # the REPL keeps one step visible, so its focus stays usable
    r.cmd_undo(None)
    assert [s.id for s in r.wf.visible_steps()] == [0]
    assert r.focus == 0
