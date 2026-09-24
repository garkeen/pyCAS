"""Undo/redo event view and scope pointer."""

from cas.frontend.parser import parse
from cas.frontend.repl import REPL
from cas.runtime import Runtime, new_workflow
from cas.syntax.term import S
from cas.workflow.command import Claim, Diff

X = S("x")


def _two_steps(runtime: Runtime):
    workflow = new_workflow(runtime)
    first = workflow.add(parse(runtime, "x^2"), Claim())
    second = workflow.add(parse(runtime, "2*x"), Diff(pred=first.id, var=X))
    return workflow, first, second


def test_undo_hides_last_step_but_keeps_records(runtime: Runtime) -> None:
    workflow, _first, _second = _two_steps(runtime)
    assert [step.id for step in workflow.visible_steps()] == [0, 1]
    assert workflow.undo() == 1
    assert [step.id for step in workflow.visible_steps()] == [0]
    assert [step.id for step in workflow.all_steps()] == [0, 1]
    assert [int(event.id) for event in workflow.events.events()] == [0, 1]
    assert len(workflow.events.visible()) == 1
    assert workflow.events.current_revision() == 1
    assert workflow.redo() == 2
    assert [step.id for step in workflow.visible_steps()] == [0, 1]


def test_undo_restores_scope_version(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    root = workflow.scope
    workflow.add(parse(runtime, "x^2"), Claim())
    scopes = workflow.store.scopes
    grown = workflow.scope
    assert grown != root
    assert [item.proposition for item in scopes.assumptions(workflow.scope)] == [
        parse(runtime, "x^2")
    ]
    assert workflow.undo() == 0
    assert workflow.scope == root
    assert scopes.assumptions(workflow.scope) == ()
    assert workflow.redo() == 1
    assert workflow.scope == grown
    assert [item.proposition for item in scopes.assumptions(workflow.scope)] == [
        parse(runtime, "x^2")
    ]


def test_undo_reverts_declaration(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    root = workflow.scope
    scopes = workflow.store.scopes
    workflow.declare(S("u"), S("Real"))
    declared = workflow.scope
    assert [event.command for event in workflow.events.visible()] == ["Declare"]
    assert declared != root
    assert [item.symbol for item in scopes.declarations(workflow.scope)] == [S("u")]
    assert workflow.undo() == 0
    assert workflow.scope == root
    assert scopes.declarations(workflow.scope) == ()
    assert workflow.events.visible() == ()
    assert workflow.redo() == 1
    assert workflow.scope == declared
    assert [item.symbol for item in scopes.declarations(workflow.scope)] == [S("u")]


def test_undo_reverts_definition(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    root = workflow.scope
    scopes = workflow.store.scopes
    body = parse(runtime, "x^2")
    workflow.define(S("u"), body)
    defined = workflow.scope
    assert [event.command for event in workflow.events.visible()] == ["Define"]
    assert scopes.lookup_definition(workflow.scope, S("u")) is body
    assert workflow.undo() == 0
    assert workflow.scope == root
    assert scopes.lookup_definition(workflow.scope, S("u")) is None
    assert workflow.redo() == 1
    assert workflow.scope == defined
    assert scopes.lookup_definition(workflow.scope, S("u")) is body


def test_operation_after_undo_branches(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    first = parse(runtime, "x^2")
    second = parse(runtime, "u > 0")
    third = parse(runtime, "v > 0")
    workflow.add(first, Claim())
    workflow.add(second, Claim())
    assert workflow.undo() == 1
    workflow.add(third, Claim())
    assert [int(event.id) for event in workflow.events.visible()] == [0, 2]
    assert [step.id for step in workflow.visible_steps()] == [0, 2]
    assert [step.id for step in workflow.all_steps()] == [0, 1, 2]
    assert workflow.redo() == 2
    assert [int(event.id) for event in workflow.events.visible()] == [0, 2]
    propositions = [
        item.proposition for item in workflow.store.scopes.assumptions(workflow.scope)
    ]
    assert propositions == [first, third]


def test_parent_revision_records_operation_location(runtime: Runtime) -> None:
    workflow, first, _second = _two_steps(runtime)
    revision = workflow.undo()
    assert revision == 1
    workflow.add(parse(runtime, "2*x"), Diff(pred=first.id, var=X))
    event = workflow.events.events()[-1]
    assert event.parent_revision == revision
    assert workflow.events.current_revision() == revision + 1
    assert [int(item.id) for item in workflow.events.visible()] == [0, 2]
    assert workflow.events.events()[1].parent_revision == 1


def test_repl_step_listing_and_undo_follow_visible_view(
    runtime: Runtime,
    capsys,
) -> None:
    repl = REPL(runtime)
    repl.cmd_claim("x^2")
    repl.cmd_claim("y^2")
    assert [step.id for step in repl.session.workflow.visible_steps()] == [0, 1]
    repl.cmd_undo(None)
    assert repl.session.workflow.events.current_revision() == 1
    assert [step.id for step in repl.session.workflow.visible_steps()] == [0]
    assert repl.session.focus == 0
    capsys.readouterr()
    repl.cmd_steps(None)
    shown = capsys.readouterr().out
    assert "# 0" in shown
    assert "# 1" not in shown
    repl.cmd_undo(None)
    assert [step.id for step in repl.session.workflow.visible_steps()] == [0]
    assert repl.session.focus == 0
