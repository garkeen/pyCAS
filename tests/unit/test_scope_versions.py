"""Scope versions are immutable."""

import pytest

from cas.errors import ScopeError
from cas.frontend.parser import parse
from cas.runtime import Runtime, new_workflow
from cas.workflow.command import Claim


def test_extension_appends_a_new_version(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    root = workflow.scope
    workflow.add(parse(runtime, "x^2"), Claim())
    current = workflow.scope
    scopes = workflow.store.scopes
    assert current != root
    assert scopes.lineage_of(current) == scopes.lineage_of(root)
    assert scopes.head_of(root) == current
    assert scopes.assumptions(root) == ()
    assert [item.proposition for item in scopes.assumptions(current)] == [
        parse(runtime, "x^2")
    ]


def test_conclusion_keeps_the_context_it_was_checked_in(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    first = workflow.add(parse(runtime, "x^2"), Claim())
    second = workflow.add(parse(runtime, "u > 0"), Claim())
    scopes = workflow.store.scopes
    first_judgment = workflow.store.get_judgment(first.judgment)
    second_judgment = workflow.store.get_judgment(second.judgment)
    assert first_judgment.scope != second_judgment.scope
    assert scopes.assumptions(first_judgment.scope) == ()
    assert [item.proposition for item in scopes.assumptions(second_judgment.scope)] == [
        parse(runtime, "x^2")
    ]
    assert workflow.scope != second_judgment.scope
    assert [item.proposition for item in scopes.assumptions(workflow.scope)] == [
        parse(runtime, "x^2"),
        parse(runtime, "u > 0"),
    ]


def test_extension_of_an_older_version_is_refused(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    root = workflow.store.scopes.get(workflow.scope)
    workflow.add(parse(runtime, "x^2"), Claim())
    with pytest.raises(ScopeError):
        workflow.store.scopes.extend(root)


def test_branch_does_not_see_later_parent_entries(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    group = workflow.split_on(parse(runtime, "x != 0"))
    case = group.cases[0]
    workflow.enter(group.parent_lineage)
    workflow.add(parse(runtime, "u > 0"), Claim())
    scopes = workflow.store.scopes
    assert [item.proposition for item in scopes.assumptions(case.scope)] == [
        parse(runtime, "x != 0")
    ]
    assert scopes.head_of(case.scope) == case.scope


def test_introducers_index_names_the_introducing_version(runtime: Runtime) -> None:
    from cas.syntax.term import S

    workflow = new_workflow(runtime)
    scopes = workflow.store.scopes
    root = workflow.scope
    workflow.declare(S("u"), S("Real"))
    assert scopes.introducers(S("u")) == (workflow.scope,)
    assert scopes.introducers(S("u")) != (root,)
    assert scopes.introducers(S("never_introduced")) == ()
