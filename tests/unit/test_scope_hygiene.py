"""Scope declarations, definitions, and local-symbol hygiene."""

import pytest

from cas.errors import ScopeError
from cas.runtime import Runtime, new_workflow
from cas.syntax import term as T
from cas.syntax.term import S
from cas.workflow.command import Claim

X = S("x")
U = S("u")


def _workflow(runtime: Runtime):
    return new_workflow(runtime)


def _child(workflow) -> int:
    parent = workflow.store.scopes.get(workflow.scope)
    child = workflow.store.scopes.child(parent)
    workflow.enter(child.id)
    return child.id


def test_definition_visible_on_scope_chain(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    root = workflow.scope
    body = T.times(X, X)
    workflow.define(U, body)
    assert workflow.scope != root
    assert workflow.store.scopes.lookup_definition(workflow.scope, U) is body
    assert workflow.store.scopes.definition_map(workflow.scope)[U] is body
    assert workflow.store.scopes.head_of(root) == workflow.scope
    assert workflow.store.scopes.lineage_of(root) == workflow.store.scopes.lineage_of(
        workflow.scope
    )
    assert workflow.store.scopes.lookup_definition(root, U) is None


def test_declaration_enters_scope_entries(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    root = workflow.scope
    workflow.declare(U, S("Real"))
    declarations = workflow.store.scopes.declarations(workflow.scope)
    assert len(declarations) == 1 and declarations[0].symbol is U
    assert workflow.store.scopes.declarations(root) == ()


def test_defined_symbol_not_flagged_as_escape(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    workflow.define(U, T.times(X, X))
    step = workflow.add(T.eq(U, T.times(X, X)), Claim())
    assert step.status == "committed"


def test_descendant_sees_ancestor_definition(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    workflow.define(U, T.times(X, X))
    _child(workflow)
    step = workflow.add(T.eq(U, T.times(X, X)), Claim())
    assert step.status == "committed"


def test_stale_symbol_rejected_redefinition(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    workflow.define(U, T.times(X, X))
    with pytest.raises(ScopeError):
        workflow.define(U, X)


def test_stale_symbol_rejected_redeclaration(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    workflow.declare(U, S("Real"))
    with pytest.raises(ScopeError):
        workflow.declare(U, S("Integer"))


def test_stale_symbol_rejected_declare_then_define(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    workflow.declare(U, S("Real"))
    with pytest.raises(ScopeError):
        workflow.define(U, X)


def test_recursive_definition_rejected(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    with pytest.raises(ScopeError):
        workflow.define(U, T.plus(U, X))


def test_definition_body_may_use_earlier_alias(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    workflow.define(U, T.times(X, X))
    v = S("v")
    workflow.define(v, T.plus(U, X))
    assert workflow.store.scopes.lookup_definition(workflow.scope, v) is T.plus(U, X)
    assert workflow.store.scopes.lookup_definition(workflow.scope, U) is T.times(X, X)


def test_definition_body_may_not_use_other_scope_local(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    root = workflow.scope
    _child(workflow)
    workflow.define(U, T.times(X, X))
    workflow.enter(root)
    _child(workflow)
    with pytest.raises(ScopeError):
        workflow.define(S("v"), T.plus(U, X))


def test_mutual_alias_recursion_rejected(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    v = S("v")
    workflow.define(U, v)
    with pytest.raises(ScopeError):
        workflow.define(v, T.plus(U, X))


def test_local_symbol_must_not_escape_to_parent(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    root = workflow.scope
    _child(workflow)
    workflow.define(U, T.times(X, X))
    assert workflow.add(T.eq(U, T.times(X, X)), Claim()).status == "committed"
    workflow.enter(root)
    step = workflow.add(T.eq(U, T.times(X, X)), Claim())
    assert step.status == "refused"
    assert "escapes" in step.note


def test_sibling_branches_do_not_share_locals(runtime: Runtime) -> None:
    workflow = _workflow(runtime)
    root = workflow.scope
    first = _child(workflow)
    workflow.define(U, T.times(X, X))
    workflow.enter(root)
    second = _child(workflow)
    step = workflow.add(T.eq(U, T.times(X, X)), Claim())
    assert step.status == "refused" and "escapes" in step.note
    assert first != second
