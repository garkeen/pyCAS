# -*- coding: utf-8 -*-
"""Scope contract: declaration/definition, and the invariant that a local symbol must
not escape.

Before the wiring: `Scope`'s `declarations`/`definitions` fields,
`ScopeStore.declarations`/`definition_map`/`lookup_definition`, and the local-symbol
check had no producer and no consumer, so the locally defined symbol mechanism was
half-built, step 1 of `commit` only checked "the scope exists", and the escape check
had no execution point. This file pins the behaviour once it is wired up.
"""

import pytest

from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.errors import ScopeError
from cas.syntax import term as T
from cas.syntax.term import S

install(bootstrap())

X = S("x")
U = S("u")


def _wf():
    return new_workflow()


def _child(wf):
    """Create a child scope and enter it."""
    parent = wf.store.scopes.get(wf.scope)
    c = wf.store.scopes.child(parent)
    wf.enter(c.id)
    return c.id


# ---------------------------------------------------------------------------
# Declaration / definition: the producers
# ---------------------------------------------------------------------------

def test_definition_visible_on_scope_chain():
    wf = _wf()
    root = wf.scope
    body = T.times(X, X)
    wf.define(U, body)
    # the definition lands in a new version of the same scope, and that version
    # becomes the current one
    assert wf.scope != root
    assert wf.store.scopes.lookup_definition(wf.scope, U) is body
    assert wf.store.scopes.definition_map(wf.scope)[U] is body
    assert wf.store.scopes.head_of(root) == wf.scope
    assert wf.store.scopes.lineage_of(root) == wf.store.scopes.lineage_of(wf.scope)
    # the earlier version stays frozen: the entry did not grow there retroactively
    assert wf.store.scopes.lookup_definition(root, U) is None


def test_declaration_enters_scope_entries():
    wf = _wf()
    root = wf.scope
    wf.declare(U, S("Real"))
    decls = wf.store.scopes.declarations(wf.scope)
    assert len(decls) == 1 and decls[0].symbol is U
    # a declaration appends on top of the previous version, which stays frozen
    assert wf.store.scopes.declarations(root) == ()


def test_defined_symbol_not_flagged_as_escape():
    """Using a defined local symbol inside its own scope is legal, not an escape."""
    wf = _wf()
    wf.define(U, T.times(X, X))
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "committed", s.note


def test_descendant_sees_ancestor_definition():
    """The symbol was introduced by an ancestor, so descendants can see it: present on
    the chain is not an escape."""
    wf = _wf()
    wf.define(U, T.times(X, X))
    _child(wf)
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "committed", s.note


# ---------------------------------------------------------------------------
# The four checks
# ---------------------------------------------------------------------------

def test_stale_symbol_rejected_redefinition():
    wf = _wf()
    wf.define(U, T.times(X, X))
    with pytest.raises(ScopeError):
        wf.define(U, X)


def test_stale_symbol_rejected_redeclaration():
    wf = _wf()
    wf.declare(U, S("Real"))
    with pytest.raises(ScopeError):
        wf.declare(U, S("Integer"))


def test_stale_symbol_rejected_declare_then_define():
    wf = _wf()
    wf.declare(U, S("Real"))
    with pytest.raises(ScopeError):
        wf.define(U, X)


def test_recursive_definition_rejected():
    wf = _wf()
    with pytest.raises(ScopeError):
        wf.define(U, T.plus(U, X))


def test_definition_body_may_use_earlier_same_scope_alias():
    """Ordering is **visible-in-order**: within one scope a later definition may use an
    earlier alias."""
    wf = _wf()
    wf.define(U, T.times(X, X))
    v = S("v")
    wf.define(v, T.plus(U, X))
    assert wf.store.scopes.lookup_definition(wf.scope, v) is T.plus(U, X)
    assert wf.store.scopes.lookup_definition(wf.scope, U) is T.times(X, X)


def test_definition_body_may_not_use_other_scope_local():
    """The right-hand side may not reference a local symbol of **another** scope (a
    sibling branch); that one really is unbound."""
    wf = _wf()
    root = wf.scope
    _child(wf)
    wf.define(U, T.times(X, X))
    wf.enter(root)
    _child(wf)
    with pytest.raises(ScopeError):
        wf.define(S("v"), T.plus(U, X))


def test_mutual_alias_recursion_rejected():
    """A mutually recursive alias pair (u := v then v := u) is also an unexpandable
    cycle."""
    wf = _wf()
    v = S("v")
    wf.define(U, v)                     # v is a free symbol here, so this is allowed
    with pytest.raises(ScopeError):
        wf.define(v, T.plus(U, X))


# ---------------------------------------------------------------------------
# The invariant: a local symbol must not escape into a conclusion outside its scope
# ---------------------------------------------------------------------------

def test_local_symbol_must_not_escape_to_parent():
    wf = _wf()
    root = wf.scope
    _child(wf)
    wf.define(U, T.times(X, X))
    # legal inside this scope
    assert wf.add(T.eq(U, T.times(X, X)), _claim()).status == "committed"
    # back in the parent scope u is not visible here, so the conclusion may not contain it
    wf.enter(root)
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "refused"
    assert "escapes" in s.note


def test_sibling_branches_do_not_share_locals():
    """Two branches each define a local symbol of the same name; neither is a visible
    introduction for the other."""
    wf = _wf()
    root = wf.scope
    a = _child(wf)
    wf.define(U, T.times(X, X))
    wf.enter(root)
    b = _child(wf)
    # u is not on b's chain (a's u is not on b's chain), so using u in b is an escape
    s = wf.add(T.eq(U, T.times(X, X)), _claim())
    assert s.status == "refused" and "escapes" in s.note
    assert a != b


def _claim():
    from cas.workflow.command import Claim
    return Claim()
