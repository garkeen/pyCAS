# -*- coding: utf-8 -*-
"""Scope versions: every id names one fixed context.

An extension appends entries and returns a new version with its own id, so a
recorded conclusion is never re-interpreted by entries added later. A branch
forks from one fixed version of its parent and only ever sees that version and
its ancestors.
"""

import pytest

from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.errors import ScopeError
from cas.frontend.parser import parse
from cas.workflow.command import Claim

install(bootstrap())


def test_extension_appends_a_new_version():
    wf = new_workflow()
    root = wf.scope
    wf.add(parse("x^2"), Claim())
    current = wf.scope
    scopes = wf.store.scopes
    assert current != root
    assert scopes.lineage_of(current) == scopes.lineage_of(root)
    assert scopes.head_of(root) == current
    assert scopes.assumptions(root) == ()
    assert [a.proposition for a in scopes.assumptions(current)] == [parse("x^2")]


def test_conclusion_keeps_the_context_it_was_checked_in():
    """A later claim must not change how an earlier conclusion is read, and a
    claim is never read under its own assumption."""
    wf = new_workflow()
    first = wf.add(parse("x^2"), Claim())
    second = wf.add(parse("u > 0"), Claim())
    scopes = wf.store.scopes
    j0 = wf.store.get_judgment(first.judgment)
    j1 = wf.store.get_judgment(second.judgment)
    assert j0.scope != j1.scope
    assert scopes.assumptions(j0.scope) == ()
    assert [a.proposition for a in scopes.assumptions(j1.scope)] == [parse("x^2")]
    # the assumption of the second claim lands in the version after its judgment
    assert wf.scope != j1.scope
    assert [a.proposition for a in scopes.assumptions(wf.scope)] == [
        parse("x^2"), parse("u > 0")]


def test_extension_of_an_older_version_is_refused():
    """Only the current version of a lineage can be extended: extending an older
    one would fork the version chain and leave the head ambiguous."""
    wf = new_workflow()
    root = wf.store.scopes.get(wf.scope)
    wf.add(parse("x^2"), Claim())
    with pytest.raises(ScopeError):
        wf.store.scopes.extend(root)


def test_branch_does_not_see_later_parent_entries():
    """A branch forks from one fixed version of its parent, so entries appended
    to the parent afterwards are not part of the branch context."""
    wf = new_workflow()
    group = wf.split_on(parse("x != 0"))
    case = group.cases[0]
    wf.enter(group.parent_lineage)
    wf.add(parse("u > 0"), Claim())              # the parent grows afterwards
    scopes = wf.store.scopes
    assert [a.proposition for a in scopes.assumptions(case.scope)] == [
        parse("x != 0")]
    assert scopes.head_of(case.scope) == case.scope


def test_introducers_index_names_the_introducing_version():
    """The escape check asks which scopes introduce a symbol: the answer is the
    version that recorded the declaration, not every version of its lineage."""
    from cas.syntax.term import S
    wf = new_workflow()
    scopes = wf.store.scopes
    root = wf.scope
    wf.declare(S("u"), S("Real"))
    assert scopes.introducers(S("u")) == (wf.scope,)
    assert scopes.introducers(S("u")) != (root,)
    assert scopes.introducers(S("never_introduced")) == ()
