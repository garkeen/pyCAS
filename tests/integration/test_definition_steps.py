# -*- coding: utf-8 -*-
"""Definitions at the workflow boundary.

A definition is transparent to computation and to verification (both expand it),
while the *stored* step keeps the form the user wrote. An equation is an
assumption: it is never expanded and never used as a rewrite rule — the frame is
only read through the aliases it mentions.
"""

import pytest

from cas.runtime import bootstrap, get_runtime, new_workflow
from cas.runtime.dispatch import install
from cas.runtime.services import ScopeServices
from cas.frontend.parser import parse
from cas.errors import ScopeError
from cas.syntax import term as T
from cas.syntax.term import S
from cas.workflow.command import Claim, Diff, Rewrite

install(bootstrap())


def test_definition_expands_for_computation_and_keeps_the_step_form():
    wf = new_workflow()
    wf.define(S("u"), parse("x^2"))
    s0 = wf.add(parse("u^2"), Claim())
    s1 = wf.add(parse("4*x^3"), Diff(pred=s0.id, var=S("x")))
    assert s1.status == "committed", s1.note
    # the recorded step keeps the form it was written in ...
    assert s0.content is parse("u^2")
    # ... while the computation saw through the alias
    assert s1.content is parse("4*x^3")


def test_normal_form_of_an_alias_bearing_step_is_verified_after_expansion():
    wf = new_workflow()
    wf.define(S("u"), parse("x^2"))
    s0 = wf.add(parse("u^2 + 3"), Claim())
    s1 = wf.add(parse("x^4 + 3"), Rewrite(pred=s0.id))
    assert s1.status == "committed", s1.note


def test_differentiating_with_respect_to_a_defined_symbol_is_refused():
    wf = new_workflow()
    wf.define(S("u"), parse("x^2"))
    s0 = wf.add(parse("u^2"), Claim())
    s1 = wf.add(parse("2*u"), Diff(pred=s0.id, var=S("u")))
    assert s1.status == "refused"


def test_solving_for_a_defined_symbol_is_refused():
    wf = new_workflow()
    wf.define(S("u"), parse("x^2"))
    s0 = wf.add(parse("u == 4"), Claim())
    from cas.workflow.command import Solve
    s1 = wf.add(T.eq(S("u"), T.N(2)), Solve(pred=s0.id, var=S("u"),
                                            solution=T.N(2)))
    assert s1.status == "refused"


def test_recursive_definition_is_refused():
    wf = new_workflow()
    with pytest.raises(ScopeError):
        wf.define(S("u"), parse("u + 1"))


def test_mutually_recursive_definitions_are_refused():
    wf = new_workflow()
    wf.define(S("u"), parse("z + 1"))
    with pytest.raises(ScopeError):
        wf.define(S("z"), parse("u + 1"))


def test_frame_assumptions_are_read_through_definitions():
    """The commit-time discharge path expands definitions, so a fact stated with
    an alias endorses the expanded query (and the stored assumption keeps its
    own form: a definition is transparent, an equation is not rewritten)."""
    wf = new_workflow()
    wf.define(S("u"), parse("x^2"))
    wf.add(parse("u = 9"), Claim())
    services = ScopeServices(wf.store.scopes, get_runtime().math)
    assert services.decide(parse("x^2 == 9"), wf.scope).is_yes()
