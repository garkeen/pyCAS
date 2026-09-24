"""Definitions at the workflow boundary."""

import pytest

from cas.errors import ScopeError
from cas.frontend.parser import parse
from cas.runtime import Runtime, new_workflow
from cas.runtime.services import ScopeServices
from cas.syntax import term as T
from cas.syntax.term import S
from cas.workflow.command import Claim, Diff, Rewrite, Solve


def test_definition_expands_for_computation_and_keeps_step_form(
    runtime: Runtime,
) -> None:
    workflow = new_workflow(runtime)
    workflow.define(S("u"), parse(runtime, "x^2"))
    first = workflow.add(parse(runtime, "u^2"), Claim())
    second = workflow.add(
        parse(runtime, "4*x^3"),
        Diff(pred=first.id, var=S("x")),
    )
    assert second.status == "committed"
    assert first.content is parse(runtime, "u^2")
    assert second.content is parse(runtime, "4*x^3")


def test_normal_form_alias_step_is_verified_after_expansion(
    runtime: Runtime,
) -> None:
    workflow = new_workflow(runtime)
    workflow.define(S("u"), parse(runtime, "x^2"))
    first = workflow.add(parse(runtime, "u^2 + 3"), Claim())
    second = workflow.add(parse(runtime, "x^4 + 3"), Rewrite(pred=first.id))
    assert second.status == "committed"


def test_differentiating_defined_symbol_is_refused(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    workflow.define(S("u"), parse(runtime, "x^2"))
    first = workflow.add(parse(runtime, "u^2"), Claim())
    result = workflow.add(parse(runtime, "2*u"), Diff(pred=first.id, var=S("u")))
    assert result.status == "refused"


def test_solving_for_defined_symbol_is_refused(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    workflow.define(S("u"), parse(runtime, "x^2"))
    first = workflow.add(parse(runtime, "u == 4"), Claim())
    result = workflow.add(
        T.eq(S("u"), T.N(2)),
        Solve(pred=first.id, var=S("u"), solution=T.N(2)),
    )
    assert result.status == "refused"


def test_recursive_definition_is_refused(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    with pytest.raises(ScopeError):
        workflow.define(S("u"), parse(runtime, "u + 1"))


def test_mutually_recursive_definitions_are_refused(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    workflow.define(S("u"), parse(runtime, "z + 1"))
    with pytest.raises(ScopeError):
        workflow.define(S("z"), parse(runtime, "u + 1"))


def test_frame_assumptions_are_read_through_definitions(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    workflow.define(S("u"), parse(runtime, "x^2"))
    workflow.add(parse(runtime, "u = 9"), Claim())
    services = ScopeServices(workflow.store.scopes, runtime.math)
    assert services.decide(parse(runtime, "x^2 == 9"), workflow.scope).is_yes()
