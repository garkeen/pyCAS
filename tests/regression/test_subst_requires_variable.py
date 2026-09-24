"""Substitution commands require an occurring variable key."""

from cas.frontend.parser import parse
from cas.runtime import Runtime, new_workflow
from cas.syntax.term import S
from cas.workflow.command import Claim, Subst


def _claimed(runtime: Runtime, source: str):
    workflow = new_workflow(runtime)
    return workflow, workflow.add(parse(runtime, source), Claim())


def test_compound_key_is_refused(runtime: Runtime) -> None:
    workflow, first = _claimed(runtime, "A == B + C")
    result = workflow.add(
        first.content,
        Subst(
            pred=first.id,
            var=S("B + C"),
            value=parse(runtime, "A"),
        ),
    )
    assert result.status == "refused"


def test_absent_variable_is_refused(runtime: Runtime) -> None:
    workflow, first = _claimed(runtime, "A == B + C")
    result = workflow.add(
        first.content,
        Subst(
            pred=first.id,
            var=parse(runtime, "z"),
            value=parse(runtime, "7"),
        ),
    )
    assert result.status == "refused"
