"""An unverifiable identity remains undecided."""

from cas.frontend.parser import parse
from cas.runtime import Runtime, new_workflow
from cas.workflow.command import Claim, Rewrite


def test_unprovable_identity_is_undecided_not_refused(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    first = workflow.add(parse(runtime, "sin(x) + sin(x)"), Claim())
    result = workflow.add(parse(runtime, "2*sin(x)"), Rewrite(pred=first.id))
    assert result.status == "undecided"
