"""Decision verdicts do not depend on a search-depth cap."""

import inspect

from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.math import decide as decision_module
from cas.runtime import Runtime, new_workflow
from cas.syntax import term as T
from cas.workflow.command import Claim


def _frame(runtime: Runtime, *facts: str) -> Assumptions:
    workflow = new_workflow(runtime)
    for source in facts:
        workflow.add(parse(runtime, source), Claim())
    return Assumptions.of(workflow.store.scopes, workflow.scope)


def test_no_hardcoded_search_depth_cap() -> None:
    assert not hasattr(decision_module, "_MAX_DEPTH")


def test_decide_has_no_depth_parameter() -> None:
    parameters = inspect.signature(decision_module.decide).parameters
    assert not any("depth" in name for name in parameters)


def test_verdict_is_same_from_every_entry_path(runtime: Runtime) -> None:
    frame = _frame(runtime, "A = 1")
    for source in ("1 + 1 == 2", "A + A == 2", "A == 1", "x + x == 2"):
        fact = parse(runtime, source)
        direct = decision_module.decide(runtime.math, fact, frame)
        nested = decision_module.decide(
            runtime.math,
            T.mk(T.S("And"), (fact, T.TRUE)),
            frame,
        )
        assert direct is nested
