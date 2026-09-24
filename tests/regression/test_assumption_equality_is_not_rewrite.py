"""Ledger equalities are facts, not rewrite rules."""

from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.math import decide as decision_module
from cas.runtime import Runtime, new_workflow
from cas.workflow.command import Claim


def _frame(runtime: Runtime, *facts: str) -> Assumptions:
    workflow = new_workflow(runtime)
    for source in facts:
        workflow.add(parse(runtime, source), Claim())
    return Assumptions.of(workflow.store.scopes, workflow.scope)


def test_assumed_value_endorses_constrained_expression(runtime: Runtime) -> None:
    frame = _frame(runtime, "x = 1")
    assert decision_module.decide(
        runtime.math, parse(runtime, "x + x == 2"), frame
    ).is_yes()
    assert decision_module.decide(
        runtime.math, parse(runtime, "x^2 == 1"), frame
    ).is_yes()


def test_equality_chain_is_decided_not_refuted(runtime: Runtime) -> None:
    frame = _frame(
        runtime,
        "a0 = a1",
        "a1 = a2",
        "a2 = a3",
        "a3 = a4",
    )
    for source in ("a0 == a1", "a1 == a4", "a0 == a4", "a4 == a0"):
        verdict = decision_module.decide(runtime.math, parse(runtime, source), frame)
        assert not verdict.is_no()
    assert decision_module.decide(
        runtime.math, parse(runtime, "a0 == a4"), frame
    ).is_yes()


def test_constrained_symbol_is_still_refutable(runtime: Runtime) -> None:
    frame = _frame(runtime, "x = 1")
    assert decision_module.decide(
        runtime.math, parse(runtime, "x == 2"), frame
    ).is_no()


def test_bidirectional_rewrite_helper_is_gone() -> None:
    assert not hasattr(decision_module, "_eq_subst")
