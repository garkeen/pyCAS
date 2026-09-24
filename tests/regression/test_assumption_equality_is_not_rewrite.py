# -*- coding: utf-8 -*-
"""Nail tests for the assumption-equality channel.

An assumption — including an equation the user asserted — is a fact to decide
*against*, never a rewrite rule. Consuming ledger equations as a bidirectional
rewrite system is not a decision procedure: it has no termination measure (it
was truncated by a hardcoded depth cap), it turned numbers into variables, and
it answered NO for statements that hold under the assumptions. These nails pin
the corrected behaviour:

· a ledger equation never makes a statement that holds under it come out NO;
· a chain of ledger equalities is decided (or honestly undecided), never
  refuted;
· refutation power is kept where evidence exists (a constrained symbol is still
  refutable once its value makes both sides closed and different);
· the bidirectional rewrite helper does not exist.
"""

from cas.runtime import bootstrap, get_runtime, new_workflow
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.math import decide as D
from cas.workflow.command import Claim

install(bootstrap())


def _ctx():
    return get_runtime().math


def _frame(*facts):
    """A scope whose assumptions are exactly the given propositions."""
    wf = new_workflow()
    for src in facts:
        wf.add(parse(src), Claim())
    return Assumptions.of(wf.store.scopes, wf.scope)


def test_assumed_value_endorses_constrained_expression():
    ctx = _ctx()
    frame = _frame("x = 1")
    assert D.decide(ctx, parse("x + x == 2"), frame).is_yes()
    assert D.decide(ctx, parse("x^2 == 1"), frame).is_yes()


def test_equality_chain_is_decided_not_refuted():
    ctx = _ctx()
    frame = _frame("a0 = a1", "a1 = a2", "a2 = a3", "a3 = a4")
    for q in ("a0 == a1", "a1 == a4", "a0 == a4", "a4 == a0"):
        v = D.decide(ctx, parse(q), frame)
        assert not v.is_no(), f"{q} was refuted under an equality chain: {v}"
    assert D.decide(ctx, parse("a0 == a4"), frame).is_yes()


def test_constrained_symbol_is_still_refutable():
    # Refutation power is not lost: with x = 1 in the ledger, x = 2 must be
    # refuted by evidence (both sides become closed and different).
    ctx = _ctx()
    frame = _frame("x = 1")
    assert D.decide(ctx, parse("x == 2"), frame).is_no()


def test_bidirectional_rewrite_helper_is_gone():
    assert not hasattr(D, "_eq_subst"), \
        "the ledger-equality bidirectional rewrite helper came back"
