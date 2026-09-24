# -*- coding: utf-8 -*-
"""Assembly of the base module.

Currently one item: `ledger_decide` -- the last stage of identity decision, which
hands "difference equals zero" to the decision pipeline. It used to **self-register
at import time** inside `cas/math/decide.py` (`register_eq_stage(...)`); it is now
an `install(builder)` step, registered only during `bootstrap()`.

A stage is an **extension point**: the domain normal form / projection zero test
answers first, and only a failure to answer falls through to here. A future normal
form for the transcendental tower registers through the same protocol as a new
stage, without touching the decider.
"""

from cas.kernel.scope import Assumptions
from cas.kernel.verdict import Verdict
from cas.math.builder import DecisionStage, MathBuilder
from cas.math.context import MathContext
from cas.syntax import term as T
from cas.syntax.term import S, Term


def _ledger_decide(
    ctx: MathContext,
    r: Term,
    a: Term,
    b: Term,
    assumptions: Assumptions,
) -> Verdict | None:
    """Hand `Eq(r, 0)` to the decision pipeline; return None if undecided so a
    later stage can take over."""
    from cas.math.decide import decide
    d = decide(ctx, T.mk(S("Eq"), (r, T.ZERO)), assumptions)
    return None if d.is_unknown() else d


def install(builder: MathBuilder) -> None:
    from cas.math.base import checkers, commands
    checkers.register(builder)
    commands.install(builder)
    builder.register_decision_stage(DecisionStage("ledger_decide", _ledger_decide))
