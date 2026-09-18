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

from cas.syntax import term as T
from cas.syntax.term import S


def _ledger_decide(r, a, b, assumptions):
    """Hand `Eq(r, 0)` to the decision pipeline; return None if undecided so a
    later stage can take over."""
    from cas.math.decide import decide
    d = decide(T.mk(S("Eq"), (r, T.ZERO)), assumptions)
    return None if d.is_unknown() else d


def install(builder) -> None:
    from cas.math.base import checkers
    checkers.register(builder)
    builder.register_eq_stage("ledger_decide", _ledger_decide)
