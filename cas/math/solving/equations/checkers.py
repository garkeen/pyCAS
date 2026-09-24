# -*- coding: utf-8 -*-
"""Checkers for equation solving.

**Back-substitution judge**: the solver hands over a solution (the certificate)
and the checker only substitutes it and decides zero via the domain normal form.
It never reruns the solving formula -- the most direct instance of the rule that a
verifier must be independent of its solver. Zero decision outside the projection
is honestly left undecided.
"""

from cas.syntax import term as T
from cas.kernel.evidence import Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.kernel.scope import Assumptions
from cas.math.judge import back_substitute
from cas.math.base.checkers import (
    _defined, _expand, _ok, _one_conclusion, _premise,
)
from cas.math.linearform import linear_form, nonzero_condition


class SolveChecker:
    id = "solve.back_substitute"

    def __init__(self, ctx):
        self.ctx = ctx

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None or not T.is_eq(pred):
            return Rejected(Reason.FRAGMENT, "premise is not an equality")
        d = proposal.evidence.payload
        if _defined(context, d.var):
            return Rejected(Reason.FRAGMENT,
                            f"cannot solve for a defined symbol: {d.var}")
        pred = _expand(context, pred)
        content = _expand(context, content)
        if not (T.is_eq(content) and content.args[0] is d.var
                and content.args[1] is d.solution):
            return Rejected(Reason.FRAGMENT,
                            "conclusion is not that variable equal to that solution")
        frame = Assumptions(tuple(context.assumptions())) if hasattr(context, "assumptions") else None
        z = back_substitute(self.ctx, pred, d.var, d.solution, frame).zero
        extra = ()
        if d.condition is not None:
            form = linear_form(self.ctx, T.plus(pred.args[0], T.neg(pred.args[1])), d.var)
            if form.kind != "linear" or d.condition is not nonzero_condition(form.payload[0]):
                return Rejected(Reason.FRAGMENT,
                                "the declared solve condition is not the linear slope condition")
            extra = (d.condition,)
        if z is True:
            return _ok(self.ctx, proposal, context, extra)
        if z is False:
            return Rejected(Reason.FRAGMENT,
                            "back-substitution does not vanish: not a solution")
        return UnknownResult(Reason.FRAGMENT,
                             "back-substitution zero test outside the projection")


CHECKERS = (SolveChecker,)


def register(builder) -> None:
    for cls in CHECKERS:
        builder.register_checker(cls.id, cls)
