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
from cas.math.judge import back_substitute
from cas.math.base.checkers import (
    _ok, _one_conclusion, _premise,
)


class SolveChecker:
    id = "solve.back_substitute"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None or not T.is_eq(pred):
            return Rejected(Reason.FRAGMENT, "premise is not an equality")
        d = proposal.evidence.payload
        if not (T.is_eq(content) and content.args[0] is d.var
                and content.args[1] is d.solution):
            return Rejected(Reason.FRAGMENT,
                            "conclusion is not that variable equal to that solution")
        z = back_substitute(pred, d.var, d.solution).zero
        if z is True:
            return _ok(proposal, context)
        if z is False:
            return Rejected(Reason.FRAGMENT,
                            "back-substitution does not vanish: not a solution")
        return UnknownResult(Reason.FRAGMENT,
                             "back-substitution zero test outside the projection")


CHECKERS = (SolveChecker,)


def register(store) -> None:
    for cls in CHECKERS:
        ck = cls()
        if ck.id not in store.checkers:
            store.checkers.register(ck.id, ck)
