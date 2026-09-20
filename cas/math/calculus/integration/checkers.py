"""Integration checkers.

Independent re-check: `d/dx antiderivative == integrand`, going through the
differentiation layer (a different implementation). A definite integral also
checks `value == antiderivative(b) - antiderivative(a)` by exact evaluation. The
integrator and the integration checker are separate: the checker never re-runs
integration, it only re-checks the certificate.
"""

from cas.kernel.evidence import Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.syntax.term import S
from cas.syntax import term as T
from cas.math.domains.qarith import fold
from cas.math.base.checkers import (
    _is_piecewise, _ok, _one_conclusion, _premise,
)
from cas.math.base.equality import equal


class IntegrateChecker:
    id = "calculus.antiderivative"

    def __init__(self, ctx):
        self.ctx = ctx

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        d = proposal.evidence.payload
        f, x, G = pred, d.var, d.antideriv
        from cas.math.calculus.integration.verify import verify_antideriv
        ok = verify_antideriv(self.ctx, G, f, x)
        if ok is False:
            return Rejected(Reason.FRAGMENT, "the differentiation-layer re-check failed")
        if ok is None:
            # The vanishing channel does not cover this (an exp/sin combination,
            # for example): a capability gap, honestly undecided rather than a
            # refutation.
            return UnknownResult(Reason.FRAGMENT, "the differentiation layer cannot decide (no expansion-to-zero channel)")
        if d.bounds is None:
            want = T.eq(T.mk(S("Integrate"), (T.mk_bound(x, f),)), G)
            if equal(self.ctx, content, want):
                return _ok(self.ctx, proposal, context)
            return Rejected(Reason.FRAGMENT, "content does not match the antiderivative equation")
        a_t, b_t = d.bounds
        if _is_piecewise(f) or not (T.is_num(a_t) and T.is_num(b_t)):
            return UnknownResult(Reason.FRAGMENT, "piecewise/algebraic definite integration is not hooked up for independent checking")
        Fa = fold(T.subst(G, {x: a_t}))
        Fb = fold(T.subst(G, {x: b_t}))
        val = fold(T.plus(Fb, T.neg(Fa)))
        want = T.eq(T.mk(S("DefIntegrate"), (T.mk_bound(x, f), a_t, b_t)), val)
        if equal(self.ctx, content, want):
            return _ok(self.ctx, proposal, context)
        return Rejected(Reason.FRAGMENT, "definite integral value does not match the endpoint difference")


CHECKERS = (IntegrateChecker,)


def register(builder) -> None:
    for cls in CHECKERS:
        builder.register_checker(cls.id, cls)
