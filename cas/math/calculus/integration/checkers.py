"""Integration checkers.

Independent re-check: `d/dx antiderivative == integrand`, going through the
differentiation layer (a different implementation). A definite integral also
checks `value == antiderivative(b) - antiderivative(a)` by exact evaluation. The
integrator and the integration checker are separate: the checker never re-runs
integration, it only re-checks the certificate.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from cas.kernel.commit import ResolvedProposal
from cas.kernel.context import TrackedContext
from cas.kernel.evidence import (
    CheckResult,
    RefutationRejected,
    Rejected,
    UnknownResult,
)
from cas.kernel.services import KernelServices
from cas.kernel.verdict import No, Reason, Unknown
from cas.math.base.checkers import (
    _expand,
    _identity,
    _is_piecewise,
    _ok,
    _one_conclusion,
    _payload,
    _premise,
)
from cas.math.builder import CheckerRegistration, MathBuilder
from cas.math.domains.qarith import fold
from cas.syntax import term as T
from cas.syntax.term import S
from cas.syntax.termpath import subst
from cas.workflow.command import IntegratePayload

if TYPE_CHECKING:
    from cas.math.context import MathContext


class IntegrateChecker:
    id = "calculus.antiderivative"

    def __init__(self, ctx: MathContext) -> None:
        self.ctx = ctx

    def check(
        self,
        proposal: ResolvedProposal,
        context: TrackedContext,
        services: KernelServices,
    ) -> CheckResult:
        content = _one_conclusion(proposal)
        if isinstance(content, Rejected):
            return content
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        d = _payload(proposal, IntegratePayload)
        if d is None:
            return Rejected(
                Reason.FRAGMENT,
                "calculus.antiderivative requires an integrate payload",
            )
        pred = _expand(context, pred)
        content = _expand(context, content)
        f, x, G = pred, d.var, _expand(context, d.antideriv)
        from cas.math.calculus.integration.verify import verify_antideriv

        derivative_verdict = verify_antideriv(self.ctx, G, f, x)
        if isinstance(derivative_verdict, No):
            return RefutationRejected(derivative_verdict.evidence)
        if isinstance(derivative_verdict, Unknown):
            # The vanishing channel does not cover this (an exp/sin combination,
            # for example): a capability gap, honestly undecided rather than a
            # refutation.
            return UnknownResult(
                Reason.FRAGMENT,
                "the differentiation layer cannot decide (no expansion-to-zero channel)",
            )
        if d.bounds is None:
            want = T.eq(T.mk(S("Integrate"), (T.mk_bound(x, f),)), G)
            bad = _identity(
                self.ctx,
                content,
                want,
                "content does not match the antiderivative equation",
            )
            if bad is not None:
                return bad
            return _ok(self.ctx, proposal, context)
        a_t, b_t = d.bounds
        if _is_piecewise(f) or not (T.is_num(a_t) and T.is_num(b_t)):
            return UnknownResult(
                Reason.FRAGMENT,
                "piecewise/algebraic definite integration is not hooked up for independent checking",
            )
        Fa = fold(subst(G, {x: a_t}))
        Fb = fold(subst(G, {x: b_t}))
        val = fold(T.plus(Fb, T.neg(Fa)))
        want = T.eq(
            T.mk(S("DefIntegrate"), (T.mk_bound(x, f), a_t, b_t)),
            val,
        )
        bad = _identity(
            self.ctx,
            content,
            want,
            "definite integral value does not match the endpoint difference",
        )
        if bad is not None:
            return bad
        return _ok(self.ctx, proposal, context)


CHECKERS = (IntegrateChecker,)


def register(builder: MathBuilder) -> None:
    for checker in CHECKERS:
        builder.register_checker(CheckerRegistration(checker.id, checker))
