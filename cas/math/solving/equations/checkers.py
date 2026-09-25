"""Independent back-substitution checker for equation solving."""

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
from cas.kernel.scope import Assumptions
from cas.kernel.services import KernelServices
from cas.kernel.verdict import No, Reason, Unknown
from cas.math.base.checkers import (
    _accepted,
    _defined,
    _expand,
    _is_equation,
    _one_conclusion,
    _payload,
    _premise,
)
from cas.math.builder import CheckerRegistration, MathBuilder
from cas.math.judge import back_substitute
from cas.math.linearform import linear_form, nonzero_condition
from cas.syntax import term as T
from cas.syntax.term import Term
from cas.workflow.command import SolvePayload

if TYPE_CHECKING:
    from cas.math.context import MathContext


class SolveChecker:
    id = "solve.back_substitute"

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
        premise = _premise(proposal)
        if premise is None:
            return Rejected(Reason.FRAGMENT, "premise is not an equality")
        payload = _payload(proposal, SolvePayload)
        if payload is None:
            return Rejected(Reason.FRAGMENT, "solve requires a solve payload")
        if _defined(context, payload.var):
            return Rejected(
                Reason.FRAGMENT,
                f"cannot solve for a defined symbol: {payload.var}",
            )
        expanded_premise = _expand(context, premise)
        if not _is_equation(expanded_premise):
            return Rejected(Reason.FRAGMENT, "premise is not an equality")
        expanded_content = _expand(context, content)
        if not (
            _is_equation(expanded_content)
            and expanded_content.args[0] is payload.var
            and expanded_content.args[1] is payload.solution
        ):
            return Rejected(
                Reason.FRAGMENT,
                "conclusion is not that variable equal to that solution",
            )
        frame = Assumptions(tuple(context.assumptions()))
        substitution = back_substitute(
            self.ctx,
            expanded_premise,
            payload.var,
            payload.solution,
            frame,
        )
        extra: tuple[Term, ...] = ()
        if payload.condition is not None:
            form = linear_form(
                self.ctx,
                T.plus(
                    expanded_premise.args[0],
                    T.neg(expanded_premise.args[1]),
                ),
                payload.var,
            )
            if form.kind != "linear" or not isinstance(form.payload, tuple):
                return Rejected(
                    Reason.FRAGMENT,
                    "the declared solve condition is not the linear slope condition",
                )
            expected = nonzero_condition(form.payload[0])
            if payload.condition is not expected:
                return Rejected(
                    Reason.FRAGMENT,
                    "the declared solve condition is not the linear slope condition",
                )
            extra = (payload.condition,)
        if isinstance(substitution.verdict, No):
            return RefutationRejected(substitution.verdict.evidence)
        if isinstance(substitution.verdict, Unknown):
            return UnknownResult(
                Reason.FRAGMENT,
                "back-substitution zero test outside the projection",
            )
        return _accepted(self.ctx, proposal, context, extra)


CHECKERS = (SolveChecker,)


def register(builder: MathBuilder) -> None:
    for checker in CHECKERS:
        builder.register_checker(CheckerRegistration(checker.id, checker))
