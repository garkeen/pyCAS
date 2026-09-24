"""Differentiation checkers.

Independent cross-check: the **domain-layer derivative** (a different
implementation) re-checks the term-layer differentiation result. An equation
predecessor is always refuted, because differentiating both sides preserves no
truth (from the point solution x = 3 one would "derive" 1 = 0). When the source is
outside the projection domain there is no independent channel, so the result is
honestly undecided rather than passing itself off as verified.
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
from cas.kernel.verdict import (
    YES,
    No,
    Reason,
    RefutationChannel,
    Unknown,
    Verdict,
    refute,
    unknown,
)
from cas.math.base.checkers import (
    _defined,
    _expand,
    _is_piecewise,
    _ok,
    _one_conclusion,
    _payload,
    _premise,
)
from cas.math.builder import CheckerRegistration, MathBuilder
from cas.math.domains.poly import Poly, p_deriv, to_term
from cas.math.domains.qarith import fold
from cas.math.domains.ratfunc import rf_deriv, rf_from_term, rf_to_term
from cas.math.project import Projected, project
from cas.syntax import term as T
from cas.syntax.term import Sym, Term
from cas.syntax.termpath import free_vars
from cas.workflow.command import DiffPayload

if TYPE_CHECKING:
    from cas.math.context import MathContext


def _element_deriv(hit: Projected, variable: Sym) -> Term | None:
    """The domain-layer derivative of a projected element as an interned term, or
    None when the domain exposes no independent channel for it.

    Dispatch is by capability, never by Python type. When the domain returns the
    element itself as a polynomial through `element_as_poly`, the polynomial
    derivative applies. Otherwise the element is a genuine fraction of a domain
    that declares a rational-function variable view: the projection's own term
    is read as a rational function of those variables and differentiated by the
    quotient rule. A domain that exposes only the documented protocol declares
    no variable view at all, so the answer is None (honestly undecided), never a
    field read the domain does not declare.
    """
    domain = hit.domain
    element = hit.element
    if element is None:
        return None
    polynomial = domain.element_as_poly(element)
    if polynomial is not None:
        variables, ring = domain.vars, domain.ring
        if variables is None or ring is None:
            return None
        if variable not in variables:
            return T.ZERO
        concrete = Poly(polynomial.vars, polynomial.monos)
        return to_term(ring, p_deriv(ring, concrete, variables.index(variable)))
    variables, ring = domain.vars, domain.ring
    if variables is None or ring is None:
        return None
    rational = rf_from_term(ring, hit.term, variables)
    if rational is None:
        return None
    if variable not in variables:
        return T.ZERO
    return rf_to_term(
        ring,
        rf_deriv(ring, rational, variables.index(variable)),
    )


def _cross_diff(
    ctx: MathContext,
    source: Term,
    result: Term,
    variable: Sym,
) -> Verdict:
    """Cross-check one term through the domain-layer derivative.

    ``Unknown`` means the source is outside the projection domain, or its
    projected element is a representation the cross-check has no independent
    channel for. A mismatch is a typed mathematical refutation, never a string
    compressed into an operational rejection.
    """
    expected: Term
    hit = project(ctx, source)
    if hit is None:
        return unknown(Reason.FRAGMENT)
    if hit.element is None:
        expected = T.ZERO
    else:
        expected_term = _element_deriv(hit, variable)
        if expected_term is None:
            return unknown(Reason.FRAGMENT)
        expected = expected_term
    from cas.math.domains.ratfunc import ratfunc_domain

    variables = tuple(
        sorted(
            free_vars(expected) | free_vars(result),
            key=lambda symbol: symbol.name,
        )
    )
    if not variables:
        difference = fold(T.plus(expected, T.neg(result)))
        if difference is T.ZERO:
            return YES
        return refute(
            RefutationChannel.NORMAL_FORM,
            T.eq(expected, result),
            expected,
            result,
            difference,
            detail="the domain-layer derivative differs from the term-layer result",
        )
    rational = ratfunc_domain(*variables, ring=ctx.coeff_ring)
    equality = rational.equal(expected, result)
    if equality is True:
        return YES
    if equality is False:
        return refute(
            RefutationChannel.NORMAL_FORM,
            T.eq(expected, result),
            expected,
            result,
            detail="the domain-layer derivative differs in the rational-function view",
        )
    return unknown(Reason.FRAGMENT)


class DiffChecker:
    id = "calculus.derivative"

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
        if T.is_eq(pred):
            return Rejected(
                Reason.FRAGMENT,
                "an equation predecessor cannot be differentiated",
            )
        pred = _expand(context, pred)
        content = _expand(context, content)
        d = _payload(proposal, DiffPayload)
        if d is None:
            return Rejected(Reason.FRAGMENT, "calculus.derivative requires a diff payload")
        x = d.var
        if _defined(context, x):
            # A definition is an alias, not a variable: differentiating with
            # respect to it is not defined (the expansion has no such symbol).
            return Rejected(
                Reason.FRAGMENT,
                f"cannot differentiate with respect to a defined symbol: {x}",
            )
        if _is_piecewise(pred):
            from cas.math.piecewise import branches, fold_nested

            if not _is_piecewise(content):
                return UnknownResult(
                    Reason.FRAGMENT,
                    "piecewise source with a non-piecewise result: no independent channel",
                )
            source_branches = branches(fold_nested(pred))
            result_branches = branches(fold_nested(content))
            if len(source_branches) != len(result_branches):
                return UnknownResult(
                    Reason.FRAGMENT,
                    "different branch counts; not pretending to refute",
                )
            for (source_value, source_condition), (
                result_value,
                result_condition,
            ) in zip(source_branches, result_branches):
                if source_condition is not result_condition:
                    return UnknownResult(Reason.FRAGMENT, "branch conditions differ")
                result = _cross_diff(
                    self.ctx,
                    source_value,
                    result_value,
                    x,
                )
                if isinstance(result, No):
                    return RefutationRejected(result.evidence)
                if isinstance(result, Unknown):
                    return UnknownResult(
                        Reason.FRAGMENT,
                        "this branch is outside the projection domain",
                    )
            return _ok(self.ctx, proposal, context)
        result = _cross_diff(self.ctx, pred, content, x)
        if isinstance(result, No):
            return RefutationRejected(result.evidence)
        if isinstance(result, Unknown):
            return UnknownResult(
                Reason.FRAGMENT,
                "source is outside the projection domain: no independent channel",
            )
        return _ok(self.ctx, proposal, context)


CHECKERS = (DiffChecker,)


def register(builder: MathBuilder) -> None:
    for checker in CHECKERS:
        builder.register_checker(CheckerRegistration(checker.id, checker))
