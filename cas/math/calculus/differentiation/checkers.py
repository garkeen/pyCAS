"""Differentiation checkers.

Independent cross-check: the **domain-layer derivative** (a different
implementation) re-checks the term-layer differentiation result. An equation
predecessor is always refuted, because differentiating both sides preserves no
truth (from the point solution x = 3 one would "derive" 1 = 0). When the source is
outside the projection domain there is no independent channel, so the result is
honestly undecided rather than passing itself off as verified.
"""

from cas.kernel.evidence import Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.math.domains.poly import p_deriv, to_term
from cas.math.domains.ratfunc import rf_deriv, rf_from_term, rf_to_term
from cas.math.domains.qarith import fold
from cas.math.project import project
from cas.math.base.checkers import (
    _defined, _expand, _is_piecewise, _ok, _one_conclusion, _premise,
)
from cas.syntax import term as T


def _element_deriv(hit, x):
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
    p = domain.element_as_poly(hit.element)
    if p is not None:
        # The element's own polynomial denotation, not its vanishing view.
        vs, ring = domain.vars, domain.ring
        if vs is None or ring is None:
            return None
        if x not in vs:
            return T.ZERO
        return to_term(ring, p_deriv(ring, p, vs.index(x)))
    vs, ring = domain.vars, domain.ring
    if vs is None or ring is None:
        return None
    rf = rf_from_term(ring, hit.term, vs)
    if rf is None:
        return None
    if x not in vs:
        return T.ZERO
    return rf_to_term(ring, rf_deriv(ring, rf, vs.index(x)))


def _cross_diff(ctx, src, got, x):
    """Cross-check one term: rebuild the expected value from the domain-layer
    derivative (a different implementation) and compare it with the term-layer
    result.

    None means the source is outside the projection domain, or its projected
    element is a representation the cross-check has no independent channel for
    (None is then the honest undecided result, never an AttributeError from
    reading fields of a representation the domain does not declare); True means
    the domain-layer rebuild equals the term-layer result in the
    rational-function field; False means they differ.
    """
    hit = project(ctx, src)
    if hit is None:
        return None
    if hit.element is None:
        expected = T.ZERO                      # a constant cell (Z/Q) differentiates to 0
    else:
        expected = _element_deriv(hit, x)
        if expected is None:
            return None
    from cas.math.domains.ratfunc import ratfunc_domain
    allv = tuple(sorted(T.free_vars(expected) | T.free_vars(got),
                        key=lambda s: s.name))
    if not allv:
        return True if fold(T.plus(expected, T.neg(got))) is T.ZERO else False
    rfd = ratfunc_domain(*allv, ring=ctx.coeff_ring)
    if rfd.equal(expected, got) is True:
        return True
    if rfd.equal(expected, got) is False:
        return False
    return None


class DiffChecker:
    id = "calculus.derivative"

    def __init__(self, ctx):
        self.ctx = ctx

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        if T.is_eq(pred):
            return Rejected(Reason.FRAGMENT, "an equation predecessor cannot be differentiated")
        pred = _expand(context, pred)
        content = _expand(context, content)
        d = proposal.evidence.payload
        x = d.var
        if _defined(context, x):
            # A definition is an alias, not a variable: differentiating with
            # respect to it is not defined (the expansion has no such symbol).
            return Rejected(Reason.FRAGMENT,
                            f"cannot differentiate with respect to a defined symbol: {x}")
        if _is_piecewise(pred):
            from cas.math.piecewise import fold_nested, branches
            if not _is_piecewise(content):
                return UnknownResult(Reason.FRAGMENT, "piecewise source with a non-piecewise result: no independent channel")
            sbs = branches(fold_nested(pred))
            gbs = branches(fold_nested(content))
            if len(sbs) != len(gbs):
                return UnknownResult(Reason.FRAGMENT, "different branch counts; not pretending to refute")
            for (sv, sc), (gv, gc) in zip(sbs, gbs):
                if sc is not gc:
                    return UnknownResult(Reason.FRAGMENT, "branch conditions differ")
                r = _cross_diff(self.ctx, sv, gv, x)
                if r is None:
                    return UnknownResult(Reason.FRAGMENT, "this branch is outside the projection domain")
                if r is not True:
                    return Rejected(Reason.FRAGMENT, "domain-layer derivative disagrees on this branch")
            return _ok(self.ctx, proposal, context)
        r = _cross_diff(self.ctx, pred, content, x)
        if r is None:
            return UnknownResult(Reason.FRAGMENT, "source is outside the projection domain: no independent channel")
        if r is not True:
            return Rejected(Reason.FRAGMENT, "domain-layer derivative disagrees with the term-layer result")
        return _ok(self.ctx, proposal, context)


CHECKERS = (DiffChecker,)


def register(builder) -> None:
    for cls in CHECKERS:
        builder.register_checker(cls.id, cls)
