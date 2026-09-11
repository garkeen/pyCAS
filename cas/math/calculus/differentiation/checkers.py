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
from cas.math.domains.poly import Poly, p_deriv, to_term
from cas.math.domains.ratfunc import RatFunc, rf_deriv, rf_to_term
from cas.math.qarith import fold
from cas.math.project import project
from cas.math.base.checkers import (
    _is_piecewise, _ok, _one_conclusion, _premise,
)
from cas.syntax import term as T


def _cross_diff(src, got, x):
    """Cross-check one term: rebuild the expected value from the domain-layer
    derivative (a different implementation) and compare it with the term-layer
    result.

    None means the source is outside the projection domain (no independent
    channel, the caller treats it as undecided); True means the domain-layer
    rebuild equals the term-layer result in the rational-function field; False
    means they differ; anything else is honestly undecided.
    """
    hit = project(src)
    if hit is None:
        return None
    if hit.element is None:
        expected = T.ZERO                      # a constant cell (Z/Q) differentiates to 0
    else:
        vs = hit.domain.vars
        if x not in vs:
            expected = T.ZERO
        else:
            idx = vs.index(x)
            ring = hit.domain.ring
            if isinstance(hit.element, Poly):
                expected = to_term(ring, p_deriv(ring, hit.element, idx))
            elif isinstance(hit.element, RatFunc):
                expected = rf_to_term(ring, rf_deriv(ring, hit.element, idx))
            else:
                return None
    from cas.math.domains.ratfunc import ratfunc_domain
    allv = tuple(sorted(T.free_vars(expected) | T.free_vars(got),
                        key=lambda s: s.name))
    if not allv:
        return True if fold(T.plus(expected, T.neg(got))) is T.ZERO else False
    rfd = ratfunc_domain(*allv)
    if rfd.equal(expected, got) is True:
        return True
    if rfd.equal(expected, got) is False:
        return False
    return None


class DiffChecker:
    id = "calculus.derivative"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "missing predecessor")
        if T.is_eq(pred):
            return Rejected(Reason.FRAGMENT, "an equation predecessor cannot be differentiated")
        d = proposal.evidence.payload
        x = d.var
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
                r = _cross_diff(sv, gv, x)
                if r is None:
                    return UnknownResult(Reason.FRAGMENT, "this branch is outside the projection domain")
                if r is not True:
                    return Rejected(Reason.FRAGMENT, "domain-layer derivative disagrees on this branch")
            return _ok(proposal, context)
        r = _cross_diff(pred, content, x)
        if r is None:
            return UnknownResult(Reason.FRAGMENT, "source is outside the projection domain: no independent channel")
        if r is not True:
            return Rejected(Reason.FRAGMENT, "domain-layer derivative disagrees with the term-layer result")
        return _ok(proposal, context)


CHECKERS = (DiffChecker,)


def register(store) -> None:
    for cls in CHECKERS:
        ck = cls()
        if ck.id not in store.checkers:
            store.checkers.register(ck.id, ck)
