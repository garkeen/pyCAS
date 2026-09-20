"""Independent verifier for indefinite integration: verification and search are
kept apart.

`verify_antideriv` does one thing: it re-checks `D(F) = f` through the
differentiation layer. It does not import the integration solver
(`integrate_term` / `poly_antideriv` from `cas.math.integrate`), so this is not
the integrator certifying itself.

It used to share a module with the solver, and the checker imported the verifier
from that one module: a solver and a verifier living in the same module is exactly
the structure that must be avoided, and a checker must not live in, or import
from, the module holding the search algorithm it verifies. They are now separate.

**Three-valued semantics (critical)**: True proves vanishing, False proves
non-vanishing, None means the capability is missing and the result is undecided.
Functions that the vanishing channel cannot cover (an exp/sin combination, for
example, because the trigonometric basis reduction is not rebuilt) are a capability
gap: they must not be reported as refutations, because "not found" and "does not
exist" are two different conclusions.
"""

from cas.syntax import term as T
from cas.syntax.term import Sym
from cas.math.project import zero_of
from cas.math.domains.ratfunc import ratfunc_domain
from cas.math.diff import differentiate
from cas.math.domains.qarith import fold


def _judge_zero_diff(ctx, dF, f):
    """Whether `dF - f` vanishes identically. **Three-valued**: True proves
    vanishing, False proves non-vanishing, None is undecided.

    Undecided must be separated from non-vanishing: a function the vanishing
    channel cannot cover is a capability gap, not a refutation. Reporting None as
    False would forge a refutation, and an honest refusal when capability is
    missing is required instead.
    """
    diff = fold(T.plus(dF, T.neg(f)))
    if diff is T.ZERO:
        return True
    z = zero_of(ctx, diff)
    if z is True:
        return True
    if z is False:
        return False
    allv = tuple(sorted(T.free_vars(dF) | T.free_vars(f),
                        key=lambda s: s.name))
    if not allv:
        return None
    r = ratfunc_domain(*allv, ring=ctx.coeff_ring).equal(dF, f)
    if r is True:
        return True
    if r is False:
        return False                          # both are domain members and differ: a real refutation
    return None                               # non-member (transcendental): outside the vanishing channel


def verify_antideriv(ctx, F, f, x: Sym):
    """Independently verify that `F` is an antiderivative of `f`, with no
    dependence on the integrator.

    Returns True / False / None (undecided). A piecewise integrand or
    antiderivative is checked branch by branch, and the conditions must match
    branch by branch: changing a condition changes the branch, because branches
    are disjoint and ordered.
    """
    from cas.math.piecewise import is_piecewise, fold_nested, branches
    if is_piecewise(f) or is_piecewise(F):
        ff = fold_nested(f)
        FF = fold_nested(F)
        bf, bF = branches(ff), branches(FF)
        if len(bf) != len(bF):
            return False
        unknown = False
        for (vf, cf), (vF, cF) in zip(bf, bF):
            if cf is not cF:
                return False
            r = _judge_zero_diff(ctx, differentiate(ctx, vF, x), vf)
            if r is False:
                return False
            if r is None:
                unknown = True
        return None if unknown else True
    return _judge_zero_diff(ctx, differentiate(ctx, F, x), f)
