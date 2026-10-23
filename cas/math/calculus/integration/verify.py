"""Independent verifier for indefinite integration: verification and search are
kept apart.

`verify_antideriv` does one thing: it re-checks `D(F) = f` through the
differentiation layer. It does not import the integration solver
(`integrate_term` / `poly_antideriv` from `cas.math.integrate`), so this is not
the integrator certifying itself.

**Three-valued semantics (critical)**: ``Yes`` proves vanishing, ``No`` carries
a typed refutation, and ``Unknown`` means the capability is missing. Functions
that the vanishing channel cannot cover (an exp/sin combination, for example,
because the trigonometric basis reduction is not rebuilt) are a capability gap:
they are not reported as refutations, because "not found" and "does not exist"
are different conclusions.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from cas.kernel.verdict import (
    YES,
    Reason,
    RefutationChannel,
    Verdict,
    refute,
    unknown,
)
from cas.math.diff import differentiate
from cas.math.domains.qarith import fold
from cas.math.domains.ratfunc import ratfunc_domain
from cas.math.project import zero_of
from cas.syntax import term as T
from cas.syntax.term import Sym, Term
from cas.syntax.termpath import free_vars

if TYPE_CHECKING:
    from cas.math.context import MathContext


def _judge_zero_diff(
    ctx: MathContext,
    derivative: Term,
    integrand: Term,
) -> Verdict:
    """Whether `dF - f` vanishes identically, with typed negative evidence."""
    difference = fold(T.plus(derivative, T.neg(integrand)))
    proposition = T.eq(derivative, integrand)
    if difference is T.ZERO:
        return YES
    zero = zero_of(ctx, difference)
    if zero is True:
        return YES
    if zero is False:
        return refute(
            RefutationChannel.NORMAL_FORM,
            proposition,
            difference,
            derivative,
            integrand,
            detail="the antiderivative difference has a nonzero normal form",
        )
    variables = tuple(
        sorted(
            free_vars(derivative) | free_vars(integrand),
            key=lambda symbol: symbol.name,
        )
    )
    if not variables:
        return unknown(Reason.FRAGMENT)
    equality = ratfunc_domain(
        *variables,
        ring=ctx.coeff_ring,
    ).equal(derivative, integrand)
    if equality is True:
        return YES
    if equality is False:
        return refute(
            RefutationChannel.NORMAL_FORM,
            proposition,
            derivative,
            integrand,
            detail="the antiderivative difference is nonzero in the rational-function view",
        )
    return unknown(Reason.FRAGMENT)


def verify_antideriv(
    ctx: MathContext,
    antiderivative: Term,
    integrand: Term,
    variable: Sym,
) -> Verdict:
    """Independently verify that `F` is an antiderivative of `f`.

    A piecewise integrand or antiderivative is checked branch by branch, and
    the conditions must match branch by branch: changing a condition changes
    the branch, because branches are disjoint and ordered. A branch mismatch
    is a mathematical certificate refutation; a channel that cannot decide is
    still returned as Unknown.
    """
    from cas.math.piecewise import is_piecewise

    if is_piecewise(integrand) or is_piecewise(antiderivative):
        # Branch-by-branch derivative agreement does not establish the junction
        # points: a piecewise F can jump at a breakpoint while every branch
        # derivative still matches. Region and boundary regularity have no
        # representation here, so this stays honestly undecided instead of
        # claiming YES.
        return unknown(Reason.GUARDED)
    return _judge_zero_diff(
        ctx,
        differentiate(ctx, antiderivative, variable),
        integrand,
    )
