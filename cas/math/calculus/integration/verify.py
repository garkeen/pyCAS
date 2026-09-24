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
    No,
    Reason,
    RefutationChannel,
    Unknown,
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


def _mismatch(
    proposition: Term,
    detail: str,
    *witnesses: Term,
) -> No:
    return refute(
        RefutationChannel.DERIVATION,
        proposition,
        *witnesses,
        detail=detail,
    )


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
    from cas.math.piecewise import branches, fold_nested, is_piecewise

    if is_piecewise(integrand) or is_piecewise(antiderivative):
        flattened_integrand = fold_nested(integrand)
        flattened_antiderivative = fold_nested(antiderivative)
        integrand_branches = branches(flattened_integrand)
        antiderivative_branches = branches(flattened_antiderivative)
        proposition = T.eq(antiderivative, integrand)
        if len(integrand_branches) != len(antiderivative_branches):
            return _mismatch(
                proposition,
                "the antiderivative and integrand have different branch counts",
                antiderivative,
                integrand,
            )
        undecided = False
        for (value, condition), (candidate, candidate_condition) in zip(
            integrand_branches,
            antiderivative_branches,
        ):
            if condition is not candidate_condition:
                return _mismatch(
                    proposition,
                    "the antiderivative and integrand branch conditions differ",
                    condition,
                    candidate_condition,
                )
            verdict = _judge_zero_diff(
                ctx,
                differentiate(ctx, candidate, variable),
                value,
            )
            if isinstance(verdict, No):
                return verdict
            if isinstance(verdict, Unknown):
                undecided = True
        return unknown(Reason.FRAGMENT) if undecided else YES
    return _judge_zero_diff(
        ctx,
        differentiate(ctx, antiderivative, variable),
        integrand,
    )
