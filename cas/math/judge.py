"""Back-substitution judge: the atom of the verification system.

The sole authority on "is this candidate value a solution" lives here:
substitute, fold, decide vanishing. Vanishing goes through the domain
projection's normal form; when piecewise subterms are present, the term is
first collapsed by ordered first-match (a numeric point falls in at most one
branch, so the value is unique and vanishing is unambiguous).

Design obligations implemented here:
· verifier and solver are two independent implementations. This module is the
  verifier: it only back-substitutes and never re-runs a solution formula. The
  solver lives in cas/tactics and the two share no code path.
· undecided is not a pass: when vanishing cannot be decided the result is an
  ``Unknown`` verdict and the caller reports it honestly.
· outside the domain is not silently called nonzero. A point equation that
  collapses to ``Undefined`` is a domain refutation, while a term outside the
  projection remains ``Unknown``.

Consolidation note: this judge used to be split across two places, a private
method on the workflow and an inline copy in the REPL's check command, and
their channel orders had already diverged (the REPL tried exact ring evaluation
first and only fell back to piecewise-aware vanishing, while the workflow used
the latter only). The authority now lives here: vanishing always goes through
zero_of, which covers strictly more than ring-level exact evaluation, and
exact evaluation is retained as a separate, typed refutation channel when it
is the only available proof.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction

from cas.kernel.scope import Assumptions
from cas.kernel.verdict import (
    YES,
    Reason,
    RefutationChannel,
    Verdict,
    refute,
    unknown,
)
from cas.math.context import MathContext
from cas.math.domains.qarith import EvalNumError, eval_exact, fold
from cas.math.project import zero_of
from cas.syntax import term as T
from cas.syntax.term import Expr, Sym, Term
from cas.syntax.termpath import subst

# ---------------------------------------------------------------------------
# Structural probes
# ---------------------------------------------------------------------------


def has_piecewise(term: Term) -> bool:
    """Whether the term contains a piecewise subterm."""
    from cas.math.piecewise import is_piecewise

    if is_piecewise(term):
        return True
    if isinstance(term, Expr):
        return any(has_piecewise(argument) for argument in term.args)
    return False


def has_undef(term: Term) -> bool:
    """Whether Undefined occurs anywhere in the term."""
    if term is T.SP("Undefined"):
        return True
    if isinstance(term, Expr):
        return any(has_undef(argument) for argument in term.args)
    return False


# ---------------------------------------------------------------------------
# Vanishing
# ---------------------------------------------------------------------------


def _zero_proposition(term: Term) -> Term:
    return T.eq(term, T.ZERO)


def _is_zero(
    ctx: MathContext,
    term: Term,
    assumptions: Assumptions | None,
    proposition: Term,
) -> Verdict:
    """Internal zero channel with an explicit claim proposition."""
    if not has_piecewise(term):
        if has_undef(term):
            return refute(
                RefutationChannel.DOMAIN,
                proposition,
                term,
                detail="the value is Undefined outside its domain",
            )
        result = zero_of(ctx, term)
        if result is True:
            return YES
        if result is False:
            return refute(
                RefutationChannel.NORMAL_FORM,
                proposition,
                term,
                T.ZERO,
                detail="the projected term has a nonzero domain normal form",
            )
        return unknown(Reason.FRAGMENT)

    from cas.math.piecewise import ResidualSelection, collapse, select

    frame = Assumptions() if assumptions is None else assumptions
    selection = select(ctx, term, frame)
    if isinstance(selection, ResidualSelection):
        return unknown(selection.reason)
    collapsed = collapse(ctx, selection.value, frame)
    if collapsed is None:
        return unknown(Reason.GUARDED)
    if has_undef(collapsed):
        return refute(
            RefutationChannel.DOMAIN,
            proposition,
            collapsed,
            term,
            detail="the back-substituted piecewise value is Undefined outside its domain",
            causes=selection.refutations,
        )
    result = zero_of(ctx, fold(collapsed))
    if result is True:
        return YES
    if result is False:
        return refute(
            RefutationChannel.NORMAL_FORM,
            proposition,
            collapsed,
            T.ZERO,
            detail="the selected piecewise value has a nonzero domain normal form",
        )
    return unknown(Reason.FRAGMENT)


def is_zero(
    ctx: MathContext,
    term: Term,
    assumptions: Assumptions | None = None,
) -> Verdict:
    """Return the exact zero verdict in the caller's assumption frame."""
    return _is_zero(ctx, term, assumptions, _zero_proposition(term))


# ---------------------------------------------------------------------------
# Back-substitution
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class BackSub:
    """Back-substitution result.

    · ``diff``       the folded difference of the two sides, for display
    · ``verdict``    the typed zero verdict, including its original evidence
    · ``exact``      the exact rational value when ring evaluation can produce
                     one; it is not silently substituted for an Unknown
    """

    diff: Term
    verdict: Verdict
    exact: Fraction | None


def back_substitute(
    ctx: MathContext,
    equation: Expr,
    variable: Sym,
    value: Term,
    assumptions: Assumptions | None = None,
) -> BackSub:
    """Back-substitute and decide the difference in the caller's frame."""
    left, right = equation.args
    difference = fold(
        T.plus(
            subst(left, {variable: value}),
            T.neg(subst(right, {variable: value})),
        )
    )
    try:
        exact = eval_exact(difference, {})
    except EvalNumError:
        exact = None

    zero_verdict = _is_zero(ctx, difference, assumptions, equation)
    if zero_verdict.is_yes() or zero_verdict.is_no():
        return BackSub(diff=difference, verdict=zero_verdict, exact=exact)

    # A closed exact rational evaluation is an independent, sound proof of
    # non-vanishing.  It is used only when the normal-form channel is Unknown;
    # an existing normal-form refutation keeps its original channel and detail.
    if exact is not None and exact != 0:
        exact_verdict = refute(
            RefutationChannel.EXACT_COMPARISON,
            equation,
            difference,
            T.N(exact),
            detail=f"exact evaluation is nonzero: {exact}",
        )
        return BackSub(diff=difference, verdict=exact_verdict, exact=exact)
    return BackSub(diff=difference, verdict=zero_verdict, exact=exact)


# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class GuardCheck:
    """The back-substitution verdict for one guard."""

    guard: Term
    substituted: Term
    verdict: Verdict


def guard_report(
    ctx: MathContext,
    guards: Sequence[Term],
    variable: Sym,
    value: Term,
    assumptions: Assumptions | None = None,
) -> tuple[GuardCheck, ...]:
    """Back-substitute each guard and hand it to the decision pipeline, covering
    all predicate heads and compound propositions with no whitelist.

    A guard is not an optional extra check: a solution is a solution only where
    its guards hold. If any guard is No or undecided, the whole thing cannot be
    reported as verified. The math context is the first argument; the trailing
    `assumptions` are the caller's scope assumptions.
    """
    from cas.math.decide import decide

    frame = Assumptions() if assumptions is None else assumptions
    output: list[GuardCheck] = []
    for guard in guards:
        substituted = fold(subst(guard, {variable: value}))
        output.append(
            GuardCheck(
                guard=guard,
                substituted=substituted,
                verdict=decide(ctx, substituted, frame),
            )
        )
    return tuple(output)


def verify_solution(
    ctx: MathContext,
    equation: Expr,
    variable: Sym,
    value: Term,
    guards: Sequence[Term] = (),
    assumptions: Assumptions | None = None,
) -> Verdict:
    """Verify vanishing and all guards without replacing their evidence.

    A domain/normal-form/exact refutation and a guard refutation remain
    distinguishable. Unknown from either channel remains Unknown; it is never
    converted into a mathematical No.
    """
    substitution = back_substitute(
        ctx,
        equation,
        variable,
        value,
        assumptions,
    )
    if substitution.verdict.is_no():
        return substitution.verdict
    checks = guard_report(
        ctx,
        guards,
        variable,
        value,
        assumptions,
    )
    for check in checks:
        if check.verdict.is_no():
            return check.verdict
    if substitution.verdict.is_unknown():
        return substitution.verdict
    for check in checks:
        if check.verdict.is_unknown():
            return check.verdict
    return YES
