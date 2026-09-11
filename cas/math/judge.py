"""Back-substitution judge: the atom of the verification system.

The sole authority on "is this candidate value a solution" lives here:
substitute, fold, decide vanishing. Vanishing goes through the domain
projection's normal form; when piecewise subterms are present, the term is first
collapsed by ordered first-match (a numeric point falls in at most one branch,
so the value is unique and vanishing is unambiguous).

Design obligations implemented here:
· verifier and solver are two independent implementations. This module is the
   verifier: it only back-substitutes and never re-runs a solution formula. The
   solver lives in cas/tactics and the two share no code path.
· undecided is not a pass: when vanishing cannot be decided the result is None
   and the caller honestly reports undecided, never treating None as true or
   false.
· outside the domain is not undecided but "not a solution": a point equation
   collapsing to Undefined has no value, which is an evidenced refutation, so
   the result is False rather than None.

Consolidation note: this judge used to be split across two places, a private
method on the workflow and an inline copy in the REPL's check command, and their
channel orders had already diverged (the REPL tried exact ring evaluation first
and only fell back to piecewise-aware vanishing, while the workflow used the
latter only). The authority now lives here: vanishing always goes through
zero_of, which covers strictly more than ring-level exact evaluation, and exact
evaluation is used only to obtain a displayed value, never to decide.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.syntax.term import Expr
from cas.kernel.verdict import Verdict, YES, NO, unknown
from cas.math.qarith import fold, eval_exact, EvalNumError
from cas.math.project import zero_of


# ---------------------------------------------------------------------------
# Structural probes
# ---------------------------------------------------------------------------

def has_piecewise(t) -> bool:
    """Whether the term contains a piecewise subterm, which decides whether the
    point-collapse channel is needed."""
    from cas.math.piecewise import is_piecewise
    if is_piecewise(t):
        return True
    if isinstance(t, Expr):
        return any(has_piecewise(a) for a in t.args)
    return False


def has_undef(t) -> bool:
    """Whether Undefined occurs in the term, meaning the point is outside the
    domain."""
    if t is T.SP("Undefined"):
        return True
    if isinstance(t, Expr):
        return any(has_undef(a) for a in t.args)
    return False


# ---------------------------------------------------------------------------
# Vanishing
# ---------------------------------------------------------------------------

def is_zero(t) -> bool | None:
    """Piecewise-aware vanishing test: an ordinary term is decided by the domain
    normal form, a term with piecewise subterms is point-collapsed first.

    Returns True / False / None, where None means undecidable and the caller
    must honestly report undecided. A point that collapses to Undefined is
    outside the domain, so the equation has no value there: not a solution,
    hence False.
    """
    if not has_piecewise(t):
        return zero_of(t)
    from cas.math.piecewise import collapse        # deferred: piecewise consumes the decision layer
    from cas.kernel.scope import Assumptions
    c = collapse(t, Assumptions())
    if c is None:
        return None                           # branch selection undecided
    if has_undef(c):
        return False                          # outside the domain: no value, not a solution
    return zero_of(fold(c))


# ---------------------------------------------------------------------------
# Back-substitution
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class BackSub:
    """Back-substitution result.

    · diff   the folded difference of the two sides, for display and evidence
    · zero   the verdict: True is a solution / False is not / None undecided
    · exact  the exact rational value of the difference, non-None only when
             computable at the ring level (display only, never a verdict)
    """
    diff: object
    zero: bool | None
    exact: object | None


def back_substitute(eq, var, value) -> BackSub:
    """Substitute var := value into the equation and return the difference and
    the vanishing verdict.

    Only the difference of the two sides is used; no solution formula is
    re-run. The vanishing authority is is_zero (the domain normal form) and
    `exact` is for display only. Both are exact arithmetic, so no floats are
    involved.
    """
    lhs, rhs = eq.args
    diff = fold(T.plus(T.subst(lhs, {var: value}),
                       T.neg(T.subst(rhs, {var: value}))))
    try:
        v = eval_exact(diff, {})
    except EvalNumError:
        v = None
    return BackSub(diff=diff, zero=is_zero(diff), exact=v)


# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class GuardCheck:
    """The back-substitution verdict for one guard."""
    guard: object       # the original guard term
    subst: object       # the guard after substitution
    verdict: Verdict    # the decision pipeline's verdict


def guard_report(guards, var, value, ctx=None) -> tuple[GuardCheck, ...]:
    """Back-substitute each guard and hand it to the decision pipeline, covering
    all predicate heads and compound propositions with no whitelist.

    A guard is not an optional extra check: a solution is a solution only where
    its guards hold. If any guard is No or undecided, the whole thing cannot be
    reported as verified.
    """
    from cas.math.decide import decide
    from cas.kernel.scope import Assumptions
    if ctx is None:
        ctx = Assumptions()
    out = []
    for g in guards:
        gsub = fold(T.subst(g, {var: value}))
        out.append(GuardCheck(guard=g, subst=gsub, verdict=decide(gsub, ctx)))
    return tuple(out)


def verify_solution(eq, var, value, guards=(), ctx=None) -> Verdict:
    """Full decision: back-substitution vanishing plus all guards holding; only
    both passing makes it a solution.

    The three exits align with the decision discipline:
    · vanishing is False, or any guard is No        -> NO
    · vanishing is None, or any guard is undecided   -> Unknown
    · vanishing is True and every guard is Yes       -> YES
    """
    bs = back_substitute(eq, var, value)
    if bs.zero is False:
        return NO
    checks = guard_report(guards, var, value, ctx)
    if any(c.verdict is NO for c in checks):
        return NO
    if bs.zero is None or any(c.verdict is not YES for c in checks):
        return unknown()
    return YES
