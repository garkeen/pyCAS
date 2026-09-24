"""Tactics layer: concrete solving/simplification moves, fully independent of
the verifiers.

The verifier never re-runs the solver. The tactics layer hands over a
certificate (a solution, a normal form) and the workflow verifier only performs
an independent check for the derivation kind (back-substitution, domain
equality). A tactic failure raises TacticsError: refused honestly, never
degraded into a guess.
"""

from cas.syntax import term as T
from cas.syntax.term import Sym
from cas.errors import TacticsError
from cas.math.project import zero_of
from cas.math.linearform import linear_form, nonzero_condition, normalized


def _lin_core(ctx, diff, var: Sym):
    """Classify a difference and return the slope condition separately."""
    form = linear_form(ctx, diff, var)
    if form.kind == "linear":
        coefficient, constant = form.payload
        solution = normalized(ctx, T.times(T.neg(constant), T.pw(coefficient, T.MONE)))
        return ("linear", solution, nonzero_condition(coefficient))
    if form.kind == "zero":
        return ("zero", None, ())
    if form.kind in ("constant", "independent"):
        return ("nonzero", None, ())
    if form.kind in ("outside", "no_view"):
        return ("refuse", form.payload, ())
    return ("refuse", f"degree {form.payload} equation: only linear is supported", ())





def solve_linear_with_condition(ctx, content, var: Sym):
    """Return a candidate and the condition needed to divide by its slope."""
    if not (isinstance(content, T.Expr) and content.head.name == "Eq"):
        raise TacticsError("solve needs an equation")
    lhs, rhs = content.args
    kind, payload, condition = _lin_core(ctx, T.plus(lhs, T.neg(rhs)), var)
    if kind == "linear":
        return payload, condition
    if kind == "zero":
        raise TacticsError("identity: the solution set is everything, no unique solution")
    if kind == "nonzero":
        raise TacticsError("contradictory equation: independent of the variable and never zero")
    raise TacticsError(payload)


def solve_linear(ctx, content, var: Sym):
    """Return the linear candidate; conditions are available separately."""
    return solve_linear_with_condition(ctx, content, var)[0]


# ---------------------------------------------------------------------------
# Diophantine fragment: Z is the host of the decidable fragment; the general
# case is a theorem-level refusal.
# ---------------------------------------------------------------------------

def _integer_ring():
    """The host ring of the Diophantine fragment: a **Euclidean integral domain**
    (Z).

    Taken by capability rather than by hardcoding `Z_RING`: the algorithm
    declares that it needs a Euclidean non-field structure and the query matches
    it. If another structure with the same capabilities (such as the Gaussian
    integers) is added, this query fails loudly on an ambiguous match, forcing an
    explicit decision about which integral domain hosts the Diophantine
    fragment instead of letting import order or dict order choose.
    """
    from cas.math.domains.base import find_domain
    hits = find_domain(lambda d: d.is_euclidean and not d.is_field
                       and d.ring is not None)
    if len(hits) != 1:
        raise TacticsError(
            f"need a unique Euclidean integral domain, matched {[d.name for d in hits]}")
    return hits[0].ring


def solve_diophantine_linear(a: int, b: int, c: int):
    """Integer solutions of ax + by = c, by the extended Euclidean algorithm.

    Returns ((x0, y0), (dx, dy)): a particular solution and the period, so all
    solutions are (x0 + dx*t, y0 + dy*t) with t an integer. When gcd(a, b) does
    not divide c there is no solution and the call refuses.
    """
    g, s, t = _integer_ring().xgcd(a, b)
    if g == 0:
        if c != 0:
            raise TacticsError("0 = c != 0: no solution")
        return ((0, 0), (1, 0))            # 0 = 0: the whole plane, a trivial parametrization
    if c % g != 0:
        raise TacticsError(f"no integer solution: gcd({a},{b})={g} does not divide {c}")
    m = c // g
    return ((s * m, t * m), (b // g, -a // g))


def integer_roots(p, var):
    """All integer roots of a univariate polynomial with integer coefficients,
    by the rational root theorem.

    An integer root must divide the constant term, giving a complete finite
    candidate set verified exactly with Horner. Returns an ascending list.
    Non-integer coefficients are refused as outside the fragment.
    """
    if var not in p.vars:
        return []
    i = p.vars.index(var)
    others = [j for j in range(len(p.vars)) if j != i]
    coefs = {}
    for k, c in p.monos:
        if any(k[j] for j in others):
            raise TacticsError("involves other variables: only single-variable is supported")
        if getattr(c, "denominator", 1) != 1:
            raise TacticsError("non-integer coefficients: outside the integer-root fragment")
        coefs[k[i]] = int(c)
    if not coefs:
        return []
    roots = []
    while coefs.get(0, 0) == 0:            # x divides p: 0 is a root, reduce the degree
        roots.append(0)
        coefs = {e - 1: c for e, c in coefs.items() if e > 0}
        if not coefs:
            return roots
    deg = max(coefs)
    a0 = coefs[0]
    from cas.math.realroot import divisors
    cands = set()
    for d in divisors(a0):                 # integer root implies d | a0, O(sqrt|a0|)
        cands.update((d, -d))
    for r in sorted(cands):
        acc = coefs[deg]
        for e in range(deg - 1, -1, -1):   # Horner
            acc = acc * r + coefs.get(e, 0)
        if acc == 0:
            roots.append(r)
    return sorted(set(roots))


def solve_piecewise(ctx, f, x: Sym, target):
    """Solve the piecewise equation pw(...) = target: solve branch by branch and
    check membership in the branch condition.

    Each branch takes the branch-equation difference d = v - target (folded) and
    classifies it in two steps:
    · d contains no free variable x (closed form): decided by the vanishing
      channel -- identically zero means the whole branch region is a solution,
      provably nonzero means no contribution, undecided is recorded as a
      conditional solution;
    · d contains x: classified by `_lin_core` on the projection normal form (the
      difference of x+1 and x+1 contains x syntactically but projects to zero and
      still yields a region solution; the difference of x+1 and x projects to a
      constant and still contributes nothing) -- a linear case yields a
      candidate which is substituted into the branch condition and decided by the
      pipeline: accepted when it holds, discarded when it fails, recorded as
      conditional when undecided.

    Any branch outside the linear fragment causes a refusal: missing it could
    lose solutions, so completeness cannot be guaranteed.

    Returns {"points": [...], "regions": [...], "conditional": [(sol, cond)]}.
    """
    from cas.math.piecewise import fold_nested, branches, is_piecewise
    from cas.math.decide import decide
    from cas.kernel.scope import Assumptions
    from cas.kernel.verdict import YES, NO
    from cas.math.domains.qarith import fold
    if not is_piecewise(f):
        raise TacticsError("solve_piecewise needs a piecewise function")
    f = fold_nested(f)
    points, regions, conditional = [], [], []
    for v, c in branches(f):
        d = fold(T.plus(v, T.neg(target)))
        if x not in T.free_vars(d):
            z = zero_of(ctx, d)
            if z is True:
                regions.append(c)                 # branch equation holds identically
            elif z is None:
                conditional.append((None, c))     # identity undecided
            continue
        kind, payload, _condition = _lin_core(ctx, d, x)
        if kind == "zero":
            regions.append(c)                     # projects to zero (v == target)
            continue
        if kind == "nonzero":
            continue                              # branch equation never vanishes
        if kind == "refuse":
            raise TacticsError(
                f"branch equation is outside the linear fragment, completeness "
                f"cannot be guaranteed: {payload}")
        verdict = decide(ctx, fold(T.subst(c, {x: payload})), Assumptions())
        if verdict is YES:
            points.append(payload)
        elif verdict is NO:
            continue
        else:
            conditional.append((payload, c))
    return {"points": points, "regions": regions, "conditional": conditional}
