"""Integration skeleton: the first honestly decidable fragment plus an
independent verifier.

Scope, all exact, no heuristics and no approximation:
· indefinite integration of polynomial integrands (power rule); piecewise
  integrands are integrated branch by branch. Proper rational functions need
  Hermite reduction and transcendental ones need Risch; neither is built, so
  they raise IntegrateError.
· definite integration of [a, b] follows the domain-first discipline: intersect
  the domain with [a, b], never integrate across a gap as if it were 0, and
  refuse when a cell is undefined. A piecewise integrand is summed over its open
  cells.

**This module contains the solver only.** The independent verifier (which
re-checks D(F) = f through the differentiation layer) lives in
`cas/math/calculus/integration/verify.py`: verification and search are kept
apart, and a checker must not live in, or import from, the module holding the
search algorithm it verifies.

Honest boundaries:
· proper rational functions need Hermite reduction and transcendental ones need
  Risch, neither is built, so they refuse honestly;
· integration limits must be rational (algebraic limits need an algebraic
  extension, not built);
· a breakpoint at an irrational root is refused (it needs exact location in an
  algebraic extension);
· improper behaviour at an open endpoint or a point hole needs a limit layer,
  which is not built, so it is refused.
"""

from cas.syntax import term as T
from cas.syntax.term import Sym
from cas.errors import IntegrateError
from cas.kernel.verdict import Reason
from cas.math.project import project
from cas.math.domains.poly import Poly, to_term, _norm
from cas.math.domains.qarith import fold

_UNDEF = T.SP("Undefined")


# ---------------------------------------------------------------------------
# Indefinite integration: the polynomial fragment
# ---------------------------------------------------------------------------

def poly_antideriv(ring, p: Poly, var_i: int) -> Poly:
    """Integral of sum(c * x_i^k) = sum(c/(k+1) * x_i^(k+1)), term by term with
    an exact rational power rule."""
    d = {}
    for k, c in p.monos:
        e = k[var_i]
        nk = tuple(kj + (1 if j == var_i else 0) for j, kj in enumerate(k))
        d[nk] = ring.div_exact(c, ring.from_int(e + 1))
    return _norm(ring, p.vars, d)


def integrate_term(f, x: Sym):
    """The integral of f with respect to x: direct integration on the polynomial
    fragment, branch by branch for a piecewise integrand, and an honest refusal
    otherwise.

    Returns one antiderivative, with no constant of integration: on a
    disconnected domain the constants of the connected components are
    independent, see the piecewise case."""
    from cas.math.piecewise import is_piecewise
    if is_piecewise(f):
        return integrate_piecewise_indefinite(f, x)
    hit = project(f)
    if hit is None:
        raise IntegrateError("integrand is outside the rational/polynomial/"
                             "rational-function domains", Reason.FRAGMENT)
    if hit.element is None:
        return T.times(f, x)                    # integral of a constant c is c*x
    el = hit.element
    vs = hit.domain.vars
    if vs is None:
        # The domain declares no variable view for its elements, so there is no
        # honest way to see the integrand as a polynomial in x; refusing here
        # names the domain instead of reading a field it may not have.
        raise IntegrateError(
            "integration is not available for the element representation of "
            f"{hit.domain.name}", Reason.FRAGMENT)
    if x not in vs:
        return T.times(f, x)                    # independent of x
    if isinstance(el, Poly):
        ring = hit.domain.ring
        return to_term(ring, poly_antideriv(ring, el, vs.index(x)))
    raise IntegrateError("proper rational integration needs Hermite reduction, "
                         "not built", Reason.FRAGMENT)


def integrate_piecewise_indefinite(f, x: Sym):
    """Integrate a piecewise integrand branch by branch, leaving conditions
    unchanged.

    On a disconnected domain the constants of integration of the connected
    components are independent, so a single +C would be wrong. The branch-wise
    antiderivative returned here omits those constants; verification only checks
    that differentiating each branch restores the integrand."""
    from cas.math.piecewise import fold_nested, branches, piecewise
    f = fold_nested(f)
    return piecewise([(integrate_term(v, x), c) for v, c in branches(f)])


# ---------------------------------------------------------------------------
# Definite integration
# ---------------------------------------------------------------------------

def _require_rational(t, tag):
    tf = fold(t)
    if not T.is_num(tf):
        raise IntegrateError(f"the {tag} of integration must be rational",
                             Reason.FRAGMENT)
    return T.num_val(tf)


def _ftc(F, x: Sym, a, b):
    """Newton-Leibniz: F(b) - F(a), with F a polynomial antiderivative evaluated
    exactly at the endpoints."""
    Fa = fold(T.subst(F, {x: T.N(a)}))
    Fb = fold(T.subst(F, {x: T.N(b)}))
    return fold(T.plus(Fb, T.neg(Fa)))


def _rat_iso(iso, tag):
    """An isolating interval to rational endpoints; an irrational root is
    refused. None means unbounded."""
    if iso is None:
        return None
    a, b = iso
    if a == b:
        return a
    raise IntegrateError(f"breakpoint at an irrational root needs exact location "
                         f"in an algebraic extension ({tag})", Reason.FRAGMENT)


def definite_integrate(f, x: Sym, a, b):
    """The definite integral of f with respect to x from a to b, with a and b
    rational terms. Never integrates across a gap as if it were 0, and refuses
    when the integrand is undefined."""
    ar = _require_rational(a, "lower limit")
    br = _require_rational(b, "upper limit")
    if ar > br:
        raise IntegrateError("lower limit is greater than upper limit")
    if ar == br:
        return T.ZERO                          # integral from a to a is 0
    from cas.math.piecewise import is_piecewise
    if is_piecewise(f):
        return _definite_piecewise(f, x, ar, br)
    F = integrate_term(f, x)
    return _ftc(F, x, ar, br)


def _definite_piecewise(f, x: Sym, a, b):
    """Piecewise definite integration: Newton-Leibniz on each open cell covering
    [a, b].

    Any cell intersecting [a, b] that is undefined (a gap or a point hole) causes
    a refusal. The interval is never quietly shrunk and a gap is never integrated
    to 0."""
    from cas.math.piecewise import domain_cells
    total = None
    for cell, val in domain_cells(f, x):
        lo = _rat_iso(cell.lo, "lower bound")
        hi = _rat_iso(cell.hi, "upper bound")
        if cell.kind == "point":
            r = lo
            if a <= r <= b and val is _UNDEF:
                raise IntegrateError(
                    "integrand has an undefined point hole in [a, b]; improper "
                    "integration needs a limit layer, not built", Reason.FRAGMENT)
            continue                                # a point cell has measure 0
        L = a if lo is None else max(a, lo)
        R = b if hi is None else min(b, hi)
        if L >= R:
            continue
        if val is _UNDEF:
            raise IntegrateError("integrand has a gap in [a, b]; refusing to "
                                 "integrate across it", Reason.FRAGMENT)
        t = _ftc(integrate_term(val, x), x, L, R)
        total = t if total is None else fold(T.plus(total, t))
    if total is None:
        raise IntegrateError("integration interval does not meet the domain: "
                             "undefined rather than 0", Reason.FRAGMENT)
    return total
