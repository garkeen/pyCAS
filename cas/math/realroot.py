"""Univariate real root isolation: the projection skeleton of the simplest CAD.

All exact rational arithmetic, no approximation:
· a Cauchy bound encloses every real root;
· a Sturm sequence plus the number of sign variations gives the count of real
  roots in an open interval (Sturm's theorem);
· bisection isolates each real root into pairwise disjoint rational-endpoint
  intervals: an irrational root yields an open interval (the root is strictly
  inside, the endpoints are not roots), while a rational root is hit exactly and
  recorded as (r, r).

Implemented only for squarefree univariate polynomials over Q. This is the
foundation of the decidable fragment over real closed fields; it has nothing to
do with transcendental roots, which are undecidable.
"""

from fractions import Fraction as Fr

from cas.math.domains.poly import (Poly, p_deriv, p_neg, p_divmod_field,
                              p_gcd_univar)
from cas.math.domains.polytools import p_deg, p_lc, p_monic, p_div_exact


# ---------------------------------------------------------------------------
# Exact evaluation and sign
# ---------------------------------------------------------------------------

def p_eval_at(p: Poly, x0) -> Fr:
    """Exact value of a univariate sparse polynomial at a rational point
    (Horner)."""
    coefs = {}
    for k, c in p.monos:
        coefs[k[0]] = Fr(c)
    if not coefs:
        return Fr(0)
    deg = max(coefs)
    acc = Fr(0)
    for e in range(deg, -1, -1):
        acc = acc * x0 + coefs.get(e, Fr(0))
    return acc


def coef_sign(v) -> int:
    if v > 0:
        return 1
    if v < 0:
        return -1
    return 0


# ---------------------------------------------------------------------------
# Sturm sequence and sign variations
# ---------------------------------------------------------------------------

def sturm_sequence(ring, p: Poly):
    """The standard Sturm chain: p0 = p, p1 = p', p_{k+1} = -(p_{k-1} mod p_k)."""
    seq = [p, p_deriv(ring, p, 0)]
    while True:
        _, r = p_divmod_field(ring, seq[-2], seq[-1], 0)
        if r.is_zero():
            break
        seq.append(p_neg(ring, r))
    return seq


def sign_variations(seq, x0) -> int:
    """Number of sign variations of the Sturm chain at x0, evaluating term by
    term and ignoring zero terms."""
    prev = None
    changes = 0
    for q in seq:
        s = coef_sign(p_eval_at(q, x0))
        if s == 0:
            continue
        if prev is not None and s != prev:
            changes += 1
        prev = s
    return changes


def count_roots(seq, p: Poly, a, b) -> int:
    """Sturm's theorem: the number of distinct real roots in (a, b] equals
    V(a) - V(b).

    Zero terms are ignored in V, so the formula still counts correctly for open
    and closed endpoints when an endpoint is itself a root.
    """
    return sign_variations(seq, a) - sign_variations(seq, b)


def count_roots_open(seq, p: Poly, a, b) -> int:
    """Number of distinct real roots in the open interval (a, b); when the right
    endpoint is a root it is subtracted."""
    n = count_roots(seq, p, a, b)
    if coef_sign(p_eval_at(p, b)) == 0:
        n -= 1
    return n


# ---------------------------------------------------------------------------
# Cauchy bound and bisection isolation
# ---------------------------------------------------------------------------

def cauchy_bound(p: Poly) -> Fr:
    """Every real root has absolute value at most 1 + max|c_i/lc| for i < deg."""
    lc = Fr(p_lc(p, 0))
    m = Fr(0)
    top = p_deg(p, 0)
    for k, c in p.monos:
        if k[0] < top:
            v = abs(Fr(c) / lc)
            if v > m:
                m = v
    return Fr(1) + m


def _shrink(seq, p: Poly, iv):
    """Shrink a single-root isolating interval one step toward the root; a
    degenerate (r, r) is unchanged."""
    a, b = iv
    if a == b:
        return iv
    mid = (a + b) / 2
    if coef_sign(p_eval_at(p, mid)) == 0:
        return (mid, mid)                    # hit an exact rational root
    if count_roots_open(seq, p, a, mid) >= 1:
        return (a, mid)
    return (mid, b)


def _refine_gaps(seq, p: Poly, ivs):
    """Shrink touching or overlapping adjacent intervals until every adjacent
    pair has a strict gap."""
    changed = True
    while changed:
        changed = False
        for i in range(len(ivs) - 1):
            if ivs[i][1] >= ivs[i + 1][0]:
                ivs[i] = _shrink(seq, p, ivs[i])
                ivs[i + 1] = _shrink(seq, p, ivs[i + 1])
                changed = True
    return ivs


def _iso_open(seq, p: Poly, a, b, out):
    """Isolate every real root strictly inside the open interval (a, b); the
    endpoints a and b themselves are not counted."""
    n = count_roots_open(seq, p, a, b)
    if n == 0:
        return
    if n == 1:
        out.append((a, b))
        return
    mid = (a + b) / 2
    if coef_sign(p_eval_at(p, mid)) == 0:
        out.append((mid, mid))            # exact rational root
        _iso_open(seq, p, a, mid, out)
        _iso_open(seq, p, mid, b, out)
    else:
        _iso_open(seq, p, a, mid, out)
        _iso_open(seq, p, mid, b, out)


def squarefree_part(ring, p: Poly) -> Poly:
    """Squarefree part p / gcd(p, p'): the same root set, all roots simple."""
    if p_deg(p, 0) <= 0:
        return p
    g = p_gcd_univar(ring, p, p_deriv(ring, p, 0))
    if g.is_zero() or p_deg(g, 0) == 0:
        return p_monic(ring, p)
    return p_div_exact(ring, p_monic(ring, p), g)


def divisors(n):
    """Positive divisors of n, by trial division up to sqrt(n); the shared
    channel for enumerating rational-root candidates."""
    n = abs(n)
    if n == 0:
        return []
    out = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            if d != n // d:
                out.append(n // d)
        d += 1
    return out


def rational_roots(p: Poly):
    """The complete set of exact rational roots, by the rational root theorem,
    ascending and deduplicated.

    Clearing denominators gives integer coefficients, after which a rational
    root must be ±(factor of the constant term)/(factor of the leading
    coefficient). The finite candidate set is verified exactly one by one: this
    is a decidable fragment, not an approximation.
    """
    if p_deg(p, 0) <= 0:
        return []
    from math import gcd
    coefs = {k[0]: Fr(c) for k, c in p.monos}
    lcm = 1
    for c in coefs.values():
        lcm = lcm * c.denominator // gcd(lcm, c.denominator)
    ic = {e: int(coefs[e] * lcm) for e in coefs}
    roots = []
    while ic and ic.get(0, 0) == 0:          # root 0: reduce the degree one at a time
        roots.append(Fr(0))
        ic = {e - 1: c for e, c in ic.items() if e > 0}
    if not ic:
        return sorted(set(roots))
    deg = max(ic)
    a0 = ic.get(0, 0)
    an = ic[deg]
    cands = set()
    for d in divisors(a0):
        for e in divisors(an):
            cands.add(Fr(d, e))
            cands.add(Fr(-d, e))
    for r in cands:
        if coef_sign(p_eval_at(p, r)) == 0:
            roots.append(r)
    return sorted(set(roots))


def real_roots_intervals(ring, p: Poly):
    """Real root isolation for an arbitrary univariate polynomial.

    Rational roots are hit exactly by the rational root theorem as (r, r); they
    cut the real line into open intervals, and irrational roots are isolated by
    Sturm inside their own intervals (confined to the gaps, hence naturally
    disjoint from the rational roots). The result is ascending, pairwise
    disjoint, and strictly gapped between neighbours.
    """
    if p_deg(p, 0) <= 0:
        return []
    sf = squarefree_part(ring, p)
    seq = sturm_sequence(ring, sf)
    rat = rational_roots(sf)
    M = cauchy_bound(sf)
    ivs = [(r, r) for r in rat]
    bounds = [Fr(-M)] + rat + [Fr(M)]
    for i in range(len(bounds) - 1):
        _iso_open(seq, sf, bounds[i], bounds[i + 1], ivs)   # irrational roots in the gaps
    ivs.sort(key=lambda iv: iv[0])
    return _refine_gaps(seq, sf, ivs)
