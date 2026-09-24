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

from collections.abc import Sequence
from fractions import Fraction as Fr
from typing import TypeAlias

from cas.math.domains.base import Ring
from cas.math.domains.poly import Poly, p_deriv, p_divmod_field, p_gcd_univar, p_neg
from cas.math.domains.polytools import p_deg, p_div_exact, p_lc, p_monic

RootInterval: TypeAlias = tuple[Fr, Fr]
SturmSequence: TypeAlias = list[Poly]

# ---------------------------------------------------------------------------
# Exact evaluation and sign
# ---------------------------------------------------------------------------


def p_eval_at(ring: Ring, p: Poly, x0: Fr) -> Fr:
    """Exact value of a univariate sparse polynomial at a rational point."""
    coefs: dict[int, Fr] = {}
    for k, c in p.monos:
        coefs[k[0]] = ring.to_fraction(c)
    if not coefs:
        return Fr(0)
    deg = max(coefs)
    acc = Fr(0)
    for e in range(deg, -1, -1):
        acc = acc * x0 + coefs.get(e, Fr(0))
    return acc


def coef_sign(v: Fr) -> int:
    if v > 0:
        return 1
    if v < 0:
        return -1
    return 0


# ---------------------------------------------------------------------------
# Sturm sequence and sign variations
# ---------------------------------------------------------------------------


def sturm_sequence(ring: Ring, p: Poly) -> SturmSequence:
    """The standard Sturm chain: p0 = p, p1 = p', p_{k+1} = -(p_{k-1} mod p_k)."""
    seq: SturmSequence = [p, p_deriv(ring, p, 0)]
    while True:
        _, r = p_divmod_field(ring, seq[-2], seq[-1], 0)
        if r.is_zero():
            break
        seq.append(p_neg(ring, r))
    return seq


def sign_variations(ring: Ring, seq: Sequence[Poly], x0: Fr) -> int:
    """Number of sign variations of the Sturm chain at x0."""
    prev: int | None = None
    changes = 0
    for q in seq:
        sign = coef_sign(p_eval_at(ring, q, x0))
        if sign == 0:
            continue
        if prev is not None and sign != prev:
            changes += 1
        prev = sign
    return changes


def count_roots(ring: Ring, seq: Sequence[Poly], p: Poly, a: Fr, b: Fr) -> int:
    """Sturm's theorem: the number of distinct real roots in (a, b]."""
    return sign_variations(ring, seq, a) - sign_variations(ring, seq, b)


def count_roots_open(ring: Ring, seq: Sequence[Poly], p: Poly, a: Fr, b: Fr) -> int:
    """Number of distinct real roots in the open interval (a, b)."""
    roots = count_roots(ring, seq, p, a, b)
    if coef_sign(p_eval_at(ring, p, b)) == 0:
        roots -= 1
    return roots


# ---------------------------------------------------------------------------
# Cauchy bound and bisection isolation
# ---------------------------------------------------------------------------


def cauchy_bound(ring: Ring, p: Poly) -> Fr:
    """Every real root has absolute value at most 1 + max|c_i/lc|."""
    leading = ring.to_fraction(p_lc(p, 0))
    maximum = Fr(0)
    top = p_deg(p, 0)
    for k, coefficient in p.monos:
        if k[0] < top:
            value = abs(ring.to_fraction(coefficient) / leading)
            if value > maximum:
                maximum = value
    return Fr(1) + maximum


def _shrink(
    ring: Ring,
    seq: Sequence[Poly],
    p: Poly,
    interval: RootInterval,
) -> RootInterval:
    """Shrink a single-root isolating interval one step toward the root."""
    a, b = interval
    if a == b:
        return interval
    middle = (a + b) / 2
    if coef_sign(p_eval_at(ring, p, middle)) == 0:
        return (middle, middle)
    if count_roots_open(ring, seq, p, a, middle) >= 1:
        return (a, middle)
    return (middle, b)


def _refine_gaps(
    ring: Ring,
    seq: Sequence[Poly],
    p: Poly,
    intervals: list[RootInterval],
) -> list[RootInterval]:
    """Shrink touching or overlapping adjacent intervals until strictly gapped."""
    changed = True
    while changed:
        changed = False
        for index in range(len(intervals) - 1):
            if intervals[index][1] >= intervals[index + 1][0]:
                intervals[index] = _shrink(ring, seq, p, intervals[index])
                intervals[index + 1] = _shrink(ring, seq, p, intervals[index + 1])
                changed = True
    return intervals


def _iso_open(
    ring: Ring,
    seq: Sequence[Poly],
    p: Poly,
    a: Fr,
    b: Fr,
    output: list[RootInterval],
) -> None:
    """Isolate every real root strictly inside the open interval (a, b)."""
    roots = count_roots_open(ring, seq, p, a, b)
    if roots == 0:
        return
    if roots == 1:
        output.append((a, b))
        return
    middle = (a + b) / 2
    if coef_sign(p_eval_at(ring, p, middle)) == 0:
        output.append((middle, middle))
    _iso_open(ring, seq, p, a, middle, output)
    _iso_open(ring, seq, p, middle, b, output)


def squarefree_part(ring: Ring, p: Poly) -> Poly:
    """Squarefree part p / gcd(p, p'): the same root set, all roots simple."""
    if p_deg(p, 0) <= 0:
        return p
    divisor = p_gcd_univar(ring, p, p_deriv(ring, p, 0))
    if divisor.is_zero() or p_deg(divisor, 0) == 0:
        return p_monic(ring, p)
    return p_div_exact(ring, p_monic(ring, p), divisor)


def divisors(n: int) -> list[int]:
    """Positive divisors of n, by trial division up to sqrt(n)."""
    magnitude = abs(n)
    if magnitude == 0:
        return []
    output: list[int] = []
    divisor = 1
    while divisor * divisor <= magnitude:
        if magnitude % divisor == 0:
            output.append(divisor)
            if divisor != magnitude // divisor:
                output.append(magnitude // divisor)
        divisor += 1
    return output


def rational_roots(ring: Ring, p: Poly) -> list[Fr]:
    """Return the complete set of exact rational roots in ascending order."""
    if p_deg(p, 0) <= 0:
        return []
    from math import gcd

    coefs = {k[0]: ring.to_fraction(c) for k, c in p.monos}
    common_denominator = 1
    for coefficient in coefs.values():
        common_denominator = (
            common_denominator * coefficient.denominator
            // gcd(common_denominator, coefficient.denominator)
        )
    integer_coefs = {
        exponent: int(coefficient * common_denominator)
        for exponent, coefficient in coefs.items()
    }
    roots: list[Fr] = []
    while integer_coefs and integer_coefs.get(0, 0) == 0:
        roots.append(Fr(0))
        integer_coefs = {
            exponent - 1: coefficient
            for exponent, coefficient in integer_coefs.items()
            if exponent > 0
        }
    if not integer_coefs:
        return sorted(set(roots))
    degree = max(integer_coefs)
    constant = integer_coefs.get(0, 0)
    leading = integer_coefs[degree]
    candidates: set[Fr] = set()
    for numerator in divisors(constant):
        for denominator in divisors(leading):
            candidates.add(Fr(numerator, denominator))
            candidates.add(Fr(-numerator, denominator))
    for root in candidates:
        if coef_sign(p_eval_at(ring, p, root)) == 0:
            roots.append(root)
    return sorted(set(roots))


def real_roots_intervals(ring: Ring, p: Poly) -> list[RootInterval]:
    """Return ascending, disjoint, strictly gapped real-root isolators."""
    if p_deg(p, 0) <= 0:
        return []
    squarefree = squarefree_part(ring, p)
    sequence = sturm_sequence(ring, squarefree)
    rational = rational_roots(ring, squarefree)
    bound = cauchy_bound(ring, squarefree)
    intervals: list[RootInterval] = [(root, root) for root in rational]
    bounds = [Fr(-bound), *rational, Fr(bound)]
    for index in range(len(bounds) - 1):
        _iso_open(
            ring,
            sequence,
            squarefree,
            bounds[index],
            bounds[index + 1],
            intervals,
        )
    intervals.sort(key=lambda interval: interval[0])
    return _refine_gaps(ring, sequence, squarefree, intervals)
