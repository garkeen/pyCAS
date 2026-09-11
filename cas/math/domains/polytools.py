"""Shared polynomial parts: resultants and squarefree decomposition.

A resultant is the shared tool of the residue method and CAD projection;
squarefree decomposition (Yun) precedes factorization and Hermite reduction.
Both are implemented only for field coefficients in one variable; the
subresultant chain and the multivariate generalization upgrade through the same
interface once a multivariate gcd is in place.
"""

from cas.math.domains.poly import (Poly, p_scale, p_sub,
                              p_divmod_field, p_gcd_univar, p_deriv)


def p_deg(p: Poly, var_i: int = 0) -> int:
    return p.deg_in(var_i)


def p_lc(p: Poly, var_i: int = 0):
    """The leading coefficient with respect to var_i. A zero polynomial has no
    leading term, so the caller must guard against it."""
    top = max(p.monos, key=lambda kc: kc[0][var_i])
    return top[1]


def p_monic(ring, p: Poly, var_i: int = 0) -> Poly:
    if p.is_zero():
        return p
    return p_scale(ring, p, ring.div_exact(ring.from_int(1), p_lc(p, var_i)))


def p_div_exact(ring, a: Poly, b: Poly, var_i: int = 0) -> Poly:
    """Exact division: the remainder must be zero, otherwise the caller broke
    the contract."""
    q, r = p_divmod_field(ring, a, b, var_i)
    if not r.is_zero():
        raise ValueError("inexact division")
    return q


def resultant(ring, a: Poly, b: Poly, var_i: int = 0):
    """The resultant res(a, b) with field coefficients, by the remainder
    sequence recursion.

    Properties: res = 0 iff a and b share a root (a non-constant common factor);
    res(x - r, f) = f(r), which anchors the sign convention. Returns a ring
    element.
    """
    if a.is_zero() or b.is_zero():
        return ring.from_int(0)
    s = ring.from_int(1)
    while True:
        m, n = p_deg(a, var_i), p_deg(b, var_i)
        if m < n:
            a, b = b, a
            m, n = n, m
            if (m * n) % 2:
                s = ring.neg(s)
        if n == 0:
            # res(a, c) = c^deg(a)
            c = b.monos[0][1] if not b.is_zero() else ring.from_int(0)
            return ring.mul(s, ring.pow_pos(c, m))
        _, r = p_divmod_field(ring, a, b, var_i)
        if r.is_zero():
            return ring.from_int(0)        # a common factor
        if (m * n) % 2:
            s = ring.neg(s)
        lc = p_lc(b, var_i)
        s = ring.mul(s, ring.pow_pos(lc, m - p_deg(r, var_i)))
        a, b = b, r


def squarefree(ring, f: Poly):
    """Yun squarefree decomposition over a characteristic-zero field: returns
    [(factor, multiplicity), ...] with monic factors.

    The product of factor_i^multiplicity_i equals monic(f). A constant or zero
    polynomial returns an empty list.
    """
    if f.is_zero() or p_deg(f) == 0:
        return []
    f = p_monic(ring, f)
    df = p_deriv(ring, f, 0)
    g = p_gcd_univar(ring, f, df)
    w = p_div_exact(ring, f, g)
    y = p_div_exact(ring, df, g)
    z = p_sub(ring, y, p_deriv(ring, w, 0))
    out = []
    i = 1
    while p_deg(w) > 0:
        h = p_gcd_univar(ring, w, z)
        if p_deg(h) > 0:
            out.append((h, i))
            w = p_div_exact(ring, w, h)
        y = p_div_exact(ring, z, h) if p_deg(h) > 0 else z
        z = p_sub(ring, y, p_deriv(ring, w, 0))
        i += 1
    return out
