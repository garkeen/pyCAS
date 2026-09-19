"""K(x1..xn) rational function field: numerator/denominator sparse polynomial pairs.

Normal form: numerator and denominator are each expanded and collected, not
necessarily reduced -- reduction stays out until a general multivariate GCD is in
place (see below). Equality is exact cross-multiplication (ad == bc), fully decided
within the fragment and independent of reduction.

An honest split:
* the output of normalize is not unique for inputs that are equal but unreduced
  (x/2 and 2x/4 differ in shape), so it is not a full normal form of the quotient
  field;
* equal is a complete decision (the cross-multiplication identity), a general
  algorithm rather than a workaround;
* reduction to a normal form comes after a multivariate GCD: the univariate
  Euclidean GCD already exists in poly.p_gcd_univar and will attach as a fast path
  before equal to shrink the problem size.

Structure: K[x] is contained in K(x), so conversion takes the polynomial fast path
first (poly.from_term hitting directly) and otherwise recurses on rational
composition -- one route, no branching special case.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.syntax.term import Expr, Int
from cas.math.domains.base import Domain, Ring
from cas.math.domains.poly import (Poly, p_mul, p_scale, _norm,
                              to_term, from_term as poly_from_term,
                              p_gcd_univar, p_divmod_field, p_deriv)


@dataclass(frozen=True, slots=True)
class RatFunc:
    """Invariant: den is nonzero. num/den are Poly over the same variable set."""
    num: Poly
    den: Poly


# ---------------------------------------------------------------------------
# dict intermediate arithmetic (construction time; Poly freezing happens at the exit)
# ---------------------------------------------------------------------------

def _add(ring, a: dict, b: dict) -> dict:
    d = dict(a)
    for k, c in b.items():
        d[k] = ring.add(d.get(k, ring.from_int(0)), c)
        if ring.is_zero(d[k]):
            del d[k]
    return d


def _mul(ring, a: dict, b: dict) -> dict:
    d = {}
    for ka, ca in a.items():
        for kb, cb in b.items():
            k = tuple(x + y for x, y in zip(ka, kb))
            d[k] = ring.add(d.get(k, ring.from_int(0)), ring.mul(ca, cb))
    return {k: c for k, c in d.items() if not ring.is_zero(c)}


def _pow(ring, a: dict, n: int) -> dict:
    r = {(0,) * _width(a): ring.from_int(1)}
    b = a
    while n:
        if n & 1:
            r = _mul(ring, r, b)
        n >>= 1
        if n:
            b = _mul(ring, b, b)
    return r


def _width(a: dict) -> int:
    return len(next(iter(a))) if a else 0


def _is_zero(a: dict) -> bool:
    return not a                       # construction-time invariant: zero coefficients are not kept


# ---------------------------------------------------------------------------
# Terms <-> rational functions
# ---------------------------------------------------------------------------

def rf_from_term(ring: Ring, t, vars_: tuple) -> RatFunc | None:
    """Interned term -> RatFunc; None when the term leaves the K(x) fragment.

    A negative integer power is handled as a reciprocal (b^(-k) swaps numerator and
    denominator); 0 to a negative power is undefined and therefore not a member.
    Every other head (Sin, ...) is not a member.
    """
    w = len(vars_)
    one = {(0,) * w: ring.from_int(1)}

    def rec(u):
        # fast path: the whole subtree is a polynomial
        p = poly_from_term(ring, u, vars_)
        if p is not None:
            return dict(p.monos), dict(one)
        if not isinstance(u, Expr):
            return None                # non-member leaf: unknown symbol or non-ring coefficient
        n = u.head.name
        if n == "Plus":
            acc = None
            for a in u.args:
                pa = rec(a)
                if pa is None:
                    return None
                if acc is None:
                    acc = pa
                else:
                    an, ad = acc
                    bn, bd = pa
                    acc = (_add(ring, _mul(ring, an, bd),
                                _mul(ring, bn, ad)),
                           _mul(ring, ad, bd))
            return acc
        if n == "Times":
            acc = None
            for a in u.args:
                pa = rec(a)
                if pa is None:
                    return None
                acc = pa if acc is None else \
                    (_mul(ring, acc[0], pa[0]), _mul(ring, acc[1], pa[1]))
            return acc
        if n == "Power":
            b, e = u.args
            pb = rec(b)
            if pb is None or not isinstance(e, Int):
                return None
            bn, bd_ = pb
            k = e.v
            if k >= 0:
                if k == 0 and _is_zero(bn):
                    return None        # 0^0 refused (matches the polynomial path)
                return _pow(ring, bn, k), _pow(ring, bd_, k)
            if _is_zero(bn):
                return None            # 0 to a negative power: undefined
            return _pow(ring, bd_, -k), _pow(ring, bn, -k)
        return None

    r = rec(t)
    if r is None:
        return None
    nd, dd = r
    if _is_zero(dd):
        return None                    # zero denominator: undefined
    vt = tuple(vars_)
    return RatFunc(_norm(ring, vt, nd), _norm(ring, vt, dd))


def rf_equal(ring, a: RatFunc, b: RatFunc) -> bool:
    """ad == bc, a complete decision."""
    return p_mul(ring, a.num, b.den).monos == \
        p_mul(ring, b.num, a.den).monos


def rf_reduce(ring, rf: RatFunc) -> RatFunc:
    """Univariate GCD reduction (a fast path for the general algorithm: univariate
    Euclid is already implemented). Multivariate reduction attaches the same way once
    a multivariate GCD exists."""
    if len(rf.num.vars) != 1 or rf.den.is_zero():
        return rf
    g = p_gcd_univar(ring, rf.num, rf.den)
    if g.is_zero():
        return rf
    qn, _ = p_divmod_field(ring, rf.num, g, 0)
    qd, _ = p_divmod_field(ring, rf.den, g, 0)
    if qd.is_zero():
        return rf
    lead = max(qd.monos, key=lambda kc: kc[0][0])
    inv = ring.div_exact(ring.from_int(1), lead[1])
    return RatFunc(p_scale(ring, qn, inv), p_scale(ring, qd, inv))


def rf_to_term(ring, rf: RatFunc):
    """RatFunc -> canonical rendering as an interned term: only the numerator when
    the denominator is 1.

    The single global exit, so that project/workflow/ratfunc do not each duplicate
    the same rendering."""
    nt = to_term(ring, rf.num)
    dt = to_term(ring, rf.den)
    if T.is_num(dt) and T.num_val(dt) == 1:
        return nt
    return T.mk(T.S("Times"), (nt, T.pw(dt, T.N(-1))))


def rf_deriv(ring, rf: RatFunc, var_i: int) -> RatFunc:
    """Derivation inside the field (quotient rule): D(n/d) = (D(n)*d - n*D(d)) / d^2.

    The exit reduces through the rf_reduce fast path (univariate). The coefficient
    derivation goes through ring.deriv."""
    dn = p_deriv(ring, rf.num, var_i)
    dd = p_deriv(ring, rf.den, var_i)
    num = _norm(ring, rf.num.vars,
                _add(ring, _mul(ring, dict(dn.monos), dict(rf.den.monos)),
                     {k: ring.neg(c) for k, c in
                      _mul(ring, dict(rf.num.monos), dict(dd.monos)).items()}))
    den = _norm(ring, rf.den.vars,
                _mul(ring, dict(rf.den.monos), dict(rf.den.monos)))
    return rf_reduce(ring, RatFunc(num, den))


class RatFuncDomain(Domain):
    """K(x1..xn)."""

    def __init__(self, vars_, ring: Ring, name: str | None = None):
        self.vars = tuple(vars_)
        self.ring = ring
        self.name = name or "K(" + ",".join(v.name for v in self.vars) + ")"
        # capability: K(x) is always a field; univariate it is also Euclidean
        self.is_field = True
        self.is_euclidean = bool(ring.is_field and len(self.vars) == 1)

    def member(self, t) -> bool:
        return rf_from_term(self.ring, t, self.vars) is not None

    def normalize(self, t):
        rf = rf_from_term(self.ring, t, self.vars)
        if rf is None:
            return None
        return rf_to_term(self.ring, rf_reduce(self.ring, rf))

    def equal(self, a, b):
        ra = rf_from_term(self.ring, a, self.vars)
        rb = rf_from_term(self.ring, b, self.vars)
        if ra is None or rb is None:
            return None                  # not a member: caller out of bounds
        return rf_equal(self.ring, ra, rb)

    def element_is_zero(self, element) -> bool:
        """A fraction vanishes iff its numerator does: the denominator is
        nonzero by construction."""
        return element.num.is_zero()

    def element_to_term(self, element):
        """The existing reduced normal-form rendering path."""
        return rf_to_term(self.ring, rf_reduce(self.ring, element))


_domain_cache = {}


def ratfunc_domain(*vars_, ring=None) -> RatFuncDomain:
    """Fetch the domain object for a (variable set, coefficient ring) pair, sharing
    instances at the same level.

    Same strategy as poly_domain: only the factory cache is used, never the domain
    registry (the reason is in poly_domain's docstring). The two parameterized domain
    families must behave symmetrically, including defaulting the coefficient ring to
    the assembly-injected base field rather than hardcoding `Q_RING`.
    """
    from cas.math.domains.base import default_coeff_ring
    r = default_coeff_ring() if ring is None else ring
    key = (tuple(vars_), r)
    d = _domain_cache.get(key)
    if d is None:
        d = RatFuncDomain(tuple(vars_), r)
        _domain_cache[key] = d
    return d
