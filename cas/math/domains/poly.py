"""K[x1..xn] polynomial domain: sparse coefficient dictionary plus a generic
coefficient ring protocol.

Normal form: a canonically ordered (exponent tuple ascending, zero coefficients
dropped) coefficient/monomial collection, frozen at construction. Equality in the
same domain is structural comparison of normal forms and is fully decided.

Representation cost: addition O(|p|+|q|), multiplication O(|p|*|q|) by dictionary
merge, with no recursion and no tree allocation -- the hot path is pure dict/tuple
work.

Genericity: coefficients are handled opaquely through the Ring protocol, so any
Gaussian or quotient ring that implements the same protocol mounts with zero change
to the polynomial layer.
"""

from dataclasses import dataclass
from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.syntax.term import Expr, Int, Sym
from cas.math.domains.base import Domain, Ring, RingError


# ---------------------------------------------------------------------------
# Poly: immutable sparse polynomial
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Poly:
    """vars: the variable order (fixed); monos: ((exp...), coef) tuples in ascending
    exponent order."""
    vars: tuple
    monos: tuple

    def is_zero(self) -> bool:
        return not self.monos

    def deg_in(self, i: int) -> int:
        return max((k[i] for k, _ in self.monos), default=-1)


def _norm(ring: Ring, vars_, monos_dict: dict) -> Poly:
    """dict -> frozen normal form: drop zeros, sort exponents ascending. The single
    construction exit."""
    ks = sorted(k for k, c in monos_dict.items() if not ring.is_zero(c))
    return Poly(vars_, tuple((k, monos_dict[k]) for k in ks))


def p_zero(vars_):
    return Poly(vars_, ())


def p_const(ring: Ring, vars_, c):
    z = (0,) * len(vars_)
    return _norm(ring, vars_, {z: c})


def p_add(ring: Ring, p: Poly, q: Poly) -> Poly:
    d = dict(p.monos)
    for k, c in q.monos:
        d[k] = ring.add(d.get(k, ring.from_int(0)), c)
        if ring.is_zero(d[k]):
            del d[k]
    return _norm(ring, p.vars, d)


def p_neg(ring: Ring, p: Poly) -> Poly:
    return Poly(p.vars, tuple((k, ring.neg(c)) for k, c in p.monos))


def p_sub(ring: Ring, p: Poly, q: Poly) -> Poly:
    return p_add(ring, p, p_neg(ring, q))


def p_mul(ring: Ring, p: Poly, q: Poly) -> Poly:
    if p.is_zero() or q.is_zero():
        return p_zero(p.vars)
    d = {}
    for ka, ca in p.monos:
        for kb, cb in q.monos:
            k = tuple(x + y for x, y in zip(ka, kb))
            d[k] = ring.add(d.get(k, ring.from_int(0)), ring.mul(ca, cb))
    return _norm(ring, p.vars, d)


def p_pow(ring: Ring, p: Poly, n: int) -> Poly:
    """Fast exponentiation, n >= 0."""
    if n < 0:
        raise ValueError("negative exponent")
    r = p_const(ring, p.vars, ring.from_int(1))
    b = p
    while n:
        if n & 1:
            r = p_mul(ring, r, b)
        b = p_mul(ring, b, b)
        n >>= 1
    return r


def p_scale(ring: Ring, p: Poly, c) -> Poly:
    if ring.is_zero(c):
        return p_zero(p.vars)
    return Poly(p.vars, tuple((k, ring.mul(c, m)) for k, m in p.monos))


def p_divmod_field(ring: Ring, p: Poly, q: Poly, var_i: int):
    """Full division over a field coefficient ring, with the leading power taken in
    the monomial order of variable var_i.

    Requires exact division from the ring (Q satisfies this naturally). Returns
    (quot, rem).
    """
    if q.is_zero():
        raise ZeroDivisionError("poly division by zero")
    ex_div = lambda a, b: ring.div_exact(a, b)
    rem = dict(p.monos)
    quot = {}
    dq_top = max((k[var_i] for k, _ in q.monos), default=-1)
    q_lead = max(q.monos, key=lambda kc: kc[0][var_i])
    while True:
        live = [(k, c) for k, c in rem.items() if not ring.is_zero(c)]
        if not live:
            break
        k, c = max(live, key=lambda kc: kc[0][var_i])
        e = k[var_i] - dq_top
        if e < 0:
            break
        # quotient monomial exponents: k - q_lead exponents, componentwise
        mono = tuple(a - b for a, b in zip(k, q_lead[0]))
        lc = ex_div(c, q_lead[1])
        quot = {mono: lc} if not quot else {**quot, mono: quot.get(mono, ring.from_int(0)) + lc}
        # subtract lc * mono * q
        sub = {}
        for kq, cq in q.monos:
            kk = tuple(a + b for a, b in zip(mono, kq))
            sub[kk] = ring.mul(lc, cq)
        for kk, cc in sub.items():
            nv = ring.sub(rem.get(kk, ring.from_int(0)), cc)
            if ring.is_zero(nv):
                rem.pop(kk, None)
            else:
                rem[kk] = nv
    return (_norm(ring, p.vars, quot), _norm(ring, p.vars, rem))


def p_gcd_univar(ring: Ring, p: Poly, q: Poly) -> Poly:
    """Euclidean GCD over a field for the univariate case (len(vars) == 1), in monic
    normal form.

    This is the general Euclidean algorithm, not a special case. Multivariate GCD
    will attach as a fast path on top once the general algorithm is in place, and is
    not offered today."""
    if len(p.vars) != 1:
        raise ValueError("univariate only")
    a, b = p, q
    while not b.is_zero():
        _, r = p_divmod_field(ring, a, b, 0)
        a, b = b, r
    if a.is_zero():
        return p_zero(p.vars)
    lead = max(a.monos, key=lambda kc: kc[0][0])
    monic = p_scale(ring, a, ring.div_exact(ring.from_int(1), lead[1]))
    return monic


def p_deriv(ring: Ring, p: Poly, var_i: int) -> Poly:
    """Formal derivative with respect to the var_i-th variable (the derivation stays
    inside K[x]).

    D(sum c*x^k) = sum (D(c)*x^k + c*k_i*x^(k-e_i)), with the coefficient derivation
    delegated to ring.deriv: zero over a constant field, and overridden for
    parameterized or algebraic extensions."""
    d = {}
    for k, c in p.monos:
        dc = ring.deriv(c)
        if not ring.is_zero(dc):
            d[k] = ring.add(d.get(k, ring.from_int(0)), dc)
        ki = k[var_i]
        if ki:
            kk = tuple(kj - (1 if j == var_i else 0) for j, kj in enumerate(k))
            d[kk] = ring.add(d.get(kk, ring.from_int(0)),
                             ring.mul(ring.from_int(ki), c))
    return _norm(ring, p.vars, d)


# ---------------------------------------------------------------------------
# Terms <-> polynomials
# ---------------------------------------------------------------------------

def from_term(ring: Ring, t, vars_: tuple) -> Poly | None:
    """Interned term -> Poly; None when the term leaves the K[x] fragment (unknown
    symbol, non-integer exponent, other head). Membership test and conversion happen
    in one pass."""
    idx = {v: i for i, v in enumerate(vars_)}
    zero = (0,) * len(vars_)

    def rec(u) -> dict | None:
        if isinstance(u, Int):
            return {zero: ring.from_int(u.v)} if u.v else {}
        if T.is_num(u):
            try:
                return {zero: ring.from_frac(T.num_val(u))}
            except RingError:
                return None
        if isinstance(u, Sym):
            if u in idx:
                k = tuple(1 if j == idx[u] else 0 for j in range(len(vars_)))
                return {k: ring.from_int(1)}
            return None
        if isinstance(u, Expr):
            n = u.head.name
            if n == "Plus":
                acc = {}
                for a in u.args:
                    pa = rec(a)
                    if pa is None:
                        return None
                    for k, c in pa.items():
                        acc[k] = ring.add(acc.get(k, ring.from_int(0)), c)
                return {k: c for k, c in acc.items() if not ring.is_zero(c)}
            if n == "Times":
                acc = {zero: ring.from_int(1)}
                for a in u.args:
                    pa = rec(a)
                    if pa is None:
                        return None
                    nxt = {}
                    for k1, c1 in acc.items():
                        for k2, c2 in pa.items():
                            k = tuple(x + y for x, y in zip(k1, k2))
                            nxt[k] = ring.add(nxt.get(k, ring.from_int(0)),
                                              ring.mul(c1, c2))
                    acc = {k: c for k, c in nxt.items() if not ring.is_zero(c)}
                return acc
            if n == "Power":
                b, e = u.args
                pb = rec(b)
                if pb is None or not isinstance(e, Int) or e.v < 0:
                    return None
                if e.v == 0:
                    # 0^0 is refused (the term-level fold also leaves it interned
                    # rather than evaluating it, and eval_exact refuses it too).
                    # A nonzero base to the zero is the polynomial 1; a base that
                    # folds to the zero polynomial raised to the zero is the
                    # contentious 0^0, refused so the projection is honestly
                    # undecided rather than silently 1.
                    if not pb:
                        return None
                    return {zero: ring.from_int(1)}
                cur = {zero: ring.from_int(1)}
                base = pb
                nn = e.v
                while nn:
                    if nn & 1:
                        nxt = {}
                        for k1, c1 in cur.items():
                            for k2, c2 in base.items():
                                k = tuple(x + y for x, y in zip(k1, k2))
                                nxt[k] = ring.add(nxt.get(k, ring.from_int(0)),
                                                  ring.mul(c1, c2))
                        cur = {k: c for k, c in nxt.items()
                               if not ring.is_zero(c)}
                    nn >>= 1
                    if nn:
                        nxt = {}
                        for k1, c1 in base.items():
                            for k2, c2 in base.items():
                                k = tuple(x + y for x, y in zip(k1, k2))
                                nxt[k] = ring.add(nxt.get(k, ring.from_int(0)),
                                                  ring.mul(c1, c2))
                        base = {k: c for k, c in nxt.items()
                                if not ring.is_zero(c)}
                return cur
        return None

    d = rec(t)
    if d is None:
        return None
    return _norm(ring, vars_, d)


def to_term(ring: Ring, p: Poly):
    """Poly -> canonical interned term: sum coef * prod x^e, interned in sorted
    order."""
    terms = []
    for k, c in p.monos:
        var_factors = [v for v, e in zip(p.vars, k) if e == 1]
        var_powers = [T.pw(v, T.N(e)) for v, e in zip(p.vars, k) if e > 1]
        vf = var_factors + var_powers
        is_one = ring.equal(c, ring.from_int(1))
        if is_one and vf:
            ft = vf[0] if len(vf) == 1 else T.mk(T.S("Times"), tuple(vf))
        else:
            coef_t = T.N(c) if isinstance(c, Fr) else _coef_term(ring, c)
            facs = [coef_t] + vf
            ft = facs[0] if len(facs) == 1 else T.mk(T.S("Times"), tuple(facs))
        terms.append(ft)
    if not terms:
        return T.N(0)
    return terms[0] if len(terms) == 1 else T.mk(T.S("Plus"), tuple(terms))


def _coef_term(ring: Ring, c):
    """Hook for rendering a non-Q coefficient as a term: used when the ring carries
    its own renderer; the Q ring never reaches here."""
    render = getattr(ring, "to_term", None)
    if render is None:
        raise TypeError(f"ring {ring!r} cannot render coefficient {c!r}")
    return render(c)


# ---------------------------------------------------------------------------
# The domain object
# ---------------------------------------------------------------------------

class PolyDomain(Domain):
    """K[x1..xn] with K a field coefficient ring containing Q."""

    def __init__(self, vars_, ring: Ring, name: str | None = None):
        self.vars = tuple(vars_)
        self.ring = ring
        self.name = name or "K[" + ",".join(v.name for v in self.vars) + "]"
        # capability: K[x] is a Euclidean domain only when univariate over a field
        self.is_euclidean = bool(ring.is_field and len(self.vars) == 1)

    def member(self, t) -> bool:
        return from_term(self.ring, t, self.vars) is not None

    def normalize(self, t):
        p = from_term(self.ring, t, self.vars)
        if p is None:
            return None
        return to_term(self.ring, p)

    def equal(self, a, b):
        pa = from_term(self.ring, a, self.vars)
        pb = from_term(self.ring, b, self.vars)
        if pa is None or pb is None:
            return None                  # not a member: caller out of bounds
        return pa.monos == pb.monos

    def element_is_zero(self, element) -> bool:
        """The polynomial's own zero test: empty monomial collection."""
        return element.is_zero()

    def element_to_term(self, element):
        """The existing Poly -> canonical interned term path."""
        return to_term(self.ring, element)


_domain_cache = {}


def poly_domain(*vars_, ring=None) -> PolyDomain:
    """Fetch the domain object for a (variable set, coefficient ring) pair, sharing
    instances at the same level.

    Only the factory cache is used; **the domain registry is not touched**. The
    registry holds the resident base fields (Z/Q/Q(i)), while K[x] is parameterized
    by the variable set, which is unbounded -- pushing a new entry per variable set
    would grow the registry without bound and mix two responsibilities, "resident
    base field" and "parameterized instance", into one table. Parameterized domains
    are held by their factory caches (K(x) likewise).

    The coefficient ring defaults to the **assembly-injected** base field
    (`base.default_coeff_ring`); this module neither hardcodes `Q_RING` nor
    bootstraps a concrete domain itself. An explicit `ring` is for the projection
    layer choosing a coefficient domain by capability; the cache key contains the
    ring, so a different ring is a different domain.
    """
    from cas.math.domains.base import default_coeff_ring
    r = default_coeff_ring() if ring is None else ring
    key = (tuple(vars_), r)
    d = _domain_cache.get(key)
    if d is None:
        d = PolyDomain(tuple(vars_), r)
        _domain_cache[key] = d
    return d
