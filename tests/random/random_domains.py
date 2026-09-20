"""Domain-layer randomized bench.

Five properties, all self-proving:
  P5 polynomial round trip   random Poly -> to_term -> from_term equals the original monos
  P6 construction equivalence  the same polynomial built in a different order -> equal YES
  P7 inequality refutation   p vs p+constant -> equal NO
  P8 rational-function cross  a/b vs (a*c)/(b*c) -> equal YES; a/b vs (a+1)/b -> NO
  P9 GCD divisibility        gcd(a,b) divides both a and b (verified by exact division
                             over a univariate field)

Usage: python tests/random/random_domains.py [rounds] [seed]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.syntax.term import S, N, mk, plus, times, pw
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.domains.poly import (Poly, p_add, p_mul, p_neg, p_pow, p_scale,
                              p_const, p_zero, p_gcd_univar,
                              p_divmod_field, from_term, to_term,
                              _norm)
from cas.math.domains.ratfunc import rf_from_term, rf_equal, RatFunc
from cas.math.domains.q import Q_RING
from cas.math.domains import poly_domain, ratfunc_domain

from cas.runtime import bootstrap
from cas.runtime.dispatch import install

install(bootstrap())      # a standalone bench has no conftest: assemble explicitly

X, Y = S("x"), S("y")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_coef(rng):
    n = rng.randint(-9, 9)
    d = rng.choice((1, 1, 1, 2, 3, 4, 5))
    return Fr(n, d)


def rand_poly_uni(rng, n_terms=None):
    """Random univariate Poly in X."""
    if n_terms is None:
        n_terms = rng.randint(1, 5)
    d = {}
    exps = rng.sample(range(0, 8), min(n_terms, 8))
    for e in exps:
        c = rand_coef(rng)
        if c != 0:
            d[(e,)] = c
    return _norm(Q_RING, (X,), d)


def rand_poly_bi(rng):
    """Random bivariate Poly in X, Y."""
    d = {}
    for _ in range(rng.randint(1, 6)):
        ex = rng.randint(0, 4)
        ey = rng.randint(0, 4)
        c = rand_coef(rng)
        if c != 0:
            d[(ex, ey)] = d.get((ex, ey), Fr(0)) + c
    return _norm(Q_RING, (X, Y), {k: v for k, v in d.items() if v != 0})


# ---------------------------------------------------------------------------
# P5: Poly round-trip consistency
# ---------------------------------------------------------------------------

def prop_poly_roundtrip(rounds, rng):
    for i in range(rounds):
        p = rand_poly_bi(rng) if rng.random() < 0.5 else rand_poly_uni(rng)
        t = to_term(Q_RING, p)
        p2 = from_term(Q_RING, t, p.vars)
        if p2 is None:
            fail("P5 from_term returned None", i, p)
        if p.monos != p2.monos:
            fail("P5 round trip mismatch", i, f"orig={p.monos}", f"rt={p2.monos}")


# ---------------------------------------------------------------------------
# P6/P7: equality completeness
# ---------------------------------------------------------------------------

def prop_equal(rounds, rng):
    """P6 factored vs expanded equality; P7 inequality refutation."""
    P = poly_domain(X, ring=Q_RING)
    for i in range(rounds):
        a = rand_poly_uni(rng)
        b = rand_poly_uni(rng)
        # t1 = a*b (unexpanded product form), t2 = the p_mul-expanded form
        t1 = times(to_term(Q_RING, a), to_term(Q_RING, b))
        t2 = to_term(Q_RING, p_mul(Q_RING, a, b))
        r = P.equal(t1, t2)
        if r is not True:
            fail("P6 factored vs expanded failed", i, to_str(t1), to_str(t2))
        # inequality refutation: p vs p + constant
        p = a if not a.is_zero() else p_const(Q_RING, (X,), Fr(1))
        q = p_add(Q_RING, p, p_const(Q_RING, p.vars, Fr(rng.randint(1, 9))))
        r = P.equal(to_term(Q_RING, p), to_term(Q_RING, q))
        if r is not False:
            fail("P7 inequality refutation failed", i, to_str(to_term(Q_RING, p)),
                 to_str(to_term(Q_RING, q)))


# ---------------------------------------------------------------------------
# P8: rational-function cross-multiplication equality
# ---------------------------------------------------------------------------

def prop_ratfunc(rounds, rng):
    RF = ratfunc_domain(X, ring=Q_RING)
    for i in range(rounds):
        a = rand_poly_uni(rng)
        b = rand_poly_uni(rng)
        if b.is_zero():
            continue
        c = rand_poly_uni(rng)
        if c.is_zero():
            continue
        # a/b == (a*c)/(b*c) via cross-multiplication
        ra = RatFunc(a, b)
        rb = RatFunc(p_mul(Q_RING, a, c), p_mul(Q_RING, b, c))
        if not rf_equal(Q_RING, ra, rb):
            fail("P8 cross equivalence failed", i)
        # a/b != (a+1)/b
        a2 = p_add(Q_RING, a, p_const(Q_RING, (X,), Fr(1)))
        rb2 = RatFunc(a2, b)
        if rf_equal(Q_RING, ra, rb2):
            fail("P8 inequality failed", i)


# ---------------------------------------------------------------------------
# P9: GCD divisibility
# ---------------------------------------------------------------------------

def prop_gcd(rounds, rng):
    for i in range(rounds):
        a = rand_poly_uni(rng)
        b = rand_poly_uni(rng)
        if a.is_zero() and b.is_zero():
            continue
        g = p_gcd_univar(Q_RING, a, b)
        if g.is_zero():
            continue
        # g divides a: a = g*q + 0
        q, r = p_divmod_field(Q_RING, a, g, 0)
        if not r.is_zero():
            fail("P9 gcd does not divide a", i,
                 f"a={to_term(Q_RING,a)}",
                 f"g={to_term(Q_RING,g)}",
                 f"r={to_term(Q_RING,r)}")
        q, r = p_divmod_field(Q_RING, b, g, 0)
        if not r.is_zero():
            fail("P9 gcd does not divide b", i,
                 f"b={to_term(Q_RING,b)}",
                 f"g={to_term(Q_RING,g)}",
                 f"r={to_term(Q_RING,r)}")



if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 42
    print(f"== domain-layer random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_poly_roundtrip(rounds, rng)
    print(f"P5 polynomial round trip  {rounds} rounds passed")
    prop_equal(rounds, rng)
    print(f"P6/P7 equality complete   {rounds} rounds passed")
    prop_ratfunc(min(rounds, 1000), rng)
    print(f"P8  rational cross        {min(rounds,1000)} rounds passed")
    prop_gcd(min(rounds, 500), rng)
    print(f"P9  GCD divisibility      {min(rounds,500)} rounds passed")
    print("== all passed ==")
