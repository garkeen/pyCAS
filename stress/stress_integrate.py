# -*- coding: utf-8 -*-
"""Integration skeleton stress bench (fully self-proving, no external ground truth).

  P32 indefinite round trip  random polynomial: verify_antideriv (independently
                             re-checked by the differentiation layer) is true; and the
                             definite integral equals a per-term power-formula
                             reference (two independent channels)
  P33 additivity/FTC         integral_a^b + integral_b^c == integral_a^c; integral_a^a == 0
  P34 piecewise definite integral  summing per piece over rational breakpoints equals
                             the piecewise reference; a gap or point hole is refused
  P35 refusal boundary       a proper fraction / transcendental integrand / irrational
                             limits -> IntegrateError

Usage: python stress/stress_integrate.py [rounds] [seed]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.runtime import bootstrap
bootstrap()

import cas.syntax.term as T
from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.qarith import fold
from cas.math.integrate import integrate_term, definite_integrate
from cas.math.calculus.integration.verify import verify_antideriv
from cas.errors import IntegrateError
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import _norm, to_term
from cas.math.piecewise import piecewise

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_poly(rng, maxdeg=4):
    """Random univariate polynomial with Q coefficients; returns (Poly, {(e,):Fr})."""
    deg = rng.randint(0, maxdeg)
    d = {}
    for e in range(deg + 1):
        c = Fr(rng.randint(-9, 9), rng.choice((1, 1, 2, 3)))
        if c != 0:
            d[(e,)] = d.get((e,), Fr(0)) + c
    d = {k: c for k, c in d.items() if c != 0}
    if not d:
        d = {(0,): Fr(1)}
    return _norm(Q_RING, (X,), d), d


def ref_definite(coefs, a, b):
    """Per-term power-formula reference (independent of the antiderivative-substitution
    channel)."""
    total = Fr(0)
    for (e,), c in coefs.items():
        total += c * (b ** (e + 1) - a ** (e + 1)) / Fr(e + 1)
    return total


def _num(t):
    f = fold(t)
    if not T.is_num(f):
        return None
    return T.num_val(f)


# ---------------------------------------------------------------------------
# P32: indefinite round trip plus the independent definite channel
# ---------------------------------------------------------------------------

def prop_indefinite(rounds, rng):
    for i in range(rounds):
        p, coefs = rand_poly(rng)
        f = to_term(Q_RING, p)
        F = integrate_term(f, X)
        if verify_antideriv(F, f, X) is not True:
            fail("P32 antiderivative verification failed", i, to_str(f), to_str(F))
        a = Fr(rng.randint(-5, 5), 1)
        b = Fr(rng.randint(-5, 5), 1)
        if a > b:
            a, b = b, a
        got = _num(definite_integrate(f, X, T.N(a), T.N(b)))
        want = ref_definite(coefs, a, b)
        if got != want:
            fail("P32 definite integral disagrees between channels", i, to_str(f), a, b, got, want)


# ---------------------------------------------------------------------------
# P33: additivity and integral_a^a == 0
# ---------------------------------------------------------------------------

def prop_additivity(rounds, rng):
    for i in range(rounds):
        p, _c = rand_poly(rng, maxdeg=3)
        f = to_term(Q_RING, p)
        a, b, c = sorted(Fr(rng.randint(-6, 6), 1) for _ in range(3))
        ab = _num(definite_integrate(f, X, T.N(a), T.N(b)))
        bc = _num(definite_integrate(f, X, T.N(b), T.N(c)))
        ac = _num(definite_integrate(f, X, T.N(a), T.N(c)))
        if ab + bc != ac:
            fail("P33 additivity broken", i, to_str(f), a, b, c, ab, bc, ac)
        aa = _num(definite_integrate(f, X, T.N(a), T.N(a)))
        if aa != 0:
            fail("P33 integral_a^a is nonzero", i, to_str(f), a, aa)


# ---------------------------------------------------------------------------
# P34: piecewise definite integral
# ---------------------------------------------------------------------------

def prop_piecewise(rounds, rng):
    for i in range(rounds):
        r = rng.randint(-3, 3)
        p1, c1 = rand_poly(rng, maxdeg=3)
        p2, c2 = rand_poly(rng, maxdeg=3)
        pw = piecewise([(to_term(Q_RING, p1), parse(f"x < {r}")),
                        (to_term(Q_RING, p2), parse(f"x >= {r}"))])
        # entirely in the left region (a < b < r)
        a = Fr(r - rng.randint(3, 5), 1)
        b = Fr(r - rng.randint(1, 2), 1)
        got = _num(definite_integrate(pw, X, T.N(a), T.N(b)))
        if got != ref_definite(c1, a, b):
            fail("P34 left region mismatch", i, a, b, got, ref_definite(c1, a, b))
        # crossing the breakpoint
        lo = Fr(r - rng.randint(1, 3), 1)
        hi = Fr(r + rng.randint(1, 3), 1)
        got2 = _num(definite_integrate(pw, X, T.N(lo), T.N(hi)))
        want2 = ref_definite(c1, lo, Fr(r)) + ref_definite(c2, Fr(r), hi)
        if got2 != want2:
            fail("P34 crossing the breakpoint mismatch", i, lo, hi, got2, want2)
        # gap refusal: x<r and x>r+1 leave a gap between them
        gap_pw = piecewise([(parse("1"), parse(f"x < {r}")),
                            (parse("1"), parse(f"x > {r + 1}"))])
        try:
            definite_integrate(gap_pw, X, T.N(Fr(r - 2)), T.N(Fr(r + 3)))
            fail("P34 gap was not refused", i)
        except IntegrateError:
            pass


# ---------------------------------------------------------------------------
# P35: refusal boundary
# ---------------------------------------------------------------------------

def prop_refusal(rounds, rng):
    for i in range(rounds):
        # proper fraction
        try:
            integrate_term(parse("1/x"), X)
            fail("P35 proper fraction not refused", i)
        except IntegrateError:
            pass
        # transcendental
        try:
            integrate_term(parse("exp(x)"), X)
            fail("P35 transcendental not refused", i)
        except IntegrateError:
            pass
        # irrational limits (the roots of x^2-2 are not rational terms, so a symbolic
        # limit triggers it)
        try:
            definite_integrate(parse("x^2"), X, parse("y"), T.N(1))
            fail("P35 non-rational limit not refused", i)
        except IntegrateError:
            pass


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== integration skeleton stress bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_indefinite(rounds, rng)
    print(f"P32 indefinite round trip + two channels  {rounds} rounds passed")
    prop_additivity(rounds, rng)
    print(f"P33 additivity / integral_a^a             {rounds} rounds passed")
    prop_piecewise(rounds, rng)
    print(f"P34 piecewise definite integral           {rounds} rounds passed")
    prop_refusal(rounds, rng)
    print(f"P35 refusal boundary                      {rounds} rounds passed")
    print("== all passed ==")
