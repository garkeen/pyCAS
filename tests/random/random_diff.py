# -*- coding: utf-8 -*-
"""Differentiation-layer randomized bench.

Four properties, all self-proving with no external ground truth:
  P10 term/domain cross-check  for random polynomials and rational functions, the
                               term-layer differentiate and the domain-layer
                               p_deriv/rf_deriv (independent implementations) are
                               compared for equality in the rational function field
  P11 linearity/Leibniz        d(a+b)=da+db, d(ab)=a*db+b*da (term-layer identities)
  P12 Taylor h^1               f(x+h) viewed as a polynomial in h: the h^1 coefficient
                               equals f'(x), re-checked through an independent
                               coefficient-extraction channel
  P13 verifier independence   a workflow Diff step: a correct derivative passes the
                               domain cross-check, a deliberately wrong derivative is
                               refused by the verifier

Usage: python tests/random/random_diff.py [rounds] [seed]
"""

import random
import sys
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.frontend.pprint import to_str
from cas.math.diff import differentiate
from cas.math.domains.poly import _norm, from_term, p_deriv, to_term
from cas.math.domains.q import Q_RING
from cas.math.domains.ratfunc import RatFunc, ratfunc_domain, rf_deriv
from cas.runtime import bootstrap, new_workflow
from cas.syntax.term import N, S, neg, plus, pw, times
from cas.syntax.termpath import subst
from cas.workflow.command import Claim, Diff

RUNTIME = bootstrap()
MATH = RUNTIME.math

X, Y, H = S("x"), S("y"), S("h")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_coef(rng):
    n = rng.randint(-9, 9)
    d = rng.choice((1, 1, 1, 2, 3, 4))
    return Fr(n, d)


def rand_poly(rng):
    """Random bivariate sparse polynomial."""
    d = {}
    for _ in range(rng.randint(1, 6)):
        k = (rng.randint(0, 4), rng.randint(0, 4))
        c = rand_coef(rng)
        if c != 0:
            d[k] = d.get(k, Fr(0)) + c
    return _norm(Q_RING, (X, Y), {k: v for k, v in d.items() if v != 0})


def rand_nonzero_poly(rng):
    while True:
        p = rand_poly(rng)
        if not p.is_zero():
            return p


def _ctx():
    return MATH


def _render(term):
    return to_str(RUNTIME, term)


def rf_equal_terms(a, b):
    """Compare two terms in Q(x, y) (cross-multiplication, independent of term-layer
    folding)."""
    rfd = ratfunc_domain(X, Y, ring=Q_RING)
    return rfd.equal(a, b) is True


# ---------------------------------------------------------------------------
# P10: term-layer differentiation cross-checked against domain-layer derivatives
# ---------------------------------------------------------------------------

def prop_cross(rounds, rng):
    for i in range(rounds):
        if rng.random() < 0.5:
            p = rand_poly(rng)
            t = to_term(Q_RING, p)
            for var, idx in ((X, 0), (Y, 1)):
                got = differentiate(_ctx(), t, var)
                want = to_term(Q_RING, p_deriv(Q_RING, p, idx))
                if not rf_equal_terms(got, want):
                    fail("P10 polynomial cross-check", i, f"t={_render(t)} d/d{var.name}",
                         f"got={_render(got)}", f"want={_render(want)}")
        else:
            a, b = rand_poly(rng), rand_nonzero_poly(rng)
            rf = RatFunc(a, b)
            ta, tb = to_term(Q_RING, a), to_term(Q_RING, b)
            t = times(ta, pw(tb, N(-1)))
            for var, idx in ((X, 0), (Y, 1)):
                got = differentiate(_ctx(), t, var)
                d = rf_deriv(Q_RING, rf, idx)
                want = times(to_term(Q_RING, d.num),
                             pw(to_term(Q_RING, d.den), N(-1)))
                if not rf_equal_terms(got, want):
                    fail("P10 rational-function cross-check", i,
                         f"t={_render(t)} d/d{var.name}",
                         f"got={_render(got)}", f"want={_render(want)}")


# ---------------------------------------------------------------------------
# P11: linearity + Leibniz (term-layer identities)
# ---------------------------------------------------------------------------

def prop_leibniz(rounds, rng):
    for i in range(rounds):
        a = to_term(Q_RING, rand_poly(rng))
        b = to_term(Q_RING, rand_nonzero_poly(rng))
        da, db = differentiate(_ctx(), a, X), differentiate(_ctx(), b, X)
        # d(a+b) = da + db
        if not rf_equal_terms(differentiate(_ctx(), plus(a, b), X), plus(da, db)):
            fail("P11 linearity", i, _render(a), _render(b))
        # d(ab) = a*db + b*da
        want = plus(times(a, db), times(b, da))
        if not rf_equal_terms(differentiate(_ctx(), times(a, b), X), want):
            fail("P11 Leibniz", i, _render(a), _render(b))
        # d(a/b) = (da*b - a*db)/b^2
        q = times(a, pw(b, N(-1)))
        want_q = times(plus(times(da, b), neg(times(a, db))),
                       pw(b, N(-2)))
        if not rf_equal_terms(differentiate(_ctx(), q, X), want_q):
            fail("P11 quotient rule", i, _render(q))


# ---------------------------------------------------------------------------
# P12: Taylor h^1 coefficient equals the derivative (independent coefficient extraction)
# ---------------------------------------------------------------------------

def prop_taylor(rounds, rng):
    for i in range(rounds):
        p = rand_poly(rng)
        t = to_term(Q_RING, p)
        th = subst(t, {X: plus(X, H)})         # f(x+h, y)
        ph = from_term(Q_RING, th, (H, X, Y))
        if ph is None:
            fail("P12 expansion left the domain", i, _render(th))
        coefs = {}
        for k, c in ph.monos:
            coefs.setdefault(k[0], {})[(k[1], k[2])] = c
        lin = _norm(Q_RING, (X, Y), coefs.get(1, {}))
        got = differentiate(_ctx(), t, X)
        want = to_term(Q_RING, lin)
        if not rf_equal_terms(got, want):
            fail("P12 Taylor h^1", i, f"t={_render(t)}",
                 f"got={_render(got)}", f"want={_render(want)}")


# ---------------------------------------------------------------------------
# P13: workflow verifier independence (correct passes, wrong is refused)
# ---------------------------------------------------------------------------

def prop_workflow(rounds, rng):
    for i in range(rounds):
        p = rand_poly(rng)
        t = to_term(Q_RING, p)
        good = differentiate(_ctx(), t, X)
        wf = new_workflow(RUNTIME)
        s0 = wf.add(t, Claim())
        s1 = wf.add(good, Diff(pred=s0.id, var=X))
        if s1.status != "committed":
            fail("P13 correct derivative was refused", i, _render(t), _render(good))
        bad = plus(good, N(1))
        s2 = wf.add(bad, Diff(pred=s0.id, var=X))
        if s2.status != "refused":
            fail("P13 wrong derivative was not refused", i, _render(t), _render(bad))


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== differentiation random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_cross(rounds, rng)
    print(f"P10 term/domain cross-check   {rounds} rounds passed")
    prop_leibniz(rounds, rng)
    print(f"P11 linear/Leibniz/quotient   {rounds} rounds passed")
    prop_taylor(min(rounds, 500), rng)
    print(f"P12 Taylor h^1                {min(rounds,500)} rounds passed")
    prop_workflow(min(rounds, 300), rng)
    print(f"P13 verifier independence     {min(rounds,300)} rounds passed")
    print("== all passed ==")
