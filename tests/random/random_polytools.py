# -*- coding: utf-8 -*-
"""Resultant and squarefree-decomposition random bench.

Four properties, all self-proving with no external ground truth:
  P18 evaluation anchor  res(f, x-r) == f(r) (checked against exact Horner evaluation)
  P19 common-root test   res(f, g) = 0 iff gcd(f, g) is nonconstant -- two independent
                         algorithms cross-checked; sign convention:
                         res(f, g) = (-1)^(mn) res(g, f)
  P20 squarefree round trip  prod factor_i^multiplicity_i == monic(f); each factor is
                         genuinely squarefree (gcd(h, h') is constant); and the sum of
                         multiplicity times degree equals deg f

Usage: python tests/random/random_polytools.py [rounds] [seed]
"""

import random
import sys
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.math.domains.poly import _norm, p_deriv, p_gcd_univar, p_mul, p_pow
from cas.math.domains.polytools import p_deg, p_monic, resultant, squarefree
from cas.math.domains.q import Q_RING as R
from cas.syntax.term import S


X = S("x")
V = (X,)


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_poly(rng, maxdeg=5):
    d = {}
    for e in range(rng.randint(0, maxdeg)):
        c = Fr(rng.randint(-6, 6), rng.choice((1, 1, 2)))
        if c != 0:
            d[(e,)] = c
    if not d:
        d[(0,)] = Fr(rng.randint(1, 4))
    return _norm(R, V, d)


def nonzero(rng, maxdeg=5):
    while True:
        p = rand_poly(rng, maxdeg)
        if not p.is_zero() and p_deg(p) > 0:
            return p


def horner(p, r: Fr) -> Fr:
    acc = Fr(0)
    for e in range(p_deg(p), -1, -1):
        c = Fr(0)
        for k, cc in p.monos:
            if k[0] == e:
                c = cc
        acc = acc * r + c
    return acc


def poly_equal(a, b) -> bool:
    return a.monos == b.monos


# ---------------------------------------------------------------------------
# P18: evaluation anchor
# ---------------------------------------------------------------------------

def prop_eval_anchor(rounds, rng):
    for i in range(rounds):
        f = nonzero(rng)
        r = Fr(rng.randint(-4, 4), rng.choice((1, 2)))
        lin = _norm(R, V, {(1,): Fr(1), (0,): -r})
        got = resultant(R, lin, f)
        want = horner(f, r)
        if got != want:
            fail("P18 evaluation anchor", i, f"res={got} f(r)={want}")


# ---------------------------------------------------------------------------
# P19: common-root test plus symmetry
# ---------------------------------------------------------------------------

def prop_common_root(rounds, rng):
    for i in range(rounds):
        f, g = nonzero(rng), nonzero(rng)
        m, n = p_deg(f), p_deg(g)
        res = resultant(R, f, g)
        gcd_deg = p_deg(p_gcd_univar(R, f, g))
        if (res == 0) != (gcd_deg >= 1):
            fail("P19 common-root test", i, f"res={res} gcd_deg={gcd_deg}")
        res_swap = resultant(R, g, f)
        sign = -1 if (m * n) % 2 else 1
        if res != sign * res_swap:
            fail("P19 symmetry", i, f"res={res} swap={res_swap}")
        # build a pair sharing a factor: the resultant must vanish
        c = nonzero(rng, 3)
        if resultant(R, p_mul(R, f, c), p_mul(R, g, c)) != 0:
            fail("P19 shared factor did not vanish", i)


# ---------------------------------------------------------------------------
# P20: squarefree round trip
# ---------------------------------------------------------------------------

def prop_squarefree(rounds, rng):
    for i in range(rounds):
        f = nonzero(rng)
        f = p_monic(R, f)
        parts = squarefree(R, f)
        acc = _norm(R, V, {(0,): Fr(1)})
        total = 0
        for h, mult in parts:
            if p_deg(h) <= 0:
                fail("P20 constant factor", i)
            if p_deg(p_gcd_univar(R, h, p_deriv(R, h, 0))) > 0:
                fail("P20 factor contains a square", i)
            acc = p_mul(R, acc, p_pow(R, h, mult))
            total += mult * p_deg(h)
        if not poly_equal(acc, f):
            fail("P20 round trip mismatch", i, f"deg f={p_deg(f)}")
        if total != p_deg(f):
            fail("P20 degree accounting", i, f"sum={total} deg={p_deg(f)}")


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== resultant/squarefree random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_eval_anchor(rounds, rng)
    print(f"P18 evaluation anchor     {rounds} rounds passed")
    prop_common_root(rounds, rng)
    print(f"P19 common root/symmetry  {rounds} rounds passed")
    prop_squarefree(rounds, rng)
    print(f"P20 squarefree round trip {rounds} rounds passed")
    print("== all passed ==")
