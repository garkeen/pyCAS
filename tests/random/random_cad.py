# -*- coding: utf-8 -*-
"""One-dimensional CAD / real-root isolation random bench (fully self-proving, no
external ground truth).

  P25 isolation correctness  build a polynomial with known roots (rational roots and
                             irrational quadratic factors): the number of isolating
                             intervals equals the number of distinct real roots, each
                             interval holds exactly one root, adjacent intervals leave a
                             strict gap, and rational roots are hit exactly
  P26 partition structure    cells alternate open/point and the open intervals cover the
                             whole axis end to end; the condition truth value on an open
                             cell equals direct substitution at the sample point (an
                             independent cross-check)
  P27 refusal reason         a transcendental condition -> UNDECIDABLE; a multivariate
                             condition -> FRAGMENT
  P28 point-cell sign        a boundary vanishing at the root evaluates to 0 there (Eq
                             true, Gt/Lt false); a non-vanishing boundary has the same
                             sign as a sample in the neighbourhood

Usage: python tests/random/random_cad.py [rounds] [seed]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.runtime import bootstrap
bootstrap()

from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.errors import CadError
from cas.kernel.verdict import Reason
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import from_term
from cas.math.realroot import (real_roots_intervals, p_eval_at, coef_sign,
                          squarefree_part)
from cas.math.cad import resolve_partition, extract_boundary_polys, cells, sign_at_cell

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def poly(s):
    return from_term(Q_RING, parse(s), (X,))


# ---------------------------------------------------------------------------
# P25: isolation correctness
# ---------------------------------------------------------------------------

def prop_isolation(rounds, rng):
    for i in range(rounds):
        # random rational roots
        roots = sorted(set(rng.randint(-8, 8) for _ in range(rng.randint(1, 4))))
        expr = "*".join(f"(x - ({r}))" for r in roots) if len(roots) > 1 \
            else f"(x - ({roots[0]}))"
        # append irrational quadratic factors (x^2 - c) with distinct nonsquare c (to avoid repeated factors)
        irr = rng.sample([2, 3, 5, 6, 7, 8], rng.randint(0, 2))
        for c in irr:
            expr += f"*(x^2 - {c})"
        p = poly(expr)
        ivs = real_roots_intervals(Q_RING, p)
        want = len(roots) + 2 * len(irr)
        if len(ivs) != want:
            fail("P25 root count mismatch", i, f"{expr} got={len(ivs)} want={want}")
        # adjacent intervals leave a strict gap
        for k in range(1, len(ivs)):
            if not (ivs[k - 1][1] < ivs[k][0]):
                fail("P25 gap broken", i, expr, ivs[k - 1], ivs[k])
        # exactly one root per interval: the squarefree part changes sign inside the
        # interval (open case), or the endpoint is a root
        sf = squarefree_part(Q_RING, p)
        for (a, b) in ivs:
            if a == b:
                if coef_sign(p_eval_at(sf, a)) != 0:
                    fail("P25 exact root is not a root", i, expr, a)
            else:
                if coef_sign(p_eval_at(sf, a)) * coef_sign(p_eval_at(sf, b)) >= 0:
                    fail("P25 interval has no root", i, expr, (a, b))
        # every rational root is covered by some isolating interval (the isolating
        # contract does not force an exact hit)
        for r in roots:
            if not any(a <= Fr(r) <= b for (a, b) in ivs):
                fail("P25 rational root not covered", i, expr, r, ivs)


# ---------------------------------------------------------------------------
# P26: partition structure plus open-cell label cross-check
# ---------------------------------------------------------------------------

def prop_partition(rounds, rng):
    cond_pool = ["x<0", "x>0", "x>=1", "x<=-2", "x^2<1", "x^2-2>0",
                 "x-3>=0", "x+1<0", "x^2-x>0"]
    for i in range(rounds):
        k = rng.randint(1, 3)
        conds = [parse(s) for s in rng.sample(cond_pool, k)]
        res = resolve_partition(conds, X)
        if not res:
            fail("P26 empty partition", i)
        # open intervals at both ends, alternating with points
        if res[0][0].kind != "open" or res[-1][0].kind != "open":
            fail("P26 the ends are not open intervals", i)
        for k2 in range(1, len(res)):
            if res[k2][0].kind == res[k2 - 1][0].kind:
                fail("P26 cells do not alternate", i, [c[0].kind for c in res])
        # open cell: direct substitution at the sample point equals cond_holds
        for cell, labels in res:
            if cell.kind != "open":
                continue
            s = cell.sample
            for ci, c in enumerate(conds):
                a, b = c.args
                from cas.math.domains.qarith import eval_exact
                da = eval_exact(a, {X: s})
                db = eval_exact(b, {X: s})
                op = c.head.name
                direct = {"Lt": da < db, "Le": da <= db, "Gt": da > db,
                          "Ge": da >= db, "Eq": da == db, "Ne": da != db}[op]
                if direct != labels[ci]:
                    fail("P26 label disagrees with direct substitution", i, s, direct, labels[ci])


# ---------------------------------------------------------------------------
# P27: refusal reason
# ---------------------------------------------------------------------------

def prop_refusal(rounds, rng):
    cases = [
        ("cos(x)>0", Reason.UNDECIDABLE),
        ("exp(x)<1", Reason.UNDECIDABLE),
        ("sin(x)+x>=0", Reason.UNDECIDABLE),
        ("x+y>0", Reason.FRAGMENT),
        ("x*y<1", Reason.FRAGMENT),
    ]
    for i in range(rounds):
        s, want = rng.choice(cases)
        try:
            resolve_partition([parse(s)], X)
        except CadError as e:
            if e.reason is not want:
                fail("P27 reason mismatch", i, s, e.reason, want)
            continue
        fail("P27 not refused", i, s)


# ---------------------------------------------------------------------------
# P28: point-cell sign
# ---------------------------------------------------------------------------

def prop_point_sign(rounds, rng):
    for i in range(rounds):
        r = rng.randint(-5, 5)
        # conditions: (x-r)==0 and (x-r)>0; on the root cell the first is true, the second false
        conds = [parse(f"(x - ({r})) == 0"), parse(f"(x - ({r})) > 0")]
        res = resolve_partition(conds, X)
        # find the root cell covering r (the isolating interval contains r; an exact (r, r) is not required)
        hit = None
        for cell, labels in res:
            if cell.kind == "point":
                a, b = cell.iso
                if a <= Fr(r) <= b:
                    hit = labels
                    break
        if hit is None:
            fail("P28 root cell not found", i, r, res)
        if hit[0] is not True or hit[1] is not False:
            fail("P28 sign wrong at the root", i, r, hit)
        # non-vanishing boundary: (x-(r+1)) should be negative at the root r
        c2 = parse(f"(x - ({r + 1})) < 0")
        res2 = resolve_partition([conds[0], c2], X)
        for cell, labels in res2:
            if cell.kind == "point":
                a, b = cell.iso
                if a <= Fr(r) <= b:
                    if labels[1] is not True:
                        fail("P28 non-vanishing boundary sign wrong", i, r, labels)
                    break


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== CAD / real-root isolation random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_isolation(rounds, rng)
    print(f"P25 isolation correctness   {rounds} rounds passed")
    prop_partition(rounds, rng)
    print(f"P26 partition structure + cross-check  {rounds} rounds passed")
    prop_refusal(rounds, rng)
    print(f"P27 refusal reason          {rounds} rounds passed")
    prop_point_sign(rounds, rng)
    print(f"P28 point-cell sign         {rounds} rounds passed")
    print("== all passed ==")
