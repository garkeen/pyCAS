# -*- coding: utf-8 -*-
"""Random piecewise differentiation, solving, and workflow checks.

The bench is fully self-proving: every result is checked by an independent
channel rather than an external oracle.

  P36 piecewise differentiation  random piecewise polynomials: the per-branch
                                 derivative equals the domain-layer derivative
                                 (independently rebuilt via p_deriv, so two channels);
                                 and the breakpoint cell set equals the boundary point set
  P37 piecewise equation solving  random piecewise linear function = target: point
                                 solutions equal an independent reference (per-branch
                                 -b/a candidates filtered by direct rational comparison
                                 against the branch condition); region solutions
                                 (constant branch, identity), conditional solutions, and
                                 nonlinear branches are refused when appropriate
  P38 workflow end to end        Claim(piecewise equation) -> every Solve point
                                 solution is committed and verified (the
                                 back-substitution judge takes the piecewise
                                 branch-selection channel); Claim(piecewise) -> a Diff
                                 step passes the per-branch domain cross-check; and a
                                 spurious solution (a candidate failing its condition) is
                                 refused by the judge

Usage: python tests/random/random_piecewise_workflow.py [rounds] [seed]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.runtime import new_workflow
from cas.runtime import bootstrap
from cas.runtime.dispatch import install

install(bootstrap())      # a standalone bench has no conftest: assemble explicitly

import cas.syntax.term as T
from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.domains.qarith import fold
from cas.math.diff import differentiate_piecewise
from cas.math.tactics import solve_piecewise, TacticsError
from cas.errors import DiffError, CadError
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import from_term, p_deriv, to_term
from cas.math.piecewise import piecewise, fold_nested, branches
from cas.workflow.command import Claim, Solve, Diff

X = S("x")


def _ctx():
    """The installed math context: the bench assembled its own runtime above."""
    from cas.runtime import get_runtime
    return get_runtime().math


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_lin(rng):
    """Random linear function a*x + b with a != 0; returns (term, a, b)."""
    a = Fr(rng.randint(-5, 5), rng.choice((1, 1, 2)))
    while a == 0:
        a = Fr(rng.randint(-5, 5), 2)
    b = Fr(rng.randint(-6, 6), rng.choice((1, 1, 3)))
    t = T.plus(T.times(T.N(a), X), T.N(b))
    return fold(t), a, b


def _num(t):
    f = fold(t)
    if not T.is_num(f):
        return None
    return T.num_val(f)


# ---------------------------------------------------------------------------
# P36: piecewise differentiation -- per-branch two-channel cross-check plus
# breakpoint location
# ---------------------------------------------------------------------------

def prop_piecewise_diff(rounds, rng):
    for i in range(rounds):
        r = Fr(rng.randint(-4, 4), rng.choice((1, 1, 2)))
        p1, _, _ = rand_lin(rng)
        p2, _, _ = rand_lin(rng)
        pw = piecewise([(p1, parse(f"x <= {r}")), (p2, parse(f"x > {r}"))])
        try:
            deriv, bounds = differentiate_piecewise(_ctx(), pw, X)
        except (DiffError, CadError) as e:
            fail("P36 piecewise differentiation refused", i, to_str(pw), e)
        bs = branches(fold_nested(deriv))
        if len(bs) != 2:
            fail("P36 derivative branch count", i, to_str(deriv))
        # per branch: term-layer result vs domain-layer derivative (independently rebuilt via p_deriv)
        for (v, c), src in zip(bs, (p1, p2)):
            p = from_term(Q_RING, src, (X,))
            expect = to_term(Q_RING, p_deriv(Q_RING, p, 0))
            got = fold(v)
            if _num(T.plus(got, T.neg(expect))) != 0:
                fail("P36 per-branch derivative disagrees with the domain layer", i, to_str(src),
                     to_str(got), to_str(expect))
        # breakpoint cell set equals the boundary point set
        pts = [c.iso[0] for c in bounds if c.iso[0] == c.iso[1]]
        if pts != [r]:
            fail("P36 breakpoint set", i, r, pts)


# ---------------------------------------------------------------------------
# P37: piecewise equation solving -- independent reference (direct arithmetic, not the
# decision pipeline)
# ---------------------------------------------------------------------------

def ref_solve(pairs, target):
    """Reference channel: per-branch -b/a candidates filtered by direct rational
    comparison against the branch condition."""
    out = []
    for (a, b, lo, hi, lo_open, hi_open) in pairs:
        cand = (target - b) / a
        if lo is not None and (cand <= lo if lo_open else cand < lo):
            continue
        if hi is not None and (cand >= hi if hi_open else cand > hi):
            continue
        out.append(cand)
    return sorted(out)


def prop_piecewise_solve(rounds, rng):
    for i in range(rounds):
        r = Fr(rng.randint(-4, 4), 1)
        t1, a1, b1 = rand_lin(rng)
        t2, a2, b2 = rand_lin(rng)
        pw = piecewise([(t1, parse(f"x <= {r}")), (t2, parse(f"x > {r}"))])
        target = Fr(rng.randint(-6, 6), 1)
        try:
            res = solve_piecewise(_ctx(), pw, X, T.N(target))
        except TacticsError as e:
            fail("P37 a linear piecewise was refused", i, to_str(pw), e)
        got = sorted(T.num_val(s) for s in res["points"])
        want = ref_solve([(a1, b1, None, r, True, False),
                          (a2, b2, r, None, True, True)], target)
        if got != want:
            fail("P37 point solutions disagree with the reference", i, to_str(pw), target, got, want)
        if res["regions"] or res["conditional"]:
            fail("P37 a linear piecewise should have no region/conditional solution", i, res)
        # constant branch identity -> region solution
        c_pw = piecewise([(T.N(target), parse(f"x < {r}")),
                          (T.N(target + 1), parse(f"x >= {r}"))])
        res2 = solve_piecewise(_ctx(), c_pw, X, T.N(target))
        if len(res2["regions"]) != 1 or res2["points"]:
            fail("P37 region solution missing", i, res2)
        # nonlinear branch -> honest refusal
        nl = piecewise([(parse("x*x"), parse(f"x <= {r}")),
                        (t2, parse(f"x > {r}"))])
        try:
            solve_piecewise(_ctx(), nl, X, T.N(target))
            fail("P37 a nonlinear branch was not refused", i)
        except TacticsError:
            pass
        # target containing x: the solution of the constant branch equation k1 = m*x+b must
        # not be lost in the branch classification, and a degenerate branch (identity ->
        # region solution, contradiction -> no contribution) must not be misrefused. The
        # reference is direct arithmetic.
        k1 = Fr(rng.randint(-5, 5), 1)
        m = Fr(rng.randint(-4, 4), rng.choice((1, 1, 2)))
        while m == 0:
            m = Fr(rng.randint(-4, 4), 2)
        b = Fr(rng.randint(-5, 5), 1)
        a2v = Fr(rng.randint(-4, 4), rng.choice((1, 1, 2)))
        while a2v == m:                    # equal slopes are tested separately below
            a2v = Fr(rng.randint(-4, 4), 2)
        b2v = Fr(rng.randint(-5, 5), 1)
        tgt = fold(T.plus(T.times(T.N(m), X), T.N(b)))
        pw3 = piecewise([(T.N(k1), parse(f"x <= {r}")),
                         (fold(T.plus(T.times(T.N(a2v), X), T.N(b2v))),
                          parse(f"x > {r}"))])
        res3 = solve_piecewise(_ctx(), pw3, X, tgt)
        want3 = []
        x1 = (k1 - b) / m                  # k1 = m*x + b
        if x1 <= r:
            want3.append(x1)
        x2 = (b - b2v) / (a2v - m)         # a2*x + b2 = m*x + b
        if x2 > r:
            want3.append(x2)
        got3 = sorted(T.num_val(s) for s in res3["points"])
        if got3 != sorted(want3) or res3["regions"] or res3["conditional"]:
            fail("P37 x-bearing target lost or gained solutions", i, k1, m, b, a2v, b2v, r,
                 got3, sorted(want3), res3)
        # identity branch (v == target, difference shape contains x and is identically zero
        # after projection) -> region solution
        id_pw = piecewise([(tgt, parse(f"x <= {r}")),
                           (T.N(k1), parse(f"x > {r}"))])
        res4 = solve_piecewise(_ctx(), id_pw, X, tgt)
        want4 = [x1] if x1 > r else []
        got4 = sorted(T.num_val(s) for s in res4["points"])
        if len(res4["regions"]) != 1 or got4 != sorted(want4) \
                or res4["conditional"]:
            fail("P37 identity branch gave no region solution", i, k1, m, b, r, res4, want4)
        # contradiction branch (v = target+1, difference a nonzero constant after projection)
        # -> no contribution
        con_pw = piecewise([(fold(T.plus(tgt, T.N(1))), parse(f"x <= {r}")),
                            (T.N(k1), parse(f"x > {r}"))])
        res5 = solve_piecewise(_ctx(), con_pw, X, tgt)
        want5 = [x1] if x1 > r else []
        got5 = sorted(T.num_val(s) for s in res5["points"])
        if got5 != sorted(want5) or res5["regions"] or res5["conditional"]:
            fail("P37 contradiction branch did not stay silent", i, k1, m, b, r, res5, want5)


# ---------------------------------------------------------------------------
# P38: workflow end to end (the engine layer of the REPL channel)
# ---------------------------------------------------------------------------

def prop_workflow(rounds, rng):
    for i in range(rounds):
        r = Fr(rng.randint(-4, 4), 1)
        t1, a1, b1 = rand_lin(rng)
        t2, a2, b2 = rand_lin(rng)
        target = Fr(rng.randint(-6, 6), 1)
        wf = new_workflow()
        s0 = wf.add(T.eq(piecewise([(t1, parse(f"x <= {r}")),
                                    (t2, parse(f"x > {r}"))]),
                         T.N(target)), Claim())
        want = ref_solve([(a1, b1, None, r, True, False),
                          (a2, b2, r, None, True, True)], target)
        for xv in want:
            s = wf.add(T.eq(X, T.N(xv)), Solve(pred=s0.id, var=X,
                                               solution=T.N(xv)))
            if s.status == "refused":
                fail("P38 a true solution was refused by the back-substitution judge", i, r, target, xv, s.note)
        # spurious solution: the other branch's candidate (failing its condition) must be refused
        wrong = ref_solve([(a1, b1, r, None, True, True)], target)  # force the right region
        for xv in wrong:
            if xv in want:
                continue
            s = wf.add(T.eq(X, T.N(xv)), Solve(pred=s0.id, var=X,
                                               solution=T.N(xv)))
            if s.status != "refused":
                fail("P38 a spurious solution was not refused", i, r, target, xv)
        # piecewise differentiation step: the per-branch domain cross-check must pass
        s1 = wf.add(piecewise([(t1, parse(f"x <= {r}")),
                               (t2, parse(f"x > {r}"))]), Claim())
        d, _b = differentiate_piecewise(_ctx(), s1.content, X)
        s2 = wf.add(d, Diff(pred=s1.id, var=X))
        if s2.status == "refused":
            fail("P38 piecewise Diff was refused by the cross-check", i, to_str(s1.content),
                 to_str(d), s2.note)


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260828
    print(f"== piecewise workflow random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_piecewise_diff(rounds, rng)
    print(f"P36 piecewise differentiation two-channel  {rounds} rounds passed")
    prop_piecewise_solve(rounds, rng)
    print(f"P37 piecewise equation solving reference   {rounds} rounds passed")
    prop_workflow(rounds, rng)
    print(f"P38 workflow end to end                    {rounds} rounds passed")
    print("== all passed ==")
