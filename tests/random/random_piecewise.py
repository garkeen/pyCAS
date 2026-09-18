# -*- coding: utf-8 -*-
"""Piecewise container randomized bench.

Four properties, all self-proving with no external ground truth:
  P21 independent projection  branch bodies project into their own host domains with no
                              requirement of a shared host -- the per-branch project and
                              an independent project agree branch for branch, and
                              polynomial and rational-function branches (even ones
                              outside the fragment) coexist in one container without error
  P22 branch-selection semantics  select hits "the first true branch with all earlier
                              ones false": force a unique hit with ledger facts (assume
                              that branch's condition, refute the earlier ones) and it
                              returns that branch's value
  P23 per-branch lifting      lift(op, p, q) expands the Cartesian product: branch count
                              is the product and conditions are conjoined; and in a
                              uniquely-hit context select(lift) == op(select p, select q)
  P24 guarded conditions      dom_condition on a piecewise guards each branch body as
                              not-cond or constraint, matching per-branch extraction
                              followed by guarding; overlap consistency gives YES for a
                              provably empty overlap and NO for a provably unequal
                              constant overlap

Usage: python tests/random/random_piecewise.py [rounds] [seed]
"""

import sys
import random

sys.path.insert(0, ".")

from cas.runtime import bootstrap
bootstrap()

from cas.syntax import term as T
from cas.syntax.term import S, N, mk, plus, times, pw
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.kernel.scope import Assumptions
from cas.math.project import project
from cas.kernel.verdict import YES, NO
from cas.math.domcond import dom_condition
from cas.math.piecewise import (piecewise, branches, project_pw, select, coverage,
                           conflicts, lift, is_piecewise)

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_cmp(rng):
    """A strict comparison of x against a constant, used as a branch condition."""
    op = rng.choice(("Gt", "Lt", "Ge", "Le"))
    k = rng.randint(-5, 5)
    return mk(S(op), (X, N(k)))


_COND_POOL = [mk(S(op), (X, N(k)))
              for op in ("Gt", "Lt", "Ge", "Le") for k in range(-5, 6)]


def rand_pw(rng, nvals, minb=2, maxb=4):
    """Random piecewise container: distinct branch conditions (no repeats) with a final
    TRUE fallback guaranteeing coverage."""
    nb = rng.randint(minb, maxb)
    conds = rng.sample(_COND_POOL, nb - 1)         # pairwise distinct comparisons
    pairs = [(rng.choice(nvals), c) for c in conds]
    pairs.append((rng.choice(nvals), T.TRUE))
    return piecewise(pairs)


def at_ctx(a):
    """Assumption set for the concrete point x = a (a numeric comparison, so decidable)."""
    return Assumptions().extended(mk(S("Eq"), (X, N(a))))


def eval_at(c, a) -> bool:
    if c is T.TRUE:
        return True
    op = c.head.name
    b = T.num_val(c.args[1])
    return {"Gt": a > b, "Lt": a < b, "Ge": a >= b, "Le": a <= b}[op]


def ref_first(t, a):
    """Reference scan: the value of the first hit branch at x = a (the definitional truth,
    independent of select)."""
    for v, c in branches(t):
        if eval_at(c, a):
            return v
    return None


# ---------------------------------------------------------------------------
# P21: independent branch projection
# ---------------------------------------------------------------------------

def prop_projection(rounds, rng):
    het = [pw(X, N(2)),                            # K[x]
           parse("1/x"),                           # K(x)
           parse("(x^2+1)/(x-3)"),                 # K(x)
           X,                                      # K[x]
           parse("sin(x)")]                        # outside the fragment (no tower) -> None
    for i in range(rounds):
        nb = rng.randint(2, 5)
        picks = [rng.choice(het) for _ in range(nb)]
        conds = [rand_cmp(rng) for _ in range(nb - 1)] + [T.TRUE]
        t = piecewise(list(zip(picks, conds)))
        proj = project_pw(t)
        if len(proj) != len(branches(t)):
            fail("P21 branch count mismatch", i)
        for k, (v, c, hit) in enumerate(proj):
            solo = project(v)                       # independent projection
            a = hit.name if hit else None
            b = solo.name if solo else None
            if a != b:
                fail("P21 projection is not per-branch independent", i, f"branch={k} v={to_str(v)}",
                     f"pw={a} solo={b}")
        # the key ruling: heterogeneous hosts coexist (polynomial + rational + out-of-fragment
        # branches) with no shared host required
        names = [h.name if h else None for _v, _c, h in proj]
        if "K[x]" in names and "K(x)" in names and not is_piecewise(t):
            fail("P21 misjudged as non-piecewise", i)


# ---------------------------------------------------------------------------
# P22: branch-selection semantics (first true branch with all earlier false -> unique hit)
# ---------------------------------------------------------------------------

def prop_select(rounds, rng):
    vals = [N(k) for k in range(1, 6)]
    for i in range(rounds):
        t = rand_pw(rng, vals)
        for a in range(-7, 8):
            want = ref_first(t, a)
            st, payload = select(t, at_ctx(a))
            if want is None:
                if st == "value":
                    fail("P22 false hit with no branch holding", i, f"a={a}", to_str(t))
                continue
            if st != "value":
                fail("P22 concrete point did not collapse", i, f"a={a}", f"t={to_str(t)}",
                     f"payload={payload}")
            if payload is not want:
                fail("P22 wrong branch selected", i, f"a={a} want={to_str(want)} "
                     f"got={to_str(payload)} t={to_str(t)}")
        # the final TRUE branch always covers, so an empty context must not falsely report a gap (NO)
        if coverage(t, Assumptions()) is NO:
            fail("P22 coverage misjudged", i, to_str(t))


# ---------------------------------------------------------------------------
# P23: per-branch operation lifting
# ---------------------------------------------------------------------------

def prop_lift(rounds, rng):
    vals = [N(k) for k in range(-4, 5)]
    for i in range(rounds):
        p = rand_pw(rng, vals, minb=2, maxb=3)
        q = rand_pw(rng, vals, minb=2, maxb=3)
        m = lift(T.plus, p, q)
        bp, bq = branches(p), branches(q)
        if len(branches(m)) != len(bp) * len(bq):
            fail("P23 expanded branch count", i,
                 f"{len(branches(m))} != {len(bp)}*{len(bq)}")
        # pointwise agreement: at x = a, select(lift(plus,p,q)) == plus(select p, select q)
        for a in range(-7, 8):
            ctx = at_ctx(a)
            _, vp = select(p, ctx)
            _, vq = select(q, ctx)
            st_m, vm = select(m, ctx)
            if st_m != "value":
                fail("P23 lifted container did not hit", i, f"a={a}")
            if plus(vp, vq) is not vm:
                fail("P23 pointwise disagreement", i, f"a={a} "
                     f"plus({to_str(vp)},{to_str(vq)})={to_str(plus(vp,vq))} "
                     f"vs {to_str(vm)}")


# ---------------------------------------------------------------------------
# P24: guarded conditions plus overlap consistency
# ---------------------------------------------------------------------------

def prop_guards(rounds, rng):
    bodies = [T.call("Sqrt", X), parse("log(x)"), pw(X, N(-1)),
              T.call("Sqrt", plus(pw(X, N(2)), N(1)))]
    for i in range(rounds):
        nb = rng.randint(2, 4)
        pairs = []
        conds = [rand_cmp(rng) for _ in range(nb - 1)] + [T.TRUE]
        for k in range(nb):
            pairs.append((rng.choice(bodies), conds[k]))
        t = piecewise(pairs)
        got = dom_condition(t)
        # expected: each branch body's own constraints guarded as not-cond or g (a TRUE
        # branch needs no guard)
        want = []
        for v, c in branches(t):
            solo = dom_condition(v)
            neg = T.FALSE if c is T.TRUE else mk(S("Not"), (c,))
            for g in solo:
                want.append(mk(S("Or"), (neg, g)))
        if sorted(x._h for x in got) != sorted(x._h for x in want):
            fail("P24 guarded conditions mismatch", i,
                 f"got={[to_str(x) for x in got]}",
                 f"want={[to_str(x) for x in want]}")
        # overlap consistency: constant branches with a provably empty overlap -> all YES;
        # a provably unequal constant overlap -> NO
        disjoint = piecewise([(N(1), mk(S("Gt"), (X, N(0)))),
                              (N(2), mk(S("Lt"), (X, N(0))))])
        for _a, _b, verdict in conflicts(disjoint, Assumptions()):
            if verdict is not YES:
                fail("P24 empty overlap misjudged", i, verdict)
        clash = piecewise([(N(1), mk(S("Gt"), (X, N(0)))),
                           (N(2), mk(S("Gt"), (X, N(0))))])
        vs = [verdict for _a, _b, verdict in conflicts(clash, Assumptions())]
        if not any(v is NO for v in vs):
            fail("P24 constant conflict not detected", i, vs)


# ---------------------------------------------------------------------------
# P29-P31: nested flattening + domain cells + connected components (consuming CAD)
# ---------------------------------------------------------------------------

from cas.math.piecewise import fold_nested, domain_cells, connected_components
from cas.math.domains.qarith import eval_exact


def eval_prop(c, a):
    """Truth value of a proposition at x = a (rational), a reference implementation
    independent of CAD."""
    if c is T.TRUE:
        return True
    if c is T.FALSE:
        return False
    h = c.head.name
    if h == "And":
        return all(eval_prop(x, a) for x in c.args)
    if h == "Or":
        return any(eval_prop(x, a) for x in c.args)
    if h == "Not":
        return not eval_prop(c.args[0], a)
    l = eval_exact(c.args[0], {X: T.num_val(N(a))})
    r = eval_exact(c.args[1], {X: T.num_val(N(a))})
    return {"Lt": l < r, "Le": l <= r, "Gt": l > r,
            "Ge": l >= r, "Eq": l == r, "Ne": l != r}[h]


def ref_eval(t, a):
    """First-match value of a nested piecewise at x = a (recursive reference
    implementation)."""
    if not is_piecewise(t):
        return t
    for v, c in branches(t):
        if eval_prop(c, a):
            return ref_eval(v, a)
    return T.SP("Undefined")


def _same(u, v):
    if T.is_num(u) and T.is_num(v):
        return T.num_val(u) == T.num_val(v)
    return u is v


def prop_fold_nested(rounds, rng):
    vals = [N(k) for k in range(1, 6)]
    for i in range(rounds):
        inner = piecewise([(rng.choice(vals), rand_cmp(rng)),
                           (rng.choice(vals), rand_cmp(rng)),
                           (rng.choice(vals), T.TRUE)])
        outer = piecewise([(inner, rand_cmp(rng)),
                           (rng.choice(vals), rand_cmp(rng)),
                           (rng.choice(vals), T.TRUE)])
        fl = fold_nested(outer)
        if not is_piecewise(fl):
            fail("P29 flattened form is not piecewise", i)
        if any(is_piecewise(v) for v, _c in branches(fl)):
            fail("P29 flattening incomplete", i, to_str(fl))
        if fold_nested(fl) is not fl:
            fail("P29 flattening is not idempotent", i)
        # pointwise agreement: the nested original and the flattened form take the same value
        for _ in range(12):
            a = rng.randint(-6, 6)
            if not _same(ref_eval(outer, a), ref_eval(fl, a)):
                fail("P29 flattening pointwise mismatch", i, f"a={a}",
                     to_str(outer), to_str(fl))


def prop_components(rounds, rng):
    vals = [N(k) for k in range(1, 4)]
    for i in range(rounds):
        t = rand_pw(rng, vals, minb=2, maxb=4)
        dom = domain_cells(t, X)
        comps = connected_components(dom)
        # total cells inside components == number of defined cells (Undefined enters no component)
        defined = sum(1 for _c, v in dom if v is not T.SP("Undefined"))
        got = sum(len(c.cells) for c in comps)
        if got != defined:
            fail("P30 component cell count mismatch", i, got, defined)
        # a TRUE fallback implies full coverage, hence exactly one connected component
        if any(c is T.TRUE for _v, c in branches(t)) and len(comps) != 1:
            fail("P30 full coverage should be a single component", i, len(comps))


def prop_gap(rounds, rng):
    for i in range(rounds):
        lo = rng.randint(-5, -1)
        hi = rng.randint(1, 5)
        # domain is x<lo or x>hi: the middle is a gap, so exactly two connected components
        t = piecewise([(N(1), mk(S("Lt"), (X, N(lo)))),
                       (N(2), mk(S("Gt"), (X, N(hi))))])
        dom = domain_cells(t, X)
        comps = connected_components(dom)
        if len(comps) != 2:
            fail("P31 a gap should split into exactly 2 components", i, lo, hi, len(comps))
        # the two components should take the values 1 and 2 (left and right regions)
        vals = set()
        for c in comps:
            v = c.cells[0][1]
            if not T.is_num(v):
                fail("P31 component value is not numeric", i, to_str(v))
            vals.add(T.num_val(v))
        if vals != {T.num_val(N(1)), T.num_val(N(2))}:
            fail("P31 component values mismatch", i, vals)
        # an open cell inside the gap (both bounds present) must stay undefined: never
        # integrate the gap to 0
        for cell, v in dom:
            if cell.kind == "open" and cell.lo is not None \
                    and cell.hi is not None and v is not T.SP("Undefined"):
                fail("P31 a gap cell was defined", i, lo, hi)


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== piecewise container random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_projection(rounds, rng)
    print(f"P21 independent projection        {rounds} rounds passed")
    prop_select(rounds, rng)
    print(f"P22 branch-selection semantics    {rounds} rounds passed")
    prop_lift(min(rounds, 200), rng)
    print(f"P23 per-branch lifting            {min(rounds,200)} rounds passed")
    prop_guards(rounds, rng)
    print(f"P24 guarded conditions + overlap  {rounds} rounds passed")
    prop_fold_nested(rounds, rng)
    print(f"P29 nested flattening pointwise   {rounds} rounds passed")
    prop_components(rounds, rng)
    print(f"P30 connected-component split     {rounds} rounds passed")
    prop_gap(rounds, rng)
    print(f"P31 gap disconnection             {rounds} rounds passed")
    print("== all passed ==")
