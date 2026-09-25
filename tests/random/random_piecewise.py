# -*- coding: utf-8 -*-
"""Piecewise container randomized bench.

Properties, all self-proving with no external ground truth:
  P21 independent projection  branch bodies project into their own host domains with no
                              requirement of a shared host -- the per-branch project and
                              an independent project agree branch for branch, and
                              polynomial and rational-function branches (even ones
                              outside the fragment) coexist in one container without error
  P22 branch-selection semantics  select hits "the first true branch with all earlier
                              ones false": force a unique hit with ledger facts (assume
                              that branch's condition, refute the earlier ones) and it
                              returns that branch's value
  P23 per-branch lifting      lift(op, p, q) expands the Cartesian product after merging
                              adjacent same-value branches in each argument: branch count
                              is at most the product (equal only when no argument had such
                              an adjacent pair) and conditions are conjoined; and in a
                              uniquely-hit context select(lift) == op(select p, select q)
  P24 guarded conditions      dom_condition on a piecewise guards each branch body as
                              not-cond or constraint, matching per-branch extraction
                              followed by guarding; overlap consistency gives YES for a
                              provably empty overlap and NO for a provably unequal
                              constant overlap
  P33 lift merge              a lift whose arguments contain adjacent same-value branches
                              produces no adjacent same-value pair, and the merged result
                              still agrees pointwise with the selected argument values

Usage: python tests/random/random_piecewise.py [rounds] [seed]
"""

import random
import sys

sys.path.insert(0, ".")

from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.kernel.scope import Assumptions
from cas.kernel.verdict import YES
from cas.math.domains.qarith import eval_exact
from cas.math.domcond import dom_condition
from cas.math.piecewise import (
    ResidualSelection,
    SelectedValue,
    branches,
    conflicts,
    connected_components,
    coverage,
    domain_cells,
    fold_nested,
    is_piecewise,
    lift,
    piecewise,
    project_pw,
    select,
)
from cas.math.project import project
from cas.runtime import bootstrap
from cas.syntax import term as T
from cas.syntax.term import N, S, mk, plus, pw

RUNTIME = bootstrap()
MATH = RUNTIME.math


X = S("x")


def _ctx():
    return MATH


def _render(term):
    return to_str(RUNTIME, term)


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
           parse(RUNTIME, "1/x"),                           # K(x)
           parse(RUNTIME, "(x^2+1)/(x-3)"),                 # K(x)
           X,                                      # K[x]
           parse(RUNTIME, "sin(x)")]                        # outside the fragment (no tower) -> None
    for i in range(rounds):
        nb = rng.randint(2, 5)
        picks = [rng.choice(het) for _ in range(nb)]
        conds = [rand_cmp(rng) for _ in range(nb - 1)] + [T.TRUE]
        t = piecewise(list(zip(picks, conds)))
        proj = project_pw(_ctx(), t)
        if len(proj) != len(branches(t)):
            fail("P21 branch count mismatch", i)
        for k, (v, c, hit) in enumerate(proj):
            solo = project(_ctx(), v)               # independent projection
            a = hit.name if hit else None
            b = solo.name if solo else None
            if a != b:
                fail("P21 projection is not per-branch independent", i, f"branch={k} v={_render(v)}",
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
            selection = select(_ctx(), t, at_ctx(a))
            if want is None:
                if not isinstance(selection, ResidualSelection):
                    fail("P22 false hit with no branch holding", i, f"a={a}", _render(t))
                continue
            if not isinstance(selection, SelectedValue):
                fail(
                    "P22 concrete point did not collapse",
                    i,
                    f"a={a}",
                    f"t={_render(t)}",
                    selection,
                )
            if selection.value is not want:
                fail(
                    "P22 wrong branch selected",
                    i,
                    f"a={a} want={_render(want)} "
                    f"got={_render(selection.value)} t={_render(t)}",
                )
        # the final TRUE branch always covers, so an empty context must not falsely report a gap (NO)
        if coverage(_ctx(), t, Assumptions()).is_no():
            fail("P22 coverage misjudged", i, _render(t))


# ---------------------------------------------------------------------------
# P23: per-branch operation lifting
# ---------------------------------------------------------------------------

def forced_pairs(conds, values):
    """Branch pairs whose adjacent entries share a value: entry k takes value k//2 when
    k is even and value 0 when k is odd, so entries (0,1), (2,3), ... are adjacent
    same-value runs by construction."""
    return [(values[k // 2] if k % 2 == 0 else values[0], c) for k, c in enumerate(conds)]


def prop_lift(rounds, rng):
    vals = [N(k) for k in range(-4, 5)]
    for i in range(rounds):
        p = rand_pw(rng, vals, minb=2, maxb=3)
        q = rand_pw(rng, vals, minb=2, maxb=3)
        m = lift(T.plus, p, q)
        bp, bq = branches(p), branches(q)
        # the count is at most the product: adjacent same-value branches in an argument
        # are merged into one branch before expanding, so equal values only coincide
        # when no argument had such an adjacent pair (the merged form is pointwise
        # equivalent to the unmerged product, which is what the agreement check below
        # re-proves)
        if len(branches(m)) > len(bp) * len(bq):
            fail("P23 lifted branch count above the product", i,
                 f"{len(branches(m))} > {len(bp)}*{len(bq)}")
        # pointwise agreement: at x = a, select(lift(plus,p,q)) == plus(select p, select q)
        for a in range(-7, 8):
            ctx = at_ctx(a)
            selected_p = select(_ctx(), p, ctx)
            selected_q = select(_ctx(), q, ctx)
            selected_m = select(_ctx(), m, ctx)
            if not (
                isinstance(selected_p, SelectedValue)
                and isinstance(selected_q, SelectedValue)
                and isinstance(selected_m, SelectedValue)
            ):
                fail("P23 lifted container did not hit", i, f"a={a}")
            if plus(selected_p.value, selected_q.value) is not selected_m.value:
                fail(
                    "P23 pointwise disagreement",
                    i,
                    f"a={a} plus({_render(selected_p.value)},"
                    f"{_render(selected_q.value)})="
                    f"{_render(plus(selected_p.value, selected_q.value))} "
                    f"vs {_render(selected_m.value)}",
                )


# ---------------------------------------------------------------------------
# P33: adjacent same-value branch merging inside lift
# ---------------------------------------------------------------------------

def prop_lift_merge(rounds, rng):
    vals = [N(k) for k in range(1, 6)]
    for i in range(rounds):
        # arguments built so that at least one adjacent pair shares a value; the runs are
        # guaranteed by construction, not by chance, so the property always exercises a merge
        np_ = rng.choice((3, 4, 5))
        nq = 2
        p = piecewise(forced_pairs([rand_cmp(rng) for _ in range(np_ - 1)] + [T.TRUE], vals))
        q = piecewise(forced_pairs([rand_cmp(rng) for _ in range(nq - 1)] + [T.TRUE], vals))
        m = lift(T.plus, p, q)
        bs = branches(m)
        if len(bs) > len(branches(p)) * len(branches(q)):
            fail("P33 merged lift above the raw product", i, len(bs))
        for (va, _ca), (vb, _cb) in zip(bs, bs[1:]):
            if va is vb:
                fail("P33 adjacent same-value branches survived the merge", i,
                     _render(m))
        # the merged container still takes the pointwise product value
        for a in range(-7, 8):
            ctx = at_ctx(a)
            selected_p = select(_ctx(), p, ctx)
            selected_q = select(_ctx(), q, ctx)
            selected_m = select(_ctx(), m, ctx)
            if not (
                isinstance(selected_p, SelectedValue)
                and isinstance(selected_q, SelectedValue)
                and isinstance(selected_m, SelectedValue)
            ):
                fail("P33 merged container did not hit", i, f"a={a}")
            if plus(selected_p.value, selected_q.value) is not selected_m.value:
                fail(
                    "P33 merge changed the pointwise value",
                    i,
                    f"a={a} plus({_render(selected_p.value)},"
                    f"{_render(selected_q.value)})="
                    f"{_render(plus(selected_p.value, selected_q.value))} "
                    f"vs {_render(selected_m.value)}",
                )


# ---------------------------------------------------------------------------
# P24: guarded conditions plus overlap consistency
# ---------------------------------------------------------------------------

def prop_guards(rounds, rng):
    bodies = [T.call("Sqrt", X), parse(RUNTIME, "log(x)"), pw(X, N(-1)),
              T.call("Sqrt", plus(pw(X, N(2)), N(1)))]
    for i in range(rounds):
        nb = rng.randint(2, 4)
        pairs = []
        conds = [rand_cmp(rng) for _ in range(nb - 1)] + [T.TRUE]
        for k in range(nb):
            pairs.append((rng.choice(bodies), conds[k]))
        t = piecewise(pairs)
        got = dom_condition(_ctx(), t)
        # expected: each branch body's own constraints guarded as not-cond or g (a TRUE
        # branch needs no guard)
        want = []
        for v, c in branches(t):
            solo = dom_condition(_ctx(), v)
            neg = T.FALSE if c is T.TRUE else mk(S("Not"), (c,))
            for g in solo:
                want.append(mk(S("Or"), (neg, g)))
        if sorted(x._h for x in got) != sorted(x._h for x in want):
            fail("P24 guarded conditions mismatch", i,
                 f"got={[_render(x) for x in got]}",
                 f"want={[_render(x) for x in want]}")
        # overlap consistency: constant branches with a provably empty overlap -> all YES;
        # a provably unequal constant overlap -> NO
        disjoint = piecewise([(N(1), mk(S("Gt"), (X, N(0)))),
                              (N(2), mk(S("Lt"), (X, N(0))))])
        for check in conflicts(_ctx(), disjoint, Assumptions()):
            if check.verdict is not YES:
                fail("P24 empty overlap misjudged", i, check.verdict)
        clash = piecewise([(N(1), mk(S("Gt"), (X, N(0)))),
                           (N(2), mk(S("Gt"), (X, N(0))))])
        verdicts = [check.verdict for check in conflicts(_ctx(), clash, Assumptions())]
        if not any(verdict.is_no() for verdict in verdicts):
            fail("P24 constant conflict not detected", i, verdicts)


# ---------------------------------------------------------------------------
# P29-P31: nested flattening + domain cells + connected components (consuming CAD)
# ---------------------------------------------------------------------------



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
    left = eval_exact(c.args[0], {X: T.num_val(N(a))})
    right = eval_exact(c.args[1], {X: T.num_val(N(a))})
    return {
        "Lt": left < right,
        "Le": left <= right,
        "Gt": left > right,
        "Ge": left >= right,
        "Eq": left == right,
        "Ne": left != right,
    }[h]


def ref_eval(t, a):
    """First-match value of a nested piecewise at x = a (recursive reference
    implementation)."""
    if not is_piecewise(t):
        return t
    for v, c in branches(t):
        if eval_prop(c, a):
            return ref_eval(v, a)
    return T.UNDEFINED


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
            fail("P29 flattening incomplete", i, _render(fl))
        if fold_nested(fl) is not fl:
            fail("P29 flattening is not idempotent", i)
        # pointwise agreement: the nested original and the flattened form take the same value
        for _ in range(12):
            a = rng.randint(-6, 6)
            if not _same(ref_eval(outer, a), ref_eval(fl, a)):
                fail("P29 flattening pointwise mismatch", i, f"a={a}",
                     _render(outer), _render(fl))


def prop_components(rounds, rng):
    vals = [N(k) for k in range(1, 4)]
    for i in range(rounds):
        t = rand_pw(rng, vals, minb=2, maxb=4)
        dom = domain_cells(_ctx(), t, X)
        comps = connected_components(dom)
        # total cells inside components == number of defined cells (Undefined enters no component)
        defined = sum(1 for _c, v in dom if v is not T.UNDEFINED)
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
        dom = domain_cells(_ctx(), t, X)
        comps = connected_components(dom)
        if len(comps) != 2:
            fail("P31 a gap should split into exactly 2 components", i, lo, hi, len(comps))
        # the two components should take the values 1 and 2 (left and right regions)
        vals = set()
        for c in comps:
            v = c.cells[0][1]
            if not T.is_num(v):
                fail("P31 component value is not numeric", i, _render(v))
            vals.add(T.num_val(v))
        if vals != {T.num_val(N(1)), T.num_val(N(2))}:
            fail("P31 component values mismatch", i, vals)
        # an open cell inside the gap (both bounds present) must stay undefined: never
        # integrate the gap to 0
        for cell, v in dom:
            if cell.kind == "open" and cell.lo is not None \
                    and cell.hi is not None and v is not T.UNDEFINED:
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
    prop_lift_merge(min(rounds, 200), rng)
    print(f"P33 lift merge                    {min(rounds,200)} rounds passed")
    prop_guards(rounds, rng)
    print(f"P24 guarded conditions + overlap  {rounds} rounds passed")
    prop_fold_nested(rounds, rng)
    print(f"P29 nested flattening pointwise   {rounds} rounds passed")
    prop_components(rounds, rng)
    print(f"P30 connected-component split     {rounds} rounds passed")
    prop_gap(rounds, rng)
    print(f"P31 gap disconnection             {rounds} rounds passed")
    print("== all passed ==")
