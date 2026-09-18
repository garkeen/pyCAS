"""Randomized random bench (generation-based verification rather than handwritten
cases: the machine generates the instances and checks the properties).

Four properties, all self-proving with no external ground truth:
  P1 fold fidelity   eval_exact(t, env) == eval_exact(fold(t), env)
  P2 idempotent pointer  fold(fold(t)) is fold(t) (content addressing implies that the
                     same structure has the same pointer)
  P3 interval channel  after assuming x>k, the three-valued truth table for queries x>j
  P4 back-substitution judge  an equation built from known roots must evaluate to exactly
                     0 at each root after expansion, and a non-root sample must not

Usage: python tests/random/random_qarith.py [rounds] [seed]
On any failure it prints a minimal counterexample and the seed and exits with code 1.
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.syntax.term import S, N, mk, plus, times, pw, neg, Expr, Int
from cas.math.domains.qarith import fold, eval_exact, EvalNumError
from cas.kernel.scope import Assumptions
from cas.math.decide import decide, branch
from cas.kernel.verdict import YES, Unknown
from cas.math.domains.poly import from_term as _poly_from_term, to_term as _poly_to_term
from cas.math.domains.q import Q_RING

from cas.runtime import bootstrap
bootstrap()

X, Y = S("x"), S("y")


# ---------------------------------------------------------------------------
# Generator: random ring-layer terms (bounded depth, literals with small denominators)
# ---------------------------------------------------------------------------

def gen_lit(rng):
    n = rng.randint(-9, 9)
    if rng.random() < 0.3:
        return N(Fr(n, rng.choice((2, 3, 4, 5, 7))))
    return N(n)


def gen(d, rng):
    if d == 0:
        r = rng.random()
        if r < 0.45:
            return gen_lit(rng)
        return X if rng.random() < 0.7 else Y
    r = rng.random()
    if r < 0.40:
        return plus(*(gen(d - 1, rng) for _ in range(rng.randint(2, 3))))
    if r < 0.80:
        return times(*(gen(d - 1, rng) for _ in range(rng.randint(2, 3))))
    # integer powers: exponents 0..3 are safe (negative exponents are handled by gen_safe)
    b = gen(d - 1, rng)
    return pw(b, N(rng.randint(0, 3)))


def gen_safe(d, rng):
    """Conservative version of gen: a negative exponent applies only to a nonzero
    literal base, avoiding undefined-domain disputes."""
    t = gen(d, rng)

    def fix(u):
        if not isinstance(u, Expr):
            return u
        if u.head.name == "Power":
            b, e = u.args
            b2 = fix(b)
            ev = e.v if isinstance(e, Int) else None
            if ev is not None and ev < 0:
                if isinstance(b2, Int) and b2.v != 0:
                    return pw(b2, e)
                return b2                      # drop the negative exponent, keep the base
            return mk(u.head, (b2, e))
        return mk(u.head, tuple(fix(a) for a in u.args))

    return fix(t)


def fail(msg, seed, t=None):
    print(f"FAIL [{msg}] seed={seed}")
    if t is not None:
        print("  term:", t)
    sys.exit(1)


# ---------------------------------------------------------------------------
# P1/P2: fold fidelity and idempotence
# ---------------------------------------------------------------------------

def prop_fold(rounds, rng):
    envs = [{X: Fr(a, b), Y: Fr(c, e)}
            for a, b, c, e in [(1, 3, -2, 5), (7, 2, 1, 1), (-4, 9, 5, 3),
                               (0, 1, 11, 6), (13, 4, -7, 8)]]
    for i in range(rounds):
        t = gen_safe(rng.randint(1, 4), rng)
        ft = fold(t)
        if fold(ft) is not ft:
            fail("P2 idempotent pointer", rng.seed if hasattr(rng, "seed") else "?", t)
        for env in envs:
            try:
                v1 = eval_exact(t, env)
                v2 = eval_exact(ft, env)
            except EvalNumError:
                continue
            if v1 != v2:
                fail(f"P1 fidelity env={env}", i, t)


# ---------------------------------------------------------------------------
# P3: interval-channel three-valued truth table
# ---------------------------------------------------------------------------

def prop_interval(rounds, rng):
    for _ in range(rounds):
        k = rng.randint(-5, 5)
        assumptions = Assumptions().extended(mk(S("Gt"), (X, N(k))))
        for j in range(-7, 8):
            got = decide(mk(S("Gt"), (X, N(j))), assumptions)
            if j <= k:
                ok = got is YES
            else:
                ok = isinstance(got, Unknown)
            if not ok:
                fail(f"P3 assume x>{k}, query x>{j}: got {got}", k)
        _cond, b_assumptions, _st = branch(
            assumptions, mk(S("Lt"), (X, N(k + 10))))[0]
        got = decide(mk(S("Lt"), (X, N(k + 100))), b_assumptions)
        if got is not YES:
            fail(f"P3 branch frame inheritance", k)


# ---------------------------------------------------------------------------
# P4: back-substitution judge (seed roots -> expand -> exact back-substitution)
# ---------------------------------------------------------------------------

def _rand_root(rng):
    return Fr(rng.randint(-6, 6), rng.choice((1, 1, 1, 2, 3)))


def prop_backsub(rounds, rng):
    for i in range(rounds):
        roots = [_rand_root(rng) for _ in range(rng.randint(1, 3))]
        p = N(1)
        for r in roots:
            p = times(p, plus(X, neg(N(r))))
        # expansion uses the production polynomial machinery (single responsibility:
        # the term layer carries no expansion implementation of its own)
        poly = _poly_from_term(Q_RING, p, (X,))
        if poly is None:
            fail("P4 the product is not representable in Q[x]", i, p)
        expanded = _poly_to_term(Q_RING, poly)
        folded = fold(expanded)
        for r in roots:
            if eval_exact(folded, {X: r}) != 0:
                fail(f"P4 root back-substitution is nonzero: r={r}", i, expanded)
        for _ in range(4):
            bad = Fr(rng.randint(-9, 9), rng.choice((1, 2)))
            if bad in roots:
                continue
            if eval_exact(folded, {X: bad}) == 0:
                fail(f"P4 non-root misjudged zero: bad={bad}", i, expanded)


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260826
    print(f"== random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_fold(rounds, rng)
    print(f"P1+P2 fold fidelity/idempotence  {rounds} rounds passed")
    prop_interval(200, rng)
    print(f"P3 interval channel              200x15 queries passed")
    prop_backsub(min(rounds, 500), rng)
    print(f"P4 back-substitution judge       {min(rounds, 500)} rounds passed")
    print("== all passed ==")
