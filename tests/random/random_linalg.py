# -*- coding: utf-8 -*-
"""Linear algebra and Diophantine-fragment random bench.

Four properties, all self-proving with no external ground truth:
  P14 rank-nullity  rank(A) + dim ker(A) = number of columns, and every basis vector
                    satisfies A*v = 0
  P15 solution reconstruction  a consistent system built from a planted solution must
                    be satisfied by the particular solution; an inconsistent system
                    built by planting a contradictory row must return None
  P16 Bareiss       det(AB) = det(A)det(B) (multiplicativity over integer matrices, no
                    external ground truth)
  P17 Diophantine fragment  the extended-Euclid certificate s*a+t*b=g; a linear
                    Diophantine solution is verified with a period inside the kernel
                    and primitive; integer roots equal the planted root set exactly
                    (nothing missed, nothing spurious)

Usage: python tests/random/random_linalg.py [rounds] [seed]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.math.domains.q import Q_RING as R
from cas.math.domains.z import Z_RING
from cas.math.domains.linalg import rank, nullspace, solve_system, det_bareiss
from cas.math.domains.poly import _norm, p_mul
from cas.math.tactics import solve_diophantine_linear, integer_roots, TacticsError
from cas.syntax.term import S

from cas.runtime import bootstrap
bootstrap()

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def matvec(A, x):
    return [sum(a * xi for a, xi in zip(row, x)) for row in A]


def rand_mat(rng, m, n):
    return [[Fr(rng.randint(-6, 6), rng.choice((1, 1, 2, 3)))
             for _ in range(n)] for _ in range(m)]


# ---------------------------------------------------------------------------
# P14: rank-nullity plus kernel membership
# ---------------------------------------------------------------------------

def prop_rank_nullity(rounds, rng):
    for i in range(rounds):
        m, n = rng.randint(1, 5), rng.randint(1, 6)
        A = rand_mat(rng, m, n)
        r = rank(R, A)
        basis = nullspace(R, A)
        if r + len(basis) != n:
            fail("P14 rank-nullity", i, f"rank={r} dimker={len(basis)} n={n}")
        for v in basis:
            if any(x != 0 for x in matvec(A, v)):
                fail("P14 kernel membership", i, f"v={v}")


# ---------------------------------------------------------------------------
# P15: consistency / inconsistency
# ---------------------------------------------------------------------------

def prop_solve(rounds, rng):
    for i in range(rounds):
        m, n = rng.randint(1, 4), rng.randint(1, 5)
        A = rand_mat(rng, m, n)
        xs = [Fr(rng.randint(-5, 5)) for _ in range(n)]
        b = matvec(A, xs)
        res = solve_system(R, A, b)
        if res is None:
            fail("P15 consistent system misjudged unsolvable", i)
        x0, basis = res
        if list(matvec(A, x0)) != list(b):
            fail("P15 particular solution does not satisfy", i, f"x0={x0}")
        # inconsistency: copy the first row and alter the right-hand side (assuming the row is nonzero)
        if any(A[0][j] != 0 for j in range(n)):
            A2 = A + [list(A[0])]
            b2 = b + [b[0] + 1]
            if solve_system(R, A2, b2) is not None:
                fail("P15 contradiction not detected", i)


# ---------------------------------------------------------------------------
# P16: Bareiss determinant multiplicativity
# ---------------------------------------------------------------------------

def prop_bareiss(rounds, rng):
    for i in range(rounds):
        n = rng.randint(1, 4)
        A = [[rng.randint(-5, 5) for _ in range(n)] for _ in range(n)]
        B = [[rng.randint(-5, 5) for _ in range(n)] for _ in range(n)]
        da, db = det_bareiss(A), det_bareiss(B)
        dab = det_bareiss(matmul(A, B))
        if dab != da * db:
            fail("P16 multiplicativity", i, f"det(AB)={dab} detA*detB={da*db}")
        ident = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
        if det_bareiss(ident) != 1:
            fail("P16 identity matrix", i)


# ---------------------------------------------------------------------------
# P17: Diophantine fragment
# ---------------------------------------------------------------------------

def prop_diophantine(rounds, rng):
    for i in range(rounds):
        a, b = rng.randint(-12, 12), rng.randint(-12, 12)
        g, s, t = Z_RING.xgcd(a, b)
        if s * a + t * b != g:
            fail("P17 Bezout certificate", i, f"a={a} b={b} g={g} s={s} t={t}")
        if g != __import__("math").gcd(a, b):
            fail("P17 gcd mismatch", i)
        c = rng.randint(-20, 20)
        if g == 0 or c % g != 0:
            try:
                solve_diophantine_linear(a, b, c)
                if not (g == 0 and c == 0):
                    fail("P17 unsolvable case not refused", i, f"a={a} b={b} c={c} g={g}")
            except TacticsError:
                pass
        else:
            (x0, y0), (dx, dy) = solve_diophantine_linear(a, b, c)
            if a * x0 + b * y0 != c:
                fail("P17 particular solution verification", i)
            if a * dx + b * dy != 0:
                fail("P17 period is not in the kernel", i)
            if __import__("math").gcd(dx, dy) != 1:
                fail("P17 period is not primitive", i)


def prop_integer_roots(rounds, rng):
    """Planted integer roots times a factor with no integer root (x^2+1): the result
    must be exactly the planted set."""
    for i in range(rounds):
        roots = [rng.randint(-5, 5) for _ in range(rng.randint(1, 3))]
        p = _norm(R, (X,), {(2,): Fr(1), (0,): Fr(1)})    # x^2+1 has no integer root
        lc = rng.choice((1, 1, 2, 3))
        p = _norm(R, (X,), {k: c * lc for k, c in p.monos})
        for r in roots:
            p = p_mul(R, p, _norm(R, (X,), {(1,): Fr(1), (0,): Fr(-r)}))
        got = integer_roots(p, X)
        want = sorted(set(roots))
        if got != want:
            fail("P17 integer root set", i, f"got={got} want={want}")


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== linear algebra / Diophantine random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_rank_nullity(rounds, rng)
    print(f"P14 rank-nullity                  {rounds} rounds passed")
    prop_solve(rounds, rng)
    print(f"P15 consistent/inconsistent       {rounds} rounds passed")
    prop_bareiss(min(rounds, 500), rng)
    print(f"P16 Bareiss multiplicativity      {min(rounds,500)} rounds passed")
    prop_diophantine(rounds, rng)
    print(f"P17 Diophantine certificates      {rounds} rounds passed")
    prop_integer_roots(min(rounds, 500), rng)
    print(f"P17 integer root set              {min(rounds,500)} rounds passed")
    print("== all passed ==")
