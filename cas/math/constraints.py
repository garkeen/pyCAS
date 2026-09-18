"""Constraint solving: extract a linear system for the unknowns from equation
constraints and solve it.

**This is the untrusted side.** It produces a candidate valuation (a witness),
not a conclusion. Whether "this assignment satisfies the constraint system" may
be claimed is decided by the `constraint.satisfied` checker, which re-checks
each constraint. So this code may be heuristic and may refuse, but it must never
declare itself correct.

Algorithm steps, all explicit algebraic operations on domain elements:

1. for each relation take `E = lhs - rhs`;
2. linearity test: substitute 0 / unit values for the unknowns to extract
   coefficients, rebuild `E` and decide the difference vanishes; a nonzero
   difference means nonlinear, refused honestly as FRAGMENT rather than forced;
3. assemble the coefficient matrix and solve it with the general Gaussian
   elimination in `linalg.solve_system`;
4. return the particular solution as the valuation (underdetermined is still a
   legal witness; the checker decides whether it truly satisfies).

Solving depends only on `linalg` (the shared algorithm machine) and domain normal
form vanishing; it imports no algorithm belonging to the counterpart solver.
"""

from cas.syntax import term as T
from cas.math.domains.linalg import solve_system
from cas.math.domains.qarith import fold
from cas.math.project import project, zero_of, normalize as proj_normalize


def _nf(t):
    """Coefficient normalization: on a projection hit take the domain normal
    form (canonical rational function over K(x)); otherwise fall back to literal
    folding.

    Folding literals alone is not enough: `x - x` and `x^2 - x^2 + 1` only
    collapse through the domain normal form.
    """
    hit = project(t)
    if hit is not None:
        return proj_normalize(hit)
    return fold(t)


class TermField:
    """Adapt **terms** to the domain interface so that linalg's Gaussian
    elimination can use them.

    Coefficients are rational functions in the parameters, i.e. elements of
    K(x1..xn), with division represented as `b^-1`. The adapter does no
    mathematics itself; it only exposes the existing explicit algebraic
    operations (domain normal form plus vanishing) as the few operations the
    eliminator needs.
    """

    is_field = True

    def from_int(self, n):
        return T.N(n)

    def is_zero(self, t):
        return zero_of(t) is True

    def add(self, a, b):
        return _nf(T.plus(a, b))

    def sub(self, a, b):
        return _nf(T.plus(a, T.neg(b)))

    def mul(self, a, b):
        return _nf(T.times(a, b))

    def neg(self, a):
        return _nf(T.neg(a))

    def div_exact(self, a, b):
        return _nf(T.times(a, T.pw(b, T.MONE)))


def _decompose(t, unknowns):
    """Decompose `t` as `sum(c_i * u_i) + c_0` where the coefficients do not
    involve the unknowns.

    This is a *syntactic* linear-form analysis: it needs no simplifier and no
    semantic vanishing, so it works for transcendental coefficients such as
    `exp(x)*sin(x)` too. Nonlinear terms, or function calls with unknowns
    (`sin(u)`, `u^-1`, `u*u`), return None: refused honestly rather than forced
    into a linear form.
    """
    if t in unknowns:                       # interned pointer identity
        return ({t: T.ONE}, T.ZERO)
    if not (T.free_vars(t) & set(unknowns)):
        return ({}, t)
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Plus":
            coeffs, const = {}, T.ZERO
            for a in t.args:
                d = _decompose(a, unknowns)
                if d is None:
                    return None
                for k, v in d[0].items():
                    coeffs[k] = T.plus(coeffs.get(k, T.ZERO), v)
                const = T.plus(const, d[1])
            return (coeffs, const)
        if name == "Times":
            parts = []
            for a in t.args:
                d = _decompose(a, unknowns)
                if d is None:
                    return None
                parts.append(d)
            unknown_idx = [i for i, d in enumerate(parts) if d[0]]
            if len(unknown_idx) > 1:
                return None             # two unknown-bearing factors multiply: nonlinear
            if not unknown_idx:
                acc = T.ONE
                for _cs, c0 in parts:
                    acc = T.times(acc, c0)
                return ({}, acc)
            i = unknown_idx[0]
            # The coefficient must be multiplied by the constant part of the
            # other factors; omitting it would turn the coefficient of -1*v
            # into +1.
            k_others = T.ONE
            for j, (_cs, c0) in enumerate(parts):
                if j != i:
                    k_others = T.times(k_others, c0)
            cs, c0 = parts[i]
            return ({k: T.times(v, k_others) for k, v in cs.items()},
                    T.times(c0, k_others))
        if name == "Power" and len(t.args) == 2 and t.args[1] is T.ONE:
            return _decompose(t.args[0], unknowns)
    return None


def is_linear(e, unknowns):
    """Whether `e` is linear in the unknowns, constant term included."""
    return _decompose(e, unknowns) is not None


def _constrained_relation(rel, unknowns):
    """An equation relation to a coefficient row plus right-hand side; returns
    None when it is nonlinear or not an equation.

    The two sides are decomposed *separately* and then subtracted, to avoid
    negating `lhs - rhs` as a whole without distributing, which would destroy
    the linear form.
    """
    if not (isinstance(rel, T.Expr) and isinstance(rel.head, T.Sym)
            and rel.head.name == "Eq"):
        return None
    lhs, rhs = rel.args
    dl, dr = _decompose(lhs, unknowns), _decompose(rhs, unknowns)
    if dl is None or dr is None:
        return None
    cl, c0l = dl
    cr, c0r = dr
    # Coefficients must be normalized before reaching the eliminator:
    # decomposition can produce unfolded forms like `0 + 1`, which would defeat
    # pivot zero-testing and division in Gaussian elimination.
    row = [_nf(T.plus(cl.get(u, T.ZERO), T.neg(cr.get(u, T.ZERO))))
           for u in unknowns]
    return row, _nf(T.plus(c0r, T.neg(c0l)))    # sum(c_i u_i) = c0r - c0l


def solve_linear_constraints(relations, unknowns):
    """Find an assignment satisfying all relations.

    Returns `(valuation, complete)`:
      · valuation: `{Unknown: Term}`, unknowns expressed in parameters;
      · complete: whether the solution is unique (False when underdetermined,
        but the particular solution is still a legal witness).
    Returns None on refusal: a relation is not an equation, is nonlinear, or the
    system is inconsistent.
    """
    unknowns = tuple(unknowns)
    rows, b = [], []
    for rel in relations:
        got = _constrained_relation(rel, unknowns)
        if got is None:
            return None
        row, rhs = got
        rows.append(row)
        b.append(_nf(rhs))

    ring = TermField()
    sol = solve_system(ring, rows, b)
    if sol is None:
        return None
    particular, homogeneous = sol
    return ({u: particular[i] for i, u in enumerate(unknowns)},
            not homogeneous)
