# -*- coding: utf-8 -*-
"""Constraint solving over the shared linear-form channel."""

from cas.syntax import term as T
from cas.math.domains.linalg import solve_system
from cas.math.linearform import normalized, relation
from cas.math.project import zero_of


class TermField:
    """Adapt terms to the explicit algebraic interface used by elimination."""

    is_field = True

    def __init__(self, ctx):
        self.ctx = ctx

    def from_int(self, n):
        return T.N(n)

    def is_zero(self, t):
        return zero_of(self.ctx, t) is True

    def add(self, a, b):
        return normalized(self.ctx, T.plus(a, b))

    def sub(self, a, b):
        return normalized(self.ctx, T.plus(a, T.neg(b)))

    def mul(self, a, b):
        return normalized(self.ctx, T.times(a, b))

    def neg(self, a):
        return normalized(self.ctx, T.neg(a))

    def div_exact(self, a, b):
        return normalized(self.ctx, T.times(a, T.pw(b, T.MONE)))


def solve_linear_constraints(ctx, relations_, unknowns):
    """Return ``(valuation, complete)`` or ``None`` for a linear witness."""
    unknowns = tuple(unknowns)
    rows, rhs_values = [], []
    for rel in relations_:
        converted = relation(ctx, rel, unknowns)
        if converted is None:
            return None
        row, rhs = converted
        rows.append(row)
        rhs_values.append(rhs)

    solution = solve_system(TermField(ctx), rows, rhs_values)
    if solution is None:
        return None
    particular, homogeneous = solution
    return ({u: particular[i] for i, u in enumerate(unknowns)},
            not homogeneous)
