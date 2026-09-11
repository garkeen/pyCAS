# -*- coding: utf-8 -*-
"""Math algorithm facade: algorithms the workflow needs but may not import itself.

The workflow layer organises computation and records boundaries, and now and then
it needs two **math** capabilities:

    domain_of(term)                 project the domain the term belongs to (for step display)
    solve_linear_constraints(...)   linear solving of a constraint system (untrusted side)

Both live in `cas.math`, and the workflow is forbidden to import `cas.math`. They
are wrapped into a facade here and injected into the workflow by runtime, so the
workflow only knows "an algorithms object can answer these two questions" and not
how they are implemented.

**Note where the solver sits**: on the untrusted side (it may return a wrong
candidate), its output still has to pass the `constraint.satisfied` checker; the
facade only forwards the call.
"""


class Algorithms:
    """Math algorithm facade visible to the workflow."""

    def domain_of(self, term) -> str:
        """Domain name the term belongs to (given by projection, never by leaf
        sniffing); empty string when the projection misses."""
        from cas.math.project import project
        from cas.syntax.term import Expr, Sym
        t = term
        if (isinstance(term, Expr) and isinstance(term.head, Sym)
                and term.head.name == "Eq"):
            la, ra = term.args
            from cas.syntax import term as T
            t = T.plus(la, T.neg(ra))
        hit = project(t)
        return hit.name if hit is not None else ""

    def solve_linear_constraints(self, relations, unknowns):
        """Extract a linear system in the unknowns from equality constraints and
        solve it.

        Returns `(valuation, complete)`; a solver refusal (nonlinear /
        inconsistent) returns None.
        """
        from cas.math.constraints import solve_linear_constraints
        return solve_linear_constraints(relations, unknowns)
