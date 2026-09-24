# -*- coding: utf-8 -*-
"""Definition expansion: the **only** automatic substitution channel.

A definition (`u := x^2`) is a predicative alias, not a proposition: its
right-hand side is a term that does not refer to the symbol being defined, so the
alias graph is acyclic (checked when the definition is admitted) and expanding
aliases can never loop. An equation is a different kind of thing: it enters the
context as an *assumption*, may be self-referential (`f(x) == f(x)+1` is legal),
and is **never** expanded automatically — using a frame's equations as rewrite
rules is not a decision procedure at all.

Expansion is a syntactic operation driven by an explicit lookup function, so this
module knows neither the kernel nor the workflow:

    expand(lookup, t)        lookup(symbol) -> body | None

Termination: every step descends one alias in an acyclic graph, and the budget
guards the *size* of the result (a definition used n times duplicates its body n
times). Exceeding the budget raises BudgetExceeded, which callers report as an
honest refusal rather than truncating silently.
"""

from cas.syntax import term as T
from cas.errors import BudgetExceeded

DEFAULT_BUDGET = 100000


def _held(u) -> bool:
    """Quoted expressions are data, not mathematical terms: they are not
    expanded (their held structure is preserved, as in `subst`)."""
    return (isinstance(u, T.Expr) and isinstance(u.head, T.Sym)
            and u.head.name == "Quote")


def expand(lookup, t, budget=DEFAULT_BUDGET):
    """Expand every defined symbol in `t` to its body, bottom-up.

    The traversal is explicit-stack (never the Python recursion stack), pulls in
    the bodies of every definition reachable from the term, and then iterates a
    fixed point towards the fully expanded form. Because the alias graph is
    acyclic, the number of passes is bounded by the longest alias chain; the
    fixed-point test is the loop condition, so there is no round-count magic.
    """
    universe, seen, stack, bodies = [], set(), [t], {}
    while stack:
        u = stack.pop()
        if u._h in seen:
            continue
        seen.add(u._h)
        universe.append(u)
        if len(universe) > budget:
            raise BudgetExceeded()
        if isinstance(u, T.Sym):
            body = lookup(u)
            if body is not None:
                bodies[u._h] = body
                if body._h not in seen:
                    stack.append(body)
        elif isinstance(u, T.Expr) and not _held(u):
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    val = {u._h: u for u in universe}

    def node(u):
        if isinstance(u, T.Sym):
            body = bodies.get(u._h)
            return u if body is None else val[body._h]
        if isinstance(u, T.Expr):
            if _held(u):
                return u
            args = tuple(val[a._h] for a in u.args)
            return (T.mk(u.head, args)
                    if any(x is not y for x, y in zip(args, u.args)) else u)
        if isinstance(u, T.Bound):
            b = val[u.body._h]
            return u if b is u.body else T.mk_bound_canon(u.hint, b)
        return u

    for _ in range(len(universe) + 2):
        changed = False
        for u in universe:
            new = node(u)
            if new is not val[u._h]:
                val[u._h] = new
                changed = True
        if not changed:
            break
    return val[t._h]
