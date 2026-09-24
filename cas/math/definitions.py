"""Definition expansion: the only automatic substitution channel."""

from __future__ import annotations

from collections.abc import Callable
from typing import TypeAlias

from cas.errors import BudgetExceeded
from cas.syntax import term as T
from cas.syntax.term import Term

DefinitionLookup: TypeAlias = Callable[[T.Sym], Term | None]
DEFAULT_BUDGET = 100000


def _held(term: Term) -> bool:
    """Return whether a term is a held Quote expression."""
    return (
        isinstance(term, T.Expr)
        and isinstance(term.head, T.Sym)
        and term.head.name == "Quote"
    )


def expand(
    lookup: DefinitionLookup,
    term: Term,
    budget: int = DEFAULT_BUDGET,
) -> Term:
    """Expand every defined symbol in a term to a fixed point."""
    universe: list[Term] = []
    seen: set[int] = set()
    stack: list[Term] = [term]
    bodies: dict[int, Term] = {}
    while stack:
        current = stack.pop()
        if current._h in seen:
            continue
        seen.add(current._h)
        universe.append(current)
        if len(universe) > budget:
            raise BudgetExceeded()
        if isinstance(current, T.Sym):
            body = lookup(current)
            if body is not None:
                bodies[current._h] = body
                if body._h not in seen:
                    stack.append(body)
        elif isinstance(current, T.Expr) and not _held(current):
            stack.extend(current.args)
        elif isinstance(current, T.Bound):
            stack.append(current.body)

    values: dict[int, Term] = {current._h: current for current in universe}

    def rebuild(current: Term) -> Term:
        if isinstance(current, T.Sym):
            body = bodies.get(current._h)
            return current if body is None else values[body._h]
        if isinstance(current, T.Expr):
            if _held(current):
                return current
            arguments = tuple(values[argument._h] for argument in current.args)
            return (
                T.mk(current.head, arguments)
                if any(new is not old for new, old in zip(arguments, current.args))
                else current
            )
        if isinstance(current, T.Bound):
            body = values[current.body._h]
            return (
                current
                if body is current.body
                else T.mk_bound_canon(current.hint, body)
            )
        return current

    for _ in range(len(universe) + 2):
        changed = False
        for current in universe:
            rebuilt = rebuild(current)
            if rebuilt is not values[current._h]:
                values[current._h] = rebuilt
                changed = True
        if not changed:
            break
    return values[term._h]
