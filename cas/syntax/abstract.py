"""Subterm abstraction: replace maximal subterms satisfying a predicate."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TypeAlias

from cas.syntax import term as T
from cas.syntax.termpath import free_vars, subst

AbstractionPredicate: TypeAlias = Callable[[T.Term], bool]


@dataclass(frozen=True, slots=True)
class Abstraction:
    """An abstraction result and the environment used to restore it."""

    term: T.Term
    replacements: tuple[tuple[T.Sym, T.Term], ...]

    def thaw(self, term: T.Term | None = None) -> T.Term:
        """Restore using this environment, defaulting to the result term."""
        return thaw(self.term if term is None else term, self.replacements)


def abstract_subterms(
    term: T.Term,
    predicate: AbstractionPredicate,
    prefix: str = "_u",
) -> Abstraction:
    """Replace every maximal subterm satisfying ``predicate`` with a fresh symbol."""
    used = {symbol.name for symbol in free_vars(term)}
    replacements: list[tuple[T.Sym, T.Term]] = []
    seen: dict[T.Term, T.Sym] = {}
    counter = 0

    def fresh() -> T.Sym:
        nonlocal counter
        while True:
            name = f"{prefix}{counter}"
            counter += 1
            if name not in used:
                used.add(name)
                return T.S(name)

    def walk(current: T.Term) -> T.Term:
        if predicate(current):
            symbol = seen.get(current)
            if symbol is None:
                symbol = fresh()
                seen[current] = symbol
                replacements.append((symbol, current))
            return symbol
        if isinstance(current, T.Expr):
            arguments = tuple(walk(argument) for argument in current.args)
            if all(new is old for new, old in zip(arguments, current.args)):
                return current
            return T.mk(current.head, arguments)
        return current

    return Abstraction(term=walk(term), replacements=tuple(replacements))


def thaw(
    term: T.Term,
    environment: tuple[tuple[T.Sym, T.Term], ...],
) -> T.Term:
    """Replace abstraction symbols with their original terms."""
    if not environment:
        return term
    return subst(term, dict(environment))
