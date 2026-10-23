"""Random term generators shared by the property benches."""

from __future__ import annotations

import random
from fractions import Fraction

from cas.foundation.ids import SymbolId
from cas.syntax import term as T

SYMBOLS = (SymbolId(1), SymbolId(2), SymbolId(3))
OPERATOR = SymbolId(99)
BINDERS = ("Lam", "Mu", "Pair")


def _literal(rng: random.Random) -> T.Term:
    choice = rng.randrange(5)
    if choice == 0:
        return T.TRUE
    if choice == 1:
        return T.FALSE
    if choice == 2:
        return T.number(rng.randint(-3, 3))
    if choice == 3:
        numerator = rng.randint(-3, 3)
        denominator = rng.randint(2, 5)
        return T.number(Fraction(numerator, denominator))
    return T.number(rng.randint(0, 3))


def random_term(
    rng: random.Random,
    *,
    depth: int = 0,
    bound: int = 0,
    allow_free: bool = False,
) -> T.Term:
    """A random term; closed when `allow_free` is false."""
    if depth >= 3:
        if bound and rng.random() < 0.4:
            return T.BoundVar(rng.randrange(bound))
        if rng.random() < 0.6:
            return _literal(rng)
        return T.symbol(rng.choice(SYMBOLS), rng.choice(("x", "y", "z")))

    choice = rng.randrange(10)
    if choice < 4:
        if bound and rng.random() < 0.4:
            return T.BoundVar(rng.randrange(bound))
        if choice < 2:
            return _literal(rng)
        return T.symbol(rng.choice(SYMBOLS), rng.choice(("x", "y", "z")))
    if choice < 7:
        operator = T.symbol(OPERATOR, "f")
        arguments = tuple(
            random_term(
                rng, depth=depth + 1, bound=bound, allow_free=allow_free
            )
            for _ in range(rng.randint(1, 3))
        )
        return T.app(operator, *arguments)
    if choice < 9:
        arity = rng.choice((1, 2))
        body = random_term(
            rng,
            depth=depth + 1,
            bound=bound + arity,
            allow_free=allow_free,
        )
        annotations = tuple(
            random_term(
                rng, depth=depth + 1, bound=bound, allow_free=allow_free
            )
            for _ in range(rng.randint(0, 2))
        )
        return T.binder(
            rng.choice(BINDERS), arity, body, *annotations, hint="u"
        )
    return T.quote(
        random_term(
            rng, depth=depth + 1, bound=bound, allow_free=allow_free
        )
    )


def fresh_copy(term: T.Term) -> T.Term:
    """An independent copy built from new objects at every node."""
    if isinstance(term, T.IntLit):
        return T.IntLit(term.value)
    if isinstance(term, T.RatLit):
        return T.RatLit(term.value)
    if isinstance(term, T.BoolLit):
        return T.BoolLit(term.value)
    if isinstance(term, T.SymbolRef):
        return T.symbol(term.symbol_id, term.name)
    if isinstance(term, T.BoundVar):
        return T.BoundVar(term.index)
    if isinstance(term, T.Apply):
        return T.app(fresh_copy(term.operator), *[fresh_copy(arg) for arg in term.arguments])
    if isinstance(term, T.Binder):
        return T.binder(
            term.signature,
            term.arity,
            fresh_copy(term.body),
            *[fresh_copy(annotation) for annotation in term.annotations],
            hint=term.hint,
        )
    if isinstance(term, T.Quote):
        return T.quote(fresh_copy(term.term))
    raise AssertionError(f"unknown term variant: {type(term).__name__}")
