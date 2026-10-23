"""Randomized binding laws: shifting, abstraction, instantiation, substitution."""

import random

from generators import SYMBOLS, random_term

from cas.syntax import binding as B
from cas.syntax import term as T

SEED = 20261024
ROUNDS = 100


def closed_terms(rounds: int = ROUNDS) -> list:
    rng = random.Random(SEED)
    return [random_term(rng) for _ in range(rounds)]


def open_terms(rounds: int = ROUNDS) -> list:
    rng = random.Random(SEED + 1)
    return [random_term(rng, allow_free=True) for _ in range(rounds)]


def test_generated_closed_terms_are_well_scoped():
    for term in closed_terms():
        assert B.well_scoped(term)


def test_shift_is_invertible():
    for term in open_terms():
        moved = B.shift(term, 3)
        assert B.shift(moved, -3) == term


def test_abstract_then_instantiate_round_trips():
    symbols = (SYMBOLS[0], SYMBOLS[2])
    arguments = (
        T.symbol(symbols[0], "x"),
        T.symbol(symbols[1], "z"),
    )
    for term in closed_terms():
        binder = T.binder("Pair", 2, B.abstract(term, symbols))
        assert B.well_scoped(binder)
        assert B.instantiate(binder, arguments) == term
        assert B.free_symbols(binder).isdisjoint(symbols)


def test_simultaneous_swapping_twice_is_the_identity():
    x = T.symbol(SYMBOLS[0], "x")
    y = T.symbol(SYMBOLS[1], "y")
    mapping = {SYMBOLS[0]: y, SYMBOLS[1]: x}
    for term in open_terms():
        assert B.substitute_free(B.substitute_free(term, mapping), mapping) == term


def test_substitution_removes_exactly_the_mapped_symbols():
    mapping = {SYMBOLS[0]: T.number(1), SYMBOLS[1]: T.number(2)}
    for term in open_terms():
        before = B.free_symbols(term)
        after = B.free_symbols(B.substitute_free(term, mapping))
        assert after == before - set(mapping)


def test_quoted_content_is_inert():
    for term in open_terms():
        quoted = T.quote(term)
        assert B.shift(quoted, 2) is quoted
        assert B.abstract(quoted, SYMBOLS) is quoted
        assert B.substitute_free(quoted, {SYMBOLS[0]: T.number(1)}) is quoted
        assert B.free_symbols(quoted) == frozenset()
        assert B.well_scoped(quoted)
