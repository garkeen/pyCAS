"""Alias expansion: the only automatic substitution channel."""

import pytest
from support import head_app

from cas.foundation.ids import WorldId
from cas.language import sorts as S
from cas.language.signatures import StructuralHead
from cas.semantics.definitions import DefinitionError, expand
from cas.semantics.frames import Declaration, Definition, FrameStore, World
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


def setup():
    table = SymbolTable()
    signature = standard_language(table)
    frames = FrameStore(World(WorldId(0), signature))
    x = table.intern("x")
    base = frames.create(
        frames.root.id, declarations=(Declaration(x, "x", S.REAL),)
    )
    return table, signature, frames, base, x


def chain(table, frames, base, x_term):
    """u := x, v := u in one frame; returns (frame, u, v)."""
    u = table.intern("u")
    v = table.intern("v")
    frame = frames.create(
        base.id,
        definitions=(
            Definition(u, "u", x_term),
            Definition(v, "v", T.symbol(u, "u")),
        ),
    )
    return frame, u, v


def test_expansion_follows_an_alias_chain():
    table, _, frames, base, x = setup()
    x_term = T.symbol(x, "x")
    frame, _, v = chain(table, frames, base, x_term)
    assert expand(frames, frame.id, T.symbol(v, "v")) == x_term


def test_expansion_replaces_every_occurrence():
    table, signature, frames, base, x = setup()
    x_term = T.symbol(x, "x")
    u = table.intern("u")
    frame = frames.create(
        base.id, definitions=(Definition(u, "u", x_term),)
    )
    term = head_app(
        signature,
        StructuralHead.PLUS,
        T.symbol(u, "u"),
        head_app(
            signature,
            StructuralHead.TIMES,
            T.symbol(u, "u"),
            T.number(2),
        ),
    )
    assert expand(frames, frame.id, term) == head_app(
        signature,
        StructuralHead.PLUS,
        x_term,
        head_app(signature, StructuralHead.TIMES, x_term, T.number(2)),
    )


def test_expansion_without_aliases_returns_the_same_object():
    _, _, frames, base, x = setup()
    term = T.symbol(x, "x")
    assert expand(frames, base.id, term) is term


def test_expansion_never_uses_an_equation_as_a_rewrite():
    table, signature, frames, base, x = setup()
    x_term = T.symbol(x, "x")
    u = table.intern("u")
    body = head_app(signature, StructuralHead.PLUS, x_term, T.number(1))
    frame = frames.create(base.id, definitions=(Definition(u, "u", body),))
    equation = head_app(
        signature, StructuralHead.EQ, T.symbol(u, "u"), T.number(2)
    )
    assert expand(frames, frame.id, equation) == head_app(
        signature, StructuralHead.EQ, body, T.number(2)
    )


def test_expansion_descends_into_binders():
    table, _, frames, base, x = setup()
    x_term = T.symbol(x, "x")
    u = table.intern("u")
    f = table.intern("f")
    frame = frames.create(
        base.id, definitions=(Definition(u, "u", x_term),)
    )
    binder = T.binder(
        "Lam",
        1,
        T.app(T.symbol(f, "f"), T.symbol(u, "u"), T.BoundVar(0)),
    )
    expanded = expand(frames, frame.id, binder)
    assert isinstance(expanded, T.Binder)
    assert expanded.body == T.app(T.symbol(f, "f"), x_term, T.BoundVar(0))


def test_expansion_reports_when_it_cannot_reach_a_fixed_point():
    table, _, frames, base, x = setup()
    frame, _, v = chain(table, frames, base, T.symbol(x, "x"))
    with pytest.raises(DefinitionError):
        expand(frames, frame.id, T.symbol(v, "v"), limit=1)
    assert expand(frames, frame.id, T.symbol(v, "v"), limit=2) == T.symbol(
        x, "x"
    )


def test_expansion_is_idempotent():
    table, _, frames, base, x = setup()
    frame, _, v = chain(table, frames, base, T.symbol(x, "x"))
    once = expand(frames, frame.id, T.symbol(v, "v"))
    assert expand(frames, frame.id, once) == once
