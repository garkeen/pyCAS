"""Immutable frames: visibility, freshness, escape checks and hypotheses."""

import dataclasses

import pytest
from support import (
    MapEnvironment,
    head_app,
    proposition_in,
    runtime_proposition,
)

from cas.foundation.ids import FrameId, SymbolId, WorldId
from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import bootstrap
from cas.semantics.frames import (
    Declaration,
    Definition,
    FrameSorts,
    FrameStore,
    Hypothesis,
    World,
    new_world,
)
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


def test_the_store_starts_with_an_empty_root():
    _, _, frames, base, _ = setup()
    assert frames.root.parent is None
    assert frames.root.declarations == ()
    assert frames.count() == 2
    assert frames.chain(base.id) == (frames.root, base)


def test_visibility_is_ancestor_only():
    _, _, frames, base, _ = setup()
    child = frames.create(base.id)
    sibling = frames.create(base.id)
    assert frames.is_visible(base.id, child.id)
    assert frames.is_visible(base.id, base.id)
    assert not frames.is_visible(child.id, base.id)
    assert not frames.is_visible(sibling.id, child.id)


def test_readability_and_agreement_are_explicit_across_frames():
    _, signature, frames, base, x = setup()
    child = frames.create(base.id)
    sibling = frames.create(base.id)
    term = head_app(
        signature, StructuralHead.GT, T.symbol(x, "x"), T.number(0)
    )
    in_base = proposition_in(frames, base.id, signature, term)
    in_child = proposition_in(frames, child.id, signature, term)
    in_sibling = proposition_in(frames, sibling.id, signature, term)
    assert frames.readable(in_base, child.id)
    assert frames.readable(in_child, child.id)
    assert not frames.readable(in_sibling, child.id)
    assert frames.agree_in(child.id, in_base, in_child)
    assert not frames.agree_in(child.id, in_base, in_sibling)


def test_a_missing_parent_is_refused():
    _, _, frames, _, _ = setup()
    with pytest.raises(KeyError):
        frames.create(FrameId(10_000))


def test_a_missing_frame_is_never_visible():
    _, _, frames, base, _ = setup()
    missing = FrameId(10_000)
    assert not frames.is_visible(base.id, missing)
    assert not frames.is_visible(missing, base.id)


def test_declared_sorts_are_found_along_the_chain():
    table, _, frames, base, x = setup()
    assert frames.sort_of(base.id, x) is S.REAL
    child = frames.create(base.id)
    assert frames.sort_of(child.id, x) is S.REAL
    assert frames.sort_of(base.id, table.intern("y")) is None


def test_shadowing_requires_a_fresh_id():
    table, _, frames, base, x = setup()
    shadow = table.fresh("x")
    child = frames.create(
        base.id, declarations=(Declaration(shadow, "x", S.INTEGER),)
    )
    assert frames.sort_of(child.id, shadow) is S.INTEGER
    assert frames.sort_of(child.id, x) is S.REAL


def test_a_structural_head_cannot_be_declared_as_a_symbol():
    _, signature, frames, base, _ = setup()
    plus = signature.symbol_of(StructuralHead.PLUS)
    assert plus is not None
    with pytest.raises(ValueError):
        frames.create(
            base.id, declarations=(Declaration(plus, "Plus", S.REAL),)
        )


def test_a_symbol_cannot_be_introduced_twice():
    _, _, frames, base, x = setup()
    with pytest.raises(ValueError):
        frames.create(
            base.id,
            declarations=(
                Declaration(x, "x", S.REAL),
                Declaration(x, "x", S.REAL),
            ),
        )
    with pytest.raises(ValueError):
        frames.create(base.id, declarations=(Declaration(x, "x", S.INTEGER),))


def test_declarations_and_definitions_need_display_names():
    with pytest.raises(ValueError):
        Declaration(SymbolId(1), "", S.REAL)
    with pytest.raises(TypeError):
        Declaration(SymbolId(1), "x", "real")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Definition(SymbolId(1), "x", "term")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        Hypothesis("proposition")  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        Definition(SymbolId(1), "", T.number(1))


def test_definitions_are_visible_but_are_not_declarations():
    table, _, frames, base, x = setup()
    u = table.intern("u")
    frame = frames.create(
        base.id, definitions=(Definition(u, "u", T.symbol(x, "x")),)
    )
    assert frames.lookup_definition(frame.id, u) is not None
    assert frames.sort_of(frame.id, u) is None
    assert frames.lookup_definition(frame.id, x) is None


def test_an_alias_may_refer_to_an_earlier_alias_in_the_same_frame():
    table, _, frames, base, x = setup()
    u = table.intern("u")
    v = table.intern("v")
    frame = frames.create(
        base.id,
        definitions=(
            Definition(u, "u", T.symbol(x, "x")),
            Definition(v, "v", T.symbol(u, "u")),
        ),
    )
    assert frames.lookup_definition(frame.id, v) is not None


def test_self_reference_and_forward_reference_are_refused():
    table, _, frames, base, _ = setup()
    u = table.intern("u")
    v = table.intern("v")
    with pytest.raises(ValueError):
        frames.create(
            base.id, definitions=(Definition(u, "u", T.symbol(u, "u")),)
        )
    with pytest.raises(ValueError):
        frames.create(
            base.id,
            definitions=(
                Definition(u, "u", T.symbol(v, "v")),
                Definition(v, "v", T.number(1)),
            ),
        )
    with pytest.raises(ValueError):
        frames.create(
            base.id,
            definitions=(
                Definition(v, "v", T.symbol(u, "u")),
                Definition(u, "u", T.number(1)),
            ),
        )


def test_a_definition_body_must_be_well_scoped():
    table, _, frames, base, _ = setup()
    u = table.intern("u")
    with pytest.raises(ValueError):
        frames.create(
            base.id, definitions=(Definition(u, "u", T.BoundVar(0)),)
        )


def test_a_definition_cannot_reference_a_local_symbol_of_an_unrelated_frame():
    table, _, frames, base, _ = setup()
    u = table.intern("u")
    v = table.intern("v")
    frames.create(base.id, declarations=(Declaration(u, "u", S.REAL),))
    with pytest.raises(ValueError):
        frames.create(
            base.id,
            definitions=(Definition(v, "v", T.symbol(u, "u")),),
        )


def test_a_definition_may_reference_a_symbol_declared_in_an_ancestor():
    table, _, frames, base, _ = setup()
    u = table.intern("u")
    v = table.intern("v")
    parent = frames.create(
        base.id, declarations=(Declaration(u, "u", S.REAL),)
    )
    frame = frames.create(
        parent.id, definitions=(Definition(v, "v", T.symbol(u, "u")),)
    )
    assert frames.lookup_definition(frame.id, v) is not None


def test_escapes_reports_unrelated_and_undeclared_symbols():
    table, signature, frames, base, x = setup()
    u = table.intern("u")
    frames.create(base.id, declarations=(Declaration(u, "u", S.REAL),))
    sibling = frames.create(frames.root.id)
    undeclared = SymbolId(10_000)
    term = head_app(
        signature,
        StructuralHead.PLUS,
        T.symbol(x, "x"),
        T.symbol(u, "u"),
        T.symbol(undeclared, "global"),
    )
    assert frames.escapes(base.id, term) == tuple(sorted((u, undeclared)))
    assert frames.escapes(sibling.id, term) == tuple(
        sorted((x, u, undeclared))
    )
    assert frames.escapes(base.id, T.number(1)) == ()


def test_the_root_cannot_carry_a_hypothesis():
    table, signature, frames, base, x = setup()
    proposition = proposition_in(
        frames,
        base.id,
        signature,
        head_app(signature, StructuralHead.EQ, T.symbol(x, "x"), T.number(1)),
    )
    with pytest.raises(ValueError):
        frames.create(None, hypotheses=(Hypothesis(proposition),))


def test_a_symbol_cannot_be_declared_in_two_sibling_frames():
    table, _, frames, base, _ = setup()
    y = table.intern("y")
    frames.create(
        base.id, declarations=(Declaration(y, "y", S.REAL),)
    )
    with pytest.raises(ValueError):
        frames.create(
            base.id, declarations=(Declaration(y, "y", S.REAL),)
        )


def test_a_hypothesis_must_be_meaningful_in_the_parent():
    table, signature, frames, base, x = setup()
    sibling = frames.create(base.id)
    foreign = proposition_in(
        frames,
        sibling.id,
        signature,
        head_app(signature, StructuralHead.EQ, T.symbol(x, "x"), T.number(1)),
    )
    with pytest.raises(ValueError):
        frames.create(base.id, hypotheses=(Hypothesis(foreign),))


def test_a_hypothesis_from_another_world_is_refused(runtime):
    other = bootstrap()
    assert other.frame.id == runtime.frame.id
    assert other.world.id != runtime.world.id
    foreign = runtime_proposition(other, T.TRUE)
    with pytest.raises(ValueError, match="another meaning world"):
        runtime.frames.create(
            runtime.frame.id, hypotheses=(Hypothesis(foreign),)
        )
    assert runtime.frames.count() == 2


def test_a_hypothesis_cannot_reference_a_sibling_symbol():
    table, signature, frames, base, x = setup()
    y = table.intern("y")
    frames.create(
        base.id, declarations=(Declaration(y, "y", S.REAL),)
    )
    source = proposition_in(
        frames,
        base.id,
        signature,
        head_app(signature, StructuralHead.GT, T.symbol(x, "x"), T.number(0)),
    )
    environment = MapEnvironment({x: S.REAL, y: S.REAL})
    foreign = Pr.check(
        head_app(
            signature, StructuralHead.GT, T.symbol(y, "y"), T.number(0)
        ),
        signature,
        environment,
        source.meaning,
    )
    assert isinstance(foreign, Pr.Proposition)
    with pytest.raises(ValueError):
        frames.create(base.id, hypotheses=(Hypothesis(foreign),))


def test_assumptions_are_collected_outermost_first():
    _, signature, frames, base, x = setup()
    first = proposition_in(
        frames,
        base.id,
        signature,
        head_app(signature, StructuralHead.EQ, T.symbol(x, "x"), T.number(1)),
    )
    child = frames.create(base.id, hypotheses=(Hypothesis(first),))
    second = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.GT, T.symbol(x, "x"), T.number(0)),
    )
    grandchild = frames.create(child.id, hypotheses=(Hypothesis(second),))
    assert frames.assumptions(grandchild.id) == (first, second)


def test_frame_sorts_is_the_typing_environment_view():
    _, _, frames, base, x = setup()
    environment = FrameSorts(frames, base.id)
    assert environment.sort_of(x) is S.REAL
    assert environment.sort_of(SymbolId(10_000)) is None


def test_frames_are_immutable():
    _, _, _, base, _ = setup()
    with pytest.raises(dataclasses.FrozenInstanceError):
        base.parent = None


def _content_frames(
    *, burn_frame: bool = False, sort: S.Sort = S.REAL
):
    """Two stores with identical language and declaration content."""
    table = SymbolTable()
    signature = standard_language(table)
    frames = FrameStore(new_world(signature))
    if burn_frame:
        # Consume a frame id so the compared frame has a different process id.
        frames.create(frames.root.id)
    x = table.intern("x")
    base = frames.create(
        frames.root.id, declarations=(Declaration(x, "x", sort),)
    )
    return table, signature, frames, base, x


def test_term_structural_keys_use_symbol_identity_not_display_names():
    first = T.symbol(SymbolId(7), "x")
    second = T.symbol(SymbolId(7), "y")
    other = T.symbol(SymbolId(8), "x")
    assert first.structural_key() == second.structural_key()
    assert first.structural_key() != other.structural_key()


def test_content_digests_ignore_process_local_world_and_frame_ids():
    _, _, first_frames, first_base, _ = _content_frames()
    _, _, second_frames, second_base, _ = _content_frames(burn_frame=True)
    assert first_frames.world.id != second_frames.world.id
    assert first_base.id != second_base.id
    assert first_frames.world.digest == second_frames.world.digest
    assert first_frames.digest(first_frames.root.id) == second_frames.digest(
        second_frames.root.id
    )
    assert first_frames.digest(first_base.id) == second_frames.digest(
        second_base.id
    )


def test_content_digests_are_stable_for_identical_hypotheses():
    first = bootstrap()
    second = bootstrap()
    first_child = first.frames.create(
        first.frame.id,
        hypotheses=(Hypothesis(runtime_proposition(first, T.TRUE)),),
    )
    second_child = second.frames.create(
        second.frame.id,
        hypotheses=(Hypothesis(runtime_proposition(second, T.TRUE)),),
    )
    assert first.world.id != second.world.id
    assert first.frames.digest(first_child.id) == second.frames.digest(
        second_child.id
    )


def test_a_changed_declaration_changes_the_frame_digest():
    _, _, real_frames, real_base, _ = _content_frames(sort=S.REAL)
    _, _, integer_frames, integer_base, _ = _content_frames(sort=S.INTEGER)
    assert real_frames.digest(real_base.id) != integer_frames.digest(
        integer_base.id
    )


def _defined_frame(*, constant_body: bool):
    table = SymbolTable()
    signature = standard_language(table)
    frames = FrameStore(new_world(signature))
    x = table.intern("x")
    u = table.intern("u")
    base = frames.create(
        frames.root.id, declarations=(Declaration(x, "x", S.REAL),)
    )
    body = T.number(1) if constant_body else T.symbol(x, "x")
    child = frames.create(
        base.id, definitions=(Definition(u, "u", body),)
    )
    return frames, child


def test_a_changed_definition_changes_the_frame_digest():
    first_frames, first = _defined_frame(constant_body=False)
    second_frames, second = _defined_frame(constant_body=True)
    assert first_frames.digest(first.id) != second_frames.digest(second.id)


def _hypothesis_frame(right: int):
    table, signature, frames, base, x = setup()
    proposition = proposition_in(
        frames,
        base.id,
        signature,
        head_app(
            signature,
            StructuralHead.GT,
            T.symbol(x, "x"),
            T.number(right),
        ),
    )
    child = frames.create(base.id, hypotheses=(Hypothesis(proposition),))
    return frames, child


def test_a_changed_hypothesis_changes_the_frame_digest():
    first_frames, first = _hypothesis_frame(0)
    second_frames, second = _hypothesis_frame(1)
    assert first_frames.digest(first.id) != second_frames.digest(second.id)


def test_adding_a_child_frame_does_not_change_the_parent_digest():
    _, _, frames, base, _ = setup()
    before = frames.digest(base.id)
    child = frames.create(base.id)
    assert frames.digest(base.id) == before
    assert frames.digest(child.id) != before
