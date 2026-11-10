"""Algebra views: typed sources, symbol bindings and rendering."""

from dataclasses import replace
from fractions import Fraction

import pytest
from support import head_app, runtime_proposition, typed_in, variable

from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.decisions import Reason
from cas.language.problems import Role
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import bootstrap, bootstrap_parameterized
from cas.semantics.bridge import (
    AlgebraView,
    ConversionKind,
    ConversionWitness,
    Rendered,
    SymbolBinding,
    ViewBuilt,
    ViewRefused,
    _build_view,
    _issue_view,
    typed_view,
)
from cas.semantics.definedness import DefinednessExactness
from cas.semantics.frames import Declaration
from cas.semantics.request import Interpretation
from cas.syntax import term as T


def _typed(runtime, term, frame=None):
    identifier = runtime.frame.id if frame is None else frame
    return typed_in(
        runtime.frames, identifier, runtime.signature, term
    )


def _view(runtime, term, frame=None):
    typed = _typed(runtime, term, frame)
    outcome = runtime.bridge.to_view(typed, runtime.request)
    assert isinstance(outcome, ViewBuilt), outcome
    return outcome.view


def _refused(runtime, term, frame=None):
    typed = _typed(runtime, term, frame)
    outcome = runtime.bridge.to_view(typed, runtime.request)
    assert isinstance(outcome, ViewRefused), outcome
    return outcome


def _nonzero(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NE,
            variable(runtime),
            T.number(0),
        ),
    )


def _issued_view(
    runtime,
    term=None,
    value=None,
    *,
    witness=None,
    source_domain=None,
    valid_on=None,
):
    """Issue a view directly through the sealed factory for a variant test."""
    source_term = variable(runtime) if term is None else term
    typed = _typed(runtime, source_term)
    member = runtime.ring.generator(0) if value is None else value
    return _issue_view(
        typed,
        runtime.parent,
        member,
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        (
            ConversionWitness.representation_isomorphism()
            if witness is None
            else witness
        ),
        source_domain,
        valid_on,
        signature=runtime.signature,
    )


def test_a_polynomial_term_projects_to_an_exact_view(runtime):
    term = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.POWER,
            variable(runtime),
            T.number(2),
        ),
        T.number(1),
    )
    typed = _typed(runtime, term)
    outcome = runtime.bridge.to_view(typed, runtime.request)
    assert isinstance(outcome, ViewBuilt)
    view = outcome.view
    assert view.source is typed
    assert view.parent is runtime.parent
    expected = runtime.ring.add(
        runtime.ring.monomial((2,), Fraction(1)),
        runtime.ring.constant(Fraction(1)),
    )
    assert runtime.parent.ring.equal(view.value, expected)
    assert view.symbols == (
        SymbolBinding(runtime.variable, Role.TARGET, 0),
    )
    assert view.interpretation is Interpretation.FORMAL
    assert view.conversion is ConversionKind.REPRESENTATION_ISOMORPHISM
    assert view.witness == ConversionWitness.representation_isomorphism()
    assert view.source_domain is None
    assert view.valid_on is None
    assert view.signature is runtime.signature
    assert view.region_bindings == typed.bindings.symbols
    definedness = view.definedness
    assert definedness.source == view.source
    assert definedness.domain is None
    assert definedness.valid_on is None
    assert definedness.exactness is DefinednessExactness.TOTAL
    assert definedness.certificate is None


def test_a_constant_source_projects_and_renders(runtime):
    view = _view(runtime, T.number(2))
    rendered = runtime.bridge.render(view, view.value)
    assert isinstance(rendered, Rendered)
    assert rendered.term == T.number(2)


def test_a_symbol_outside_the_view_is_refused_with_a_structured_gap(runtime):
    extra = runtime.table.intern("view_extra")
    frame = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(extra, "view_extra", S.REAL),),
    )
    outcome = _refused(runtime, T.symbol(extra, "view_extra"), frame.id)
    assert "symbol_mapping" in outcome.missing


def test_a_negative_power_is_refused(runtime):
    term = head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(-1),
    )
    outcome = _refused(runtime, term)
    assert "nonnegative_power" in outcome.missing


def test_a_zero_power_of_a_nonconstant_is_refused(runtime):
    term = head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(0),
    )
    outcome = _refused(runtime, term)
    assert "defined_zero_power" in outcome.missing


def test_a_zero_power_of_a_globally_nonzero_constant_is_accepted(runtime):
    term = head_app(
        runtime.signature,
        StructuralHead.POWER,
        T.number(2),
        T.number(0),
    )
    view = _view(runtime, term)
    assert runtime.parent.ring.is_one(view.value)
    rendered = runtime.bridge.render(view, view.value)
    assert isinstance(rendered, Rendered)
    assert rendered.term == T.number(1)


def test_a_non_scalar_source_is_refused(runtime):
    term = head_app(
        runtime.signature,
        StructuralHead.GT,
        variable(runtime),
        T.number(0),
    )
    outcome = _refused(runtime, term)
    assert "scalar_source" in outcome.missing


def test_a_view_cannot_be_constructed_directly(runtime):
    typed = _typed(runtime, variable(runtime))
    with pytest.raises(ValueError):
        AlgebraView(
            typed,
            runtime.parent,
            runtime.parent.ring.zero(),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.FORMAL,
            ConversionWitness.representation_isomorphism(),
            runtime.signature,
            None,
            None,
        )


def test_a_view_cannot_be_replaced(runtime):
    view = _view(runtime, variable(runtime))
    with pytest.raises(ValueError, match="issued only"):
        replace(view, source_domain=None)


def test_region_fields_must_be_propositions(runtime):
    outcome = _issued_view(runtime, source_domain=T.TRUE)
    assert isinstance(outcome, ViewRefused)
    assert "source_domain" in outcome.missing
    outcome = _issued_view(runtime, valid_on=T.TRUE)
    assert isinstance(outcome, ViewRefused)
    assert "valid_on" in outcome.missing


def test_a_total_source_can_carry_a_partial_representation_region(runtime):
    nonzero = _nonzero(runtime)
    view = _issued_view(runtime, valid_on=nonzero)
    assert isinstance(view, AlgebraView)
    assert view.source_domain is None
    assert view.valid_on == nonzero
    definedness = view.definedness
    assert definedness.exactness is DefinednessExactness.SUFFICIENT
    assert definedness.domain is None
    assert definedness.valid_on is not None
    assert definedness.valid_on.condition == nonzero
    assert definedness.certificate is None


def test_the_sealed_factory_accepts_a_validity_region_without_a_domain(
    runtime,
):
    typed = _typed(runtime, variable(runtime))
    nonzero = _nonzero(runtime)
    view = _build_view(
        typed,
        runtime.parent,
        runtime.ring.zero(),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        nonzero,
        signature=runtime.signature,
    )
    assert isinstance(view, AlgebraView)
    assert view.source_domain is None
    assert view.valid_on == nonzero
    assert view.definedness.domain is None
    assert view.definedness.certificate is None


def test_regions_from_different_worlds_are_refused(runtime):
    other = bootstrap()
    foreign = runtime_proposition(
        other,
        head_app(
            other.signature,
            StructuralHead.NE,
            variable(other),
            T.number(0),
        ),
    )
    refused = _issued_view(
        runtime, source_domain=foreign, valid_on=foreign
    )
    assert isinstance(refused, ViewRefused)
    assert "region_world" in refused.missing

    mixed = _issued_view(
        runtime, source_domain=_nonzero(runtime), valid_on=foreign
    )
    assert isinstance(mixed, ViewRefused)
    assert "region_world" in mixed.missing


def _child_frame(runtime, name="view_region_child", sort=S.REAL):
    extra = runtime.table.intern(name)
    frame = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(extra, name, sort),),
    )
    return extra, frame


def test_regions_from_different_frames_must_share_one_meaning(runtime):
    _, child = _child_frame(runtime)
    everywhere = runtime_proposition(runtime, T.TRUE)
    child_nonzero = runtime_proposition(
        runtime, _nonzero(runtime).term, frame=child.id
    )
    refused = _issued_view(
        runtime, source_domain=everywhere, valid_on=child_nonzero
    )
    assert isinstance(refused, ViewRefused)
    assert "region_meaning" in refused.missing


def test_a_region_from_a_descendant_frame_of_the_same_world_is_accepted(
    runtime,
):
    _, child = _child_frame(runtime)
    child_true = runtime_proposition(runtime, T.TRUE, frame=child.id)
    child_nonzero = runtime_proposition(
        runtime, _nonzero(runtime).term, frame=child.id
    )
    view = _issued_view(
        runtime, source_domain=child_true, valid_on=child_nonzero
    )
    assert isinstance(view, AlgebraView)
    assert view.source_domain == child_true
    assert view.valid_on == child_nonzero

    partial = _issued_view(runtime, valid_on=child_nonzero)
    assert isinstance(partial, AlgebraView)
    assert partial.definedness.domain is None
    assert partial.definedness.valid_on is not None
    assert partial.definedness.certificate is None


def test_a_view_region_can_use_extra_child_frame_coordinates(runtime):
    extra, child = _child_frame(runtime, "view_extra_coordinate")
    product = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        variable(runtime),
        T.symbol(extra, "view_extra_coordinate"),
    )
    valid_on = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NE,
            product,
            T.number(0),
        ),
        frame=child.id,
    )
    source = _typed(runtime, variable(runtime))
    bindings = (
        Ty.FreeSymbol(runtime.variable, S.REAL),
        Ty.FreeSymbol(extra, S.REAL),
    )
    view = _issue_view(
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        valid_on,
        signature=runtime.signature,
        region_bindings=bindings,
    )
    assert isinstance(view, AlgebraView)
    assert view.region_bindings == bindings
    record = view.definedness
    assert record.exactness is DefinednessExactness.SUFFICIENT
    assert record.domain is None
    assert record.valid_on is not None
    assert record.valid_on.coordinates == (
        runtime.variable,
        extra,
    )
    assert record.valid_on.sort_of(runtime.variable) is S.REAL
    assert record.valid_on.sort_of(extra) is S.REAL
    assert record.valid_on.is_dense
    assert record.valid_on.condition is valid_on
    assert record.certificate is None


def test_a_region_binding_cannot_override_a_source_symbol_sort(runtime):
    source = _typed(runtime, variable(runtime))
    forged = (Ty.FreeSymbol(runtime.variable, S.INTEGER),)
    outcome = _issue_view(
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        None,
        signature=runtime.signature,
        region_bindings=forged,
    )
    assert isinstance(outcome, ViewRefused), outcome
    assert outcome.reason is Reason.FRAGMENT
    assert "region_bindings" in outcome.missing
    assert "region bindings" in outcome.detail
    assert str(runtime.variable) in outcome.detail

    with pytest.raises(ValueError, match="region bindings"):
        _build_view(
            source,
            runtime.parent,
            runtime.ring.generator(0),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.FORMAL,
            ConversionWitness.representation_isomorphism(),
            None,
            None,
            signature=runtime.signature,
            region_bindings=forged,
        )


def test_an_integer_source_cannot_be_disguised_as_a_dense_region_coordinate(
    runtime,
):
    symbol, child = _child_frame(runtime, "view_disguised_integer", S.INTEGER)
    y = T.symbol(symbol, "view_disguised_integer")
    source = _typed(runtime, y, child.id)
    everywhere = runtime_proposition(runtime, T.TRUE, frame=child.id)
    nonzero = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NE,
            y,
            T.number(0),
        ),
        frame=child.id,
    )
    arguments = (
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(symbol, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        everywhere,
        nonzero,
    )
    # The source's own binding keeps the integer sort, so the dense
    # subregion certificate path is honestly refused when read.
    honest = _issue_view(
        *arguments, signature=runtime.signature
    )
    assert isinstance(honest, AlgebraView)
    assert honest.region_bindings == source.bindings.symbols
    with pytest.raises(ValueError, match="dense"):
        honest.definedness

    forged = (Ty.FreeSymbol(symbol, S.REAL),)
    refused = _issue_view(
        *arguments,
        signature=runtime.signature,
        region_bindings=forged,
    )
    assert isinstance(refused, ViewRefused), refused
    assert refused.reason is Reason.FRAGMENT
    assert "region_bindings" in refused.missing
    assert str(symbol) in refused.detail

    with pytest.raises(ValueError, match="region bindings"):
        _build_view(
            *arguments,
            signature=runtime.signature,
            region_bindings=forged,
        )


def test_a_consistent_region_binding_with_an_extra_coordinate_is_accepted(
    runtime,
):
    extra, child = _child_frame(runtime, "view_consistent_extra")
    condition = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.symbol(extra, "view_consistent_extra"),
        ),
        frame=child.id,
    )
    source = _typed(runtime, variable(runtime))
    bindings = (
        Ty.FreeSymbol(runtime.variable, S.REAL),
        Ty.FreeSymbol(extra, S.REAL),
    )
    view = _issue_view(
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        condition,
        signature=runtime.signature,
        region_bindings=bindings,
    )
    assert isinstance(view, AlgebraView), view
    assert view.region_bindings == bindings
    record = view.definedness
    assert record.exactness is DefinednessExactness.SUFFICIENT
    assert record.valid_on is not None
    assert record.valid_on.sort_of(runtime.variable) is S.REAL
    assert record.valid_on.sort_of(extra) is S.REAL
    assert record.valid_on.is_dense
    assert record.valid_on.condition is condition


def test_a_view_region_binding_must_cover_every_region_symbol(runtime):
    extra, child = _child_frame(runtime, "view_uncovered_coordinate")
    product = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        variable(runtime),
        T.symbol(extra, "view_uncovered_coordinate"),
    )
    valid_on = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NE,
            product,
            T.number(0),
        ),
        frame=child.id,
    )
    source = _typed(runtime, variable(runtime))
    outcome = _issue_view(
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        valid_on,
        signature=runtime.signature,
        region_bindings=(
            Ty.FreeSymbol(runtime.variable, S.REAL),
        ),
    )
    assert isinstance(outcome, ViewRefused), outcome
    assert outcome.reason is Reason.FRAGMENT
    assert "region_bindings" in outcome.missing
    assert "validity region" in outcome.detail

    with pytest.raises(ValueError, match="region bindings"):
        _build_view(
            source,
            runtime.parent,
            runtime.ring.generator(0),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.FORMAL,
            ConversionWitness.representation_isomorphism(),
            None,
            valid_on,
            signature=runtime.signature,
            region_bindings=(
                Ty.FreeSymbol(runtime.variable, S.REAL),
            ),
        )


def test_a_strict_subregion_on_non_dense_coordinates_is_refused(runtime):
    symbol, child = _child_frame(runtime, "view_integer_y", S.INTEGER)
    y = T.symbol(symbol, "view_integer_y")
    source = _typed(runtime, y, child.id)
    everywhere = runtime_proposition(runtime, T.TRUE, frame=child.id)
    nonzero = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NE,
            y,
            T.number(0),
        ),
        frame=child.id,
    )
    view = _issue_view(
        source,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(symbol, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        everywhere,
        nonzero,
        signature=runtime.signature,
    )
    assert isinstance(view, AlgebraView)
    assert view.region_bindings == source.bindings.symbols
    with pytest.raises(ValueError, match="dense"):
        view.definedness


def test_the_sealed_factory_rejects_regions_from_different_worlds(runtime):
    other = bootstrap()
    foreign = runtime_proposition(
        other,
        head_app(
            other.signature,
            StructuralHead.NE,
            variable(other),
            T.number(0),
        ),
    )
    typed = _typed(runtime, variable(runtime))
    with pytest.raises(ValueError, match="another meaning world"):
        _build_view(
            typed,
            runtime.parent,
            runtime.ring.zero(),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.FORMAL,
            ConversionWitness.representation_isomorphism(),
            None,
            foreign,
            signature=runtime.signature,
        )


def test_the_sealed_factory_rejects_regions_from_different_frames(runtime):
    _, child = _child_frame(runtime)
    everywhere = runtime_proposition(runtime, T.TRUE)
    child_nonzero = runtime_proposition(
        runtime, _nonzero(runtime).term, frame=child.id
    )
    typed = _typed(runtime, variable(runtime))
    with pytest.raises(ValueError, match="different meaning"):
        _build_view(
            typed,
            runtime.parent,
            runtime.ring.zero(),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.FORMAL,
            ConversionWitness.representation_isomorphism(),
            everywhere,
            child_nonzero,
            signature=runtime.signature,
        )


def test_a_view_validity_region_must_be_inside_the_source_domain(runtime):
    nonzero = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NE,
            variable(runtime),
            T.number(0),
        ),
    )
    everywhere = runtime_proposition(runtime, T.TRUE)
    refused = _issued_view(
        runtime,
        source_domain=nonzero,
        valid_on=everywhere,
    )
    assert isinstance(refused, ViewRefused)
    assert refused.reason is Reason.GUARDED
    assert "region_coverage" in refused.missing
    assert refused.conditions == (everywhere, nonzero)
    accepted = _issued_view(
        runtime,
        source_domain=everywhere,
        valid_on=nonzero,
    )
    assert isinstance(accepted, AlgebraView)
    assert accepted.source_domain == everywhere
    assert accepted.valid_on == nonzero
    definedness = accepted.definedness
    assert definedness.exactness is DefinednessExactness.SUFFICIENT
    assert definedness.certificate is not None


def test_a_view_region_must_prove_its_definedness_premises(runtime):
    x = variable(runtime)
    powered = head_app(
        runtime.signature, StructuralHead.POWER, x, T.number(-1)
    )
    partial = runtime_proposition(
        runtime,
        head_app(
            runtime.signature, StructuralHead.EQ, powered, powered
        ),
    )
    assert tuple(
        premise.term for premise in partial.definedness
    ) == (
        head_app(
            runtime.signature, StructuralHead.NE, x, T.number(0)
        ),
    )
    refused = _issued_view(runtime, valid_on=partial)
    assert isinstance(refused, ViewRefused)
    assert refused.reason is Reason.GUARDED
    assert "region_definedness" in refused.missing
    assert refused.conditions == (partial,)


def test_a_view_region_that_proves_its_premises_is_accepted(runtime):
    x = variable(runtime)
    powered = head_app(
        runtime.signature, StructuralHead.POWER, x, T.number(-1)
    )
    partial = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.AND,
            head_app(
                runtime.signature, StructuralHead.GT, x, T.number(0)
            ),
            head_app(
                runtime.signature, StructuralHead.EQ, powered, powered
            ),
        ),
    )
    assert tuple(
        premise.term for premise in partial.definedness
    ) == (
        head_app(
            runtime.signature, StructuralHead.NE, x, T.number(0)
        ),
    )
    view = _issued_view(runtime, valid_on=partial)
    assert isinstance(view, AlgebraView)
    assert view.valid_on == partial
    definedness = view.definedness
    assert definedness.exactness is DefinednessExactness.SUFFICIENT
    assert definedness.domain is None
    assert definedness.valid_on is not None
    assert definedness.valid_on.condition == partial
    assert definedness.certificate is None


def test_the_sealed_factory_rejects_a_partial_region_when_read(runtime):
    x = variable(runtime)
    powered = head_app(
        runtime.signature, StructuralHead.POWER, x, T.number(-1)
    )
    partial = runtime_proposition(
        runtime,
        head_app(
            runtime.signature, StructuralHead.EQ, powered, powered
        ),
    )
    typed = _typed(runtime, x)
    view = _build_view(
        typed,
        runtime.parent,
        runtime.ring.zero(),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        partial,
        signature=runtime.signature,
    )
    with pytest.raises(ValueError, match="definedness premises"):
        view.definedness


def test_a_conversion_witness_must_be_coherent():
    with pytest.raises(ValueError, match="witness"):
        ConversionWitness(
            ConversionKind.REPRESENTATION_ISOMORPHISM,
            injective=False,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=True,
        )
    with pytest.raises(ValueError, match="witness"):
        ConversionWitness(
            ConversionKind.REPRESENTATION_ISOMORPHISM,
            injective=True,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=False,
        )
    with pytest.raises(ValueError, match="witness"):
        ConversionWitness(
            ConversionKind.EMBEDDING,
            injective=True,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=False,
        )
    with pytest.raises(TypeError, match="boolean"):
        ConversionWitness(
            ConversionKind.HOMOMORPHISM,
            injective=1,  # type: ignore[arg-type]
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=True,
        )
    with pytest.raises(TypeError, match="boolean"):
        ConversionWitness(
            ConversionKind.HOMOMORPHISM,
            injective=True,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=1,  # type: ignore[arg-type]
        )


def test_the_standard_isomorphism_witness_preserves_definedness():
    witness = ConversionWitness.representation_isomorphism()
    assert witness.kind is ConversionKind.REPRESENTATION_ISOMORPHISM
    assert witness.injective is True
    assert witness.preserves_equality is True
    assert witness.preserves_nonzero is True
    assert witness.preserves_definedness is True


def test_an_embedded_view_refuses_a_homomorphism_witness(runtime):
    witness = ConversionWitness(
        ConversionKind.HOMOMORPHISM,
        injective=True,
        preserves_equality=True,
        preserves_nonzero=True,
        preserves_definedness=True,
    )
    typed = _typed(runtime, variable(runtime))
    outcome = _issue_view(
        typed,
        runtime.parent,
        runtime.ring.generator(0),
        (SymbolBinding(runtime.variable, Role.TARGET, 0),),
        Interpretation.EMBEDDED,
        witness,
        None,
        None,
        signature=runtime.signature,
    )
    assert isinstance(outcome, ViewRefused), outcome
    assert outcome.reason is Reason.FRAGMENT
    assert "interpretation_witness" in outcome.missing
    assert "embedded interpretation" in outcome.detail


def test_the_sealed_factory_rejects_an_embedded_homomorphism(runtime):
    witness = ConversionWitness(
        ConversionKind.HOMOMORPHISM,
        injective=True,
        preserves_equality=True,
        preserves_nonzero=True,
        preserves_definedness=True,
    )
    typed = _typed(runtime, variable(runtime))
    with pytest.raises(ValueError, match="embedded interpretation"):
        _build_view(
            typed,
            runtime.parent,
            runtime.ring.zero(),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.EMBEDDED,
            witness,
            None,
            None,
            signature=runtime.signature,
        )


def test_a_parameter_family_view_refuses_non_isomorphism_witnesses():
    runtime = bootstrap_parameterized()
    parameter = runtime.request.parameters[0]
    typed = _typed(runtime, variable(runtime))
    symbols = (
        SymbolBinding(runtime.variable, Role.TARGET, 0),
        SymbolBinding(parameter, Role.PARAMETER, 0),
    )
    for witness in (
        ConversionWitness(
            ConversionKind.EMBEDDING,
            injective=True,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=True,
        ),
        ConversionWitness(
            ConversionKind.HOMOMORPHISM,
            injective=True,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=True,
        ),
    ):
        outcome = _issue_view(
            typed,
            runtime.parent,
            runtime.ring.generator(0),
            symbols,
            Interpretation.PARAMETER_FAMILY,
            witness,
            None,
            None,
            signature=runtime.signature,
        )
        assert isinstance(outcome, ViewRefused), outcome
        assert outcome.reason is Reason.FRAGMENT
        assert "interpretation_witness" in outcome.missing
        assert "parameter-family interpretation" in outcome.detail


def test_the_sealed_factory_rejects_a_parameter_family_embedding():
    runtime = bootstrap_parameterized()
    parameter = runtime.request.parameters[0]
    typed = _typed(runtime, variable(runtime))
    with pytest.raises(ValueError, match="parameter-family interpretation"):
        _build_view(
            typed,
            runtime.parent,
            runtime.ring.generator(0),
            (
                SymbolBinding(runtime.variable, Role.TARGET, 0),
                SymbolBinding(parameter, Role.PARAMETER, 0),
            ),
            Interpretation.PARAMETER_FAMILY,
            ConversionWitness(
                ConversionKind.EMBEDDING,
                injective=True,
                preserves_equality=True,
                preserves_nonzero=True,
                preserves_definedness=True,
            ),
            None,
            None,
            signature=runtime.signature,
        )


def test_an_embedded_view_accepts_embedding_and_isomorphism_witnesses(runtime):
    typed = _typed(runtime, variable(runtime))
    for witness in (
        ConversionWitness(
            ConversionKind.EMBEDDING,
            injective=True,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=True,
        ),
        ConversionWitness.representation_isomorphism(),
    ):
        view = _issue_view(
            typed,
            runtime.parent,
            runtime.ring.generator(0),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.EMBEDDED,
            witness,
            None,
            None,
            signature=runtime.signature,
        )
        assert isinstance(view, AlgebraView), view
        assert view.interpretation is Interpretation.EMBEDDED
        assert view.witness is witness


def test_the_specialization_view_issues_an_embedded_isomorphism():
    runtime = bootstrap_parameterized()
    specialization = runtime.specialization
    assert specialization is not None
    typed = _typed(runtime, variable(runtime))
    outcome = specialization.bridge.to_view(typed, specialization.request)
    assert isinstance(outcome, ViewBuilt), outcome
    assert outcome.view.interpretation is Interpretation.EMBEDDED
    assert (
        outcome.view.conversion is ConversionKind.REPRESENTATION_ISOMORPHISM
    )


def test_a_parameterized_view_maps_parameters_to_coefficient_generators():
    runtime = bootstrap_parameterized()
    parameter = runtime.request.parameters[0]
    term = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            T.symbol(parameter, "a"),
            head_app(
                runtime.signature,
                StructuralHead.POWER,
                variable(runtime),
                T.number(2),
            ),
        ),
        T.number(1),
    )
    view = _view(runtime, term)
    assert view.generators_for(Role.TARGET) == (runtime.variable,)
    assert view.generators_for(Role.PARAMETER) == (parameter,)
    assert view.interpretation is Interpretation.PARAMETER_FAMILY
    assert view.conversion is ConversionKind.REPRESENTATION_ISOMORPHISM
    assert view.witness == ConversionWitness.representation_isomorphism()
    rendered = runtime.bridge.render(view, view.value)
    assert isinstance(rendered, Rendered)
    again = _view(runtime, rendered.term)
    assert runtime.parent.ring.equal(again.value, view.value)


class FixedViewBridge:
    """A bridge that returns one already-issued view for any source."""

    def __init__(self, view):
        self.view = view
        self.ring = view.parent.ring

    def to_view(self, source, request):
        del source, request
        return ViewBuilt(self.view)

    def render(self, view, value):
        raise AssertionError("the fixed bridge does not render")


def test_typed_view_refuses_a_homomorphic_conversion(runtime):
    witness = ConversionWitness(
        ConversionKind.HOMOMORPHISM,
        injective=False,
        preserves_equality=True,
        preserves_nonzero=False,
        preserves_definedness=False,
    )
    view = _issued_view(runtime, witness=witness)
    assert isinstance(view, AlgebraView)
    outcome = typed_view(
        FixedViewBridge(view),
        view.source.term,
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        runtime.request,
    )
    assert isinstance(outcome, ViewRefused), outcome
    assert "conversion_witness" in outcome.missing


def test_typed_view_refuses_a_non_equality_preserving_witness(runtime):
    witness = ConversionWitness(
        ConversionKind.HOMOMORPHISM,
        injective=True,
        preserves_equality=False,
        preserves_nonzero=True,
        preserves_definedness=True,
    )
    view = _issued_view(runtime, witness=witness)
    assert isinstance(view, AlgebraView)
    outcome = typed_view(
        FixedViewBridge(view),
        view.source.term,
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        runtime.request,
    )
    assert isinstance(outcome, ViewRefused), outcome
    assert "conversion_witness" in outcome.missing


def test_typed_view_admits_a_total_view_through_a_non_preserving_homomorphism(
    runtime,
):
    witness = ConversionWitness(
        ConversionKind.HOMOMORPHISM,
        injective=True,
        preserves_equality=True,
        preserves_nonzero=True,
        preserves_definedness=False,
    )
    view = _issued_view(runtime, witness=witness)
    assert isinstance(view, AlgebraView)
    assert view.interpretation is Interpretation.FORMAL
    assert view.source_domain is None
    assert view.valid_on is None
    outcome = typed_view(
        FixedViewBridge(view),
        view.source.term,
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        runtime.request,
    )
    assert isinstance(outcome, AlgebraView), outcome
    assert outcome.conversion is ConversionKind.HOMOMORPHISM
    assert outcome.witness is witness
    assert outcome.definedness.exactness is DefinednessExactness.TOTAL


def test_a_regional_view_needs_a_definedness_preserving_witness(runtime):
    witness = ConversionWitness(
        ConversionKind.HOMOMORPHISM,
        injective=True,
        preserves_equality=True,
        preserves_nonzero=True,
        preserves_definedness=False,
    )
    nonzero = _nonzero(runtime)
    for regions in (
        {"valid_on": nonzero},
        {"source_domain": nonzero, "valid_on": nonzero},
    ):
        refused = _issued_view(runtime, witness=witness, **regions)
        assert isinstance(refused, ViewRefused), refused
        assert refused.reason is Reason.FRAGMENT
        assert "conversion_witness" in refused.missing
        assert "does not preserve definedness" in refused.detail


def test_the_sealed_factory_rejects_a_regional_view_without_preserving(
    runtime,
):
    witness = ConversionWitness(
        ConversionKind.HOMOMORPHISM,
        injective=True,
        preserves_equality=True,
        preserves_nonzero=True,
        preserves_definedness=False,
    )
    typed = _typed(runtime, variable(runtime))
    with pytest.raises(ValueError, match="does not preserve definedness"):
        _build_view(
            typed,
            runtime.parent,
            runtime.ring.zero(),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.FORMAL,
            witness,
            None,
            _nonzero(runtime),
            signature=runtime.signature,
        )


def test_typed_view_admits_an_embedding_conversion(runtime):
    witness = ConversionWitness(
        ConversionKind.EMBEDDING,
        injective=True,
        preserves_equality=True,
        preserves_nonzero=True,
        preserves_definedness=True,
    )
    view = _issued_view(runtime, witness=witness)
    assert isinstance(view, AlgebraView)
    outcome = typed_view(
        FixedViewBridge(view),
        view.source.term,
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        runtime.request,
    )
    assert isinstance(outcome, AlgebraView), outcome
    assert outcome.conversion is ConversionKind.EMBEDDING
    assert outcome.witness is witness


def test_typed_view_refuses_a_view_from_another_interpretation():
    runtime = bootstrap_parameterized()
    view = _view(runtime, T.number(2))
    formal_request = replace(
        runtime.request, interpretation=Interpretation.FORMAL
    )
    outcome = typed_view(
        FixedViewBridge(view),
        view.source.term,
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        formal_request,
    )
    assert isinstance(outcome, ViewRefused), outcome
    assert "interpretation_mismatch" in outcome.missing


def test_a_parameter_family_view_needs_a_parameter_binding(runtime):
    typed = _typed(runtime, T.number(2))
    with pytest.raises(ValueError, match="parameter-family"):
        _issue_view(
            typed,
            runtime.parent,
            runtime.ring.zero(),
            (SymbolBinding(runtime.variable, Role.TARGET, 0),),
            Interpretation.PARAMETER_FAMILY,
            ConversionWitness.representation_isomorphism(),
            None,
            None,
            signature=runtime.signature,
        )


def test_a_non_parameter_family_view_cannot_bind_parameters():
    runtime = bootstrap_parameterized()
    typed = _typed(runtime, T.number(2))
    parameter = runtime.request.parameters[0]
    with pytest.raises(ValueError, match="cannot bind parameters"):
        _issue_view(
            typed,
            runtime.parent,
            runtime.ring.zero(),
            (
                SymbolBinding(runtime.variable, Role.TARGET, 0),
                SymbolBinding(parameter, Role.PARAMETER, 0),
            ),
            Interpretation.FORMAL,
            ConversionWitness.representation_isomorphism(),
            None,
            None,
            signature=runtime.signature,
        )


class _InconsistentSortEnvironment:
    """Return a scalar sort during inference and a function sort afterwards.

    A well-typed scalar expression cannot have a non-scalar free symbol.  The
    bridge still defends that invariant, so this environment issues the one
    sealed typed expression that exercises the refusal without forging it.
    """

    def __init__(self, symbol_id, scalar, binding):
        self._symbol_id = symbol_id
        self._scalar = scalar
        self._binding = binding
        self._calls = 0

    def sort_of(self, symbol_id):
        if symbol_id != self._symbol_id:
            return None
        self._calls += 1
        return self._scalar if self._calls == 1 else self._binding

    def bound_sort(self, index):
        del index
        return None


def test_a_non_scalar_free_symbol_is_refused(runtime):
    extra = runtime.table.intern("view_function")
    environment = _InconsistentSortEnvironment(
        extra, S.REAL, S.FunctionSort((S.REAL,), S.REAL)
    )
    typed = Ty.typed(
        T.symbol(extra, "view_function"),
        runtime.signature,
        environment,
        runtime.frame.meaning,
    )
    assert isinstance(typed, Ty.TypedExpr)
    outcome = runtime.bridge.to_view(typed, runtime.request)
    assert isinstance(outcome, ViewRefused), outcome
    assert "scalar_symbol" in outcome.missing
    assert str(extra) in outcome.detail
