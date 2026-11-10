"""Term/algebra bridge: explicit fragments, regions and refusals."""

from fractions import Fraction

import pytest
from support import admitted, head_app, render_value, structural, view_of

from cas.algebra.integers import IntegerRing
from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import FrameId
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.meaning import MeaningKey
from cas.language.problems import (
    ParameterMode,
    ValueDomain,
    VariableRoles,
)
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.runtime.bootstrap import bootstrap
from cas.semantics.bridge import (
    ConversionWitness,
    RationalFunctionBridge,
    Rendered,
    RenderRefused,
    SimplePolynomialBridge,
    ViewBuilt,
    ViewRefused,
)
from cas.semantics.frames import FrameSorts
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.syntax import term as T


def x_term(runtime) -> T.SymbolRef:
    return T.symbol(runtime.variable, "x")


def bridge(runtime, term: T.Term):
    return view_of(runtime, term).value


def plus(runtime, *arguments: T.Term) -> T.Apply:
    return head_app(runtime.signature, StructuralHead.PLUS, *arguments)


def times(runtime, *arguments: T.Term) -> T.Apply:
    return head_app(runtime.signature, StructuralHead.TIMES, *arguments)


def power(runtime, base: T.Term, exponent: T.Term) -> T.Apply:
    return head_app(runtime.signature, StructuralHead.POWER, base, exponent)


def render(runtime, value):
    return render_value(runtime, value)


def rational_bridge(runtime) -> RationalFunctionBridge[Fraction]:
    field = RationalFunctionField(runtime.ring)
    registry = ParentRegistry()
    parent = registry.intern(
        ParentSpec(
            "rational_function",
            base=runtime.parent.spec,
            generators=runtime.ring.generators,
            options=(),
        ),
        field,
    )
    return RationalFunctionBridge(
        field,
        parent,
        runtime.world.id,
        runtime.signature,
        runtime.frames,
        runtime.table.name_of,
        T.number,
    )


def test_literals_and_the_generator_bridge(runtime):
    x = x_term(runtime)
    ring = runtime.ring
    assert ring.equal(bridge(runtime, T.number(3)), ring.constant(Fraction(3)))
    assert ring.equal(
        bridge(runtime, T.number(Fraction(1, 2))),
        ring.constant(Fraction(1, 2)),
    )
    assert ring.equal(bridge(runtime, x), ring.generator(0))


def test_sums_products_and_powers_bridge(runtime):
    x = x_term(runtime)
    ring = runtime.ring
    term = plus(runtime, times(runtime, T.number(2), x), T.number(1), power(runtime, x, T.number(2)))
    expected = ring.add(
        ring.monomial((2,), Fraction(1)),
        ring.add(ring.monomial((1,), Fraction(2)), ring.constant(Fraction(1))),
    )
    assert ring.equal(bridge(runtime, term), expected)


def test_outside_the_fragment_the_bridge_is_refused(runtime):
    x = x_term(runtime)
    y = T.symbol(runtime.table.intern("y"), "y")
    function = T.app(T.symbol(runtime.table.intern("Sin"), "Sin"), x)
    refused = [
        (power(runtime, x, T.number(-1)), "nonnegative_power"),
        (T.TRUE, "scalar_source"),
        (T.quote(x), "scalar_source"),
    ]
    for term, missing in refused:
        outcome = admitted(runtime, term)
        assert isinstance(outcome, ViewRefused), outcome
        assert missing in outcome.missing
    ill_typed = [
        power(runtime, x, x),
        T.app(structural(runtime.signature, StructuralHead.POWER), x, T.number(2), T.number(3)),
        y,
        function,
        T.BoundVar(0),
    ]
    for term in ill_typed:
        outcome = admitted(runtime, term)
        assert isinstance(outcome, Ty.TypedExprFailure), outcome


def test_rendering_zero_one_and_the_generator(runtime):
    x = x_term(runtime)
    ring = runtime.ring
    assert render(runtime, ring.zero()) == T.number(0)
    assert render(runtime, ring.one()) == T.number(1)
    assert render(runtime, ring.generator(0)) == x


def test_rendering_uses_canonical_term_order(runtime):
    x = x_term(runtime)
    ring = runtime.ring
    value = ring.add(
        ring.monomial((1,), Fraction(2)), ring.constant(Fraction(1))
    )
    assert render(runtime, value) == plus(
        runtime, T.number(1), times(runtime, T.number(2), x)
    )
    square = ring.monomial((2,), Fraction(1))
    assert render(runtime, square) == power(runtime, x, T.number(2))


def test_round_trip_through_terms_preserves_the_element(runtime):
    ring = runtime.ring
    value = ring.add(
        ring.monomial((2,), Fraction(3)),
        ring.add(ring.neg(ring.generator(0)), ring.constant(Fraction(1, 2))),
    )
    assert ring.equal(bridge(runtime, render(runtime, value)), value)
    assert ring.equal(bridge(runtime, render(runtime, ring.zero())), ring.zero())


def test_rational_bridge_accepts_negative_powers_and_round_trips(runtime):
    bridge_value = rational_bridge(runtime)
    x = x_term(runtime)
    one_plus_x = plus(runtime, x, T.number(1))
    term = times(
        runtime,
        x,
        power(runtime, one_plus_x, T.number(-1)),
    )
    view = view_of(runtime, term, bridge=bridge_value)
    rendered = bridge_value.render(view, view.value)
    assert isinstance(rendered, Rendered)
    round_trip = view_of(runtime, rendered.term, bridge=bridge_value)
    assert bridge_value.field.equal(round_trip.value, view.value)
    refused = admitted(
        runtime,
        power(runtime, x, T.number(Fraction(1, 2))),
        bridge=bridge_value,
    )
    assert isinstance(refused, ViewRefused)
    assert "integer_exponent" in refused.missing
    y = T.symbol(runtime.table.intern("y"), "y")
    assert isinstance(
        admitted(runtime, y, bridge=bridge_value), Ty.TypedExprFailure
    )


def test_rational_bridge_enforces_the_zero_power_boundary(runtime):
    bridge_value = rational_bridge(runtime)
    x = x_term(runtime)
    cancelled = plus(runtime, x, times(runtime, T.number(-1), x))
    for base in (T.number(0), x, cancelled):
        outcome = admitted(
            runtime,
            power(runtime, base, T.number(0)),
            bridge=bridge_value,
        )
        assert isinstance(outcome, ViewRefused), outcome
        assert "defined_zero_power" in outcome.missing
    for base in (T.number(2), plus(runtime, cancelled, T.number(2))):
        view = view_of(
            runtime,
            power(runtime, base, T.number(0)),
            bridge=bridge_value,
        )
        assert bridge_value.field.is_one(view.value)
        assert view.valid_on is None
    x_over_x = times(runtime, x, power(runtime, x, T.number(-1)))
    outcome = admitted(
        runtime,
        power(runtime, x_over_x, T.number(0)),
        bridge=bridge_value,
    )
    assert isinstance(outcome, ViewRefused)
    assert "defined_zero_power" in outcome.missing
    # A zero power of a negative power is refused even when the inverse has a
    # nonzero literal base: the bridge does not try to prove the hole away.
    inverse_constant = power(runtime, T.number(2), T.number(-1))
    outcome = admitted(
        runtime,
        power(runtime, inverse_constant, T.number(0)),
        bridge=bridge_value,
    )
    assert isinstance(outcome, ViewRefused)
    assert "defined_zero_power" in outcome.missing
    for source in (
        power(runtime, T.number(0), T.number(-1)),
        power(runtime, cancelled, T.number(-1)),
    ):
        outcome = admitted(runtime, source, bridge=bridge_value)
        assert isinstance(outcome, ViewRefused)
        assert "defined_negative_power" in outcome.missing
    assert isinstance(
        admitted(
            runtime,
            power(runtime, x, T.number(-1)),
            bridge=bridge_value,
        ),
        ViewBuilt,
    )


def test_a_total_rational_term_has_no_region(runtime):
    bridge_value = rational_bridge(runtime)
    view = view_of(
        runtime,
        plus(runtime, x_term(runtime), T.number(1)),
        bridge=bridge_value,
    )
    assert view.source_domain is None
    assert view.valid_on is None


def test_a_rational_denominator_carries_its_nonzero_region(runtime):
    bridge_value = rational_bridge(runtime)
    x = x_term(runtime)
    denominator = plus(runtime, T.number(1), x)
    view = view_of(
        runtime,
        power(runtime, denominator, T.number(-1)),
        bridge=bridge_value,
    )
    assert view.source_domain is not None
    assert view.valid_on is not None
    assert view.source_domain is view.valid_on
    assert view.witness == ConversionWitness.representation_isomorphism()
    assert view.witness.preserves_definedness is True
    assert view.valid_on.term == head_app(
        runtime.signature,
        StructuralHead.NE,
        denominator,
        T.number(0),
    )


def test_polynomial_and_rational_views_preserve_definedness(runtime):
    polynomial = view_of(runtime, x_term(runtime))
    assert polynomial.interpretation is Interpretation.FORMAL
    assert polynomial.witness.preserves_definedness is True
    assert polynomial.witness == ConversionWitness.representation_isomorphism()
    rational = view_of(
        runtime,
        power(runtime, x_term(runtime), T.number(-1)),
        bridge=rational_bridge(runtime),
    )
    assert rational.interpretation is Interpretation.FORMAL
    assert rational.witness.preserves_definedness is True
    assert rational.witness == ConversionWitness.representation_isomorphism()


def test_a_cancelled_denominator_still_carries_its_hole(runtime):
    bridge_value = rational_bridge(runtime)
    x = x_term(runtime)
    view = view_of(
        runtime,
        times(runtime, x, power(runtime, x, T.number(-1))),
        bridge=bridge_value,
    )
    assert bridge_value.field.is_one(view.value)
    assert view.valid_on is not None
    assert view.valid_on.term == head_app(
        runtime.signature,
        StructuralHead.NE,
        x,
        T.number(0),
    )


def test_the_rational_bridge_refuses_outside_its_fragment(runtime):
    bridge_value = rational_bridge(runtime)
    x = x_term(runtime)
    for term, missing in (
        (power(runtime, x, T.number(Fraction(1, 2))), "integer_exponent"),
        (T.TRUE, "scalar_source"),
    ):
        outcome = admitted(runtime, term, bridge=bridge_value)
        assert isinstance(outcome, ViewRefused), outcome
        assert missing in outcome.missing


def test_the_rational_bridge_refuses_a_foreign_source_frame(runtime):
    bridge_value = rational_bridge(runtime)
    typed = Ty.typed(
        x_term(runtime),
        runtime.signature,
        FrameSorts(runtime.frames, runtime.frame.id),
        MeaningKey(runtime.world.id, FrameId(10_000)),
    )
    assert isinstance(typed, Ty.TypedExpr)
    outcome = bridge_value.to_view(typed, runtime.request)
    assert isinstance(outcome, ViewRefused)
    assert "source_frame" in outcome.missing


def test_a_request_role_set_from_another_world_is_refused(runtime):
    other = bootstrap()
    assert other.world.id != runtime.world.id
    assert other.variable == runtime.variable
    typed = Ty.typed(
        x_term(runtime),
        runtime.signature,
        FrameSorts(runtime.frames, runtime.frame.id),
        runtime.frame.meaning,
    )
    assert isinstance(typed, Ty.TypedExpr)
    outcome = runtime.bridge.to_view(typed, other.request)
    assert isinstance(outcome, ViewRefused)
    assert "request_world" in outcome.missing


def test_rendering_requires_the_structural_heads(runtime):
    bare = LanguageSignature.build({})
    bare_bridge = SimplePolynomialBridge(
        runtime.ring,
        runtime.parent,
        runtime.world.id,
        bare,
        runtime.table.name_of,
        T.number,
    )
    view = view_of(runtime, T.number(1), bridge=bare_bridge)
    outcome = bare_bridge.render(view, runtime.ring.one())
    assert isinstance(outcome, RenderRefused)
    assert "structural_heads" in outcome.missing


def test_rendering_checks_ownership(runtime):
    other = UnivariatePolynomialRing(runtime.variable, RationalField())
    view = view_of(runtime, T.number(1))
    with pytest.raises(ValueError):
        runtime.bridge.render(view, other.one())


def test_rational_literals_need_a_rational_embedding(runtime):
    integers = IntegerRing()
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Z"), integers)
    integer_ring = PolynomialRing((runtime.variable,), integers)
    parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=ParentSpec("Z"),
            generators=(runtime.variable,),
            options=(("monomial_order", "lex"),),
        ),
        integer_ring,
    )
    integer_bridge = SimplePolynomialBridge(
        integer_ring,
        parent,
        runtime.world.id,
        runtime.signature,
        runtime.table.name_of,
        T.number,
    )
    request = AlgebraRequest(
        coefficient=coefficient,
        coefficient_domain=ValueDomain.INTEGER,
        parameter_ring=None,
        roles=VariableRoles(
            runtime.variable,
            (),
            ParameterMode.SPECIFIED_VALUES,
            runtime.world.id,
            S.REAL,
        ),
        interpretation=Interpretation.FORMAL,
    )
    refused = admitted(
        runtime,
        T.number(Fraction(1, 2)),
        bridge=integer_bridge,
        request=request,
    )
    assert isinstance(refused, ViewRefused)
    assert "rational_embedding" in refused.missing
    for term in (T.number(2), x_term(runtime)):
        assert isinstance(
            admitted(runtime, term, bridge=integer_bridge, request=request),
            ViewBuilt,
        )


def test_zero_powers_require_a_globally_nonzero_constant(runtime):
    x = x_term(runtime)
    cancelled = plus(runtime, x, times(runtime, T.number(-1), x))
    for base in (T.number(0), x, cancelled):
        source = power(runtime, base, T.number(0))
        outcome = admitted(runtime, source)
        assert isinstance(outcome, ViewRefused), outcome
        assert "defined_zero_power" in outcome.missing
    for base in (T.number(2), plus(runtime, cancelled, T.number(2))):
        assert runtime.ring.is_one(bridge(runtime, power(runtime, base, T.number(0))))
    assert runtime.ring.is_one(runtime.ring.pow(runtime.ring.zero(), 0))


def test_an_undefined_factor_cannot_disappear_during_projection(runtime):
    undefined = power(runtime, T.number(0), T.number(0))
    for source in (
        times(runtime, T.number(0), undefined),
        plus(runtime, undefined, times(runtime, T.number(-1), undefined)),
    ):
        outcome = admitted(runtime, source)
        assert isinstance(outcome, ViewRefused), outcome
        assert "defined_zero_power" in outcome.missing
