"""Term/algebra bridge: explicit fragments, regions and refusals."""

from dataclasses import replace
from fractions import Fraction

import pytest
from support import (
    InconsistentSortEnvironment,
    admitted,
    head_app,
    multivariate_setup,
    render_value,
    structural,
    typed_in,
    view_of,
)

from cas.algebra.integers import IntegerRing
from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import (
    MonomialOrder,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import FrameId
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.meaning import MeaningKey
from cas.language.problems import (
    ParameterMode,
    Role,
    ValueDomain,
    VariableRoles,
)
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.runtime.bootstrap import (
    bootstrap,
    bootstrap_elementary,
    bootstrap_parameterized,
)
from cas.semantics.bridge import (
    AlgebraView,
    ConversionWitness,
    RationalFunctionBridge,
    Rendered,
    RenderRefused,
    SimplePolynomialBridge,
    SymbolBinding,
    ViewBuilt,
    ViewRefused,
    _issue_view,
    typed_view,
)
from cas.semantics.frames import Declaration, FrameSorts
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
    w = T.symbol(runtime.table.intern("w"), "w")
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
        w,
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
    w = T.symbol(runtime.table.intern("w"), "w")
    assert isinstance(
        admitted(runtime, w, bridge=bridge_value), Ty.TypedExprFailure
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


def _multivariate_symbol(runtime, setup, index: int) -> T.SymbolRef:
    symbol = setup.symbols[index]
    return T.symbol(symbol, runtime.table.name_of(symbol))


def _multi_admitted(runtime, setup, term, *, request=None):
    return admitted(
        runtime,
        term,
        frame=setup.frame,
        bridge=setup.bridge,
        request=setup.request if request is None else request,
    )


def _multi_view(runtime, setup, term):
    outcome = _multi_admitted(runtime, setup, term)
    assert isinstance(outcome, ViewBuilt), outcome
    return outcome.view


def test_the_multivariate_bridge_maps_the_generators_in_ring_order(runtime):
    setup = multivariate_setup(runtime)
    x = _multivariate_symbol(runtime, setup, 0)
    y = _multivariate_symbol(runtime, setup, 1)
    view = _multi_view(
        runtime, setup, plus(runtime, times(runtime, x, y), T.number(2))
    )
    assert setup.ring.equal(
        view.value,
        setup.ring.add(
            setup.ring.monomial((1, 1), Fraction(1)),
            setup.ring.constant(Fraction(2)),
        ),
    )
    assert view.generators_for(Role.GENERATOR) == setup.symbols
    assert view.symbol_for(Role.TARGET, 0) is None
    assert view.interpretation is Interpretation.FORMAL
    assert view.witness == ConversionWitness.representation_isomorphism()
    assert view.source_domain is None
    assert view.valid_on is None


def test_the_multivariate_bridge_round_trips_sums_products_and_powers(
    runtime,
):
    setup = multivariate_setup(runtime)
    x = _multivariate_symbol(runtime, setup, 0)
    y = _multivariate_symbol(runtime, setup, 1)
    term = plus(
        runtime,
        power(runtime, x, T.number(2)),
        times(runtime, T.number(3), x, y),
        power(runtime, y, T.number(3)),
    )
    view = _multi_view(runtime, setup, term)
    rendered = setup.bridge.render(view, view.value)
    assert isinstance(rendered, Rendered)
    round_trip = _multi_view(runtime, setup, rendered.term)
    assert setup.ring.equal(round_trip.value, view.value)


def test_the_multivariate_bridge_renders_through_its_generator_bindings(
    runtime,
):
    setup = multivariate_setup(runtime)
    x = _multivariate_symbol(runtime, setup, 0)
    y = _multivariate_symbol(runtime, setup, 1)
    view = _multi_view(runtime, setup, plus(runtime, x, y))
    product = setup.ring.mul(
        setup.ring.generator(0), setup.ring.generator(1)
    )
    assert setup.bridge.render(view, product) == Rendered(
        times(runtime, x, y)
    )
    assert setup.bridge.render(view, setup.ring.zero()) == Rendered(
        T.number(0)
    )


def test_multivariate_rendering_requires_generator_bindings(runtime):
    setup = multivariate_setup(runtime)
    x = _multivariate_symbol(runtime, setup, 0)
    typed = Ty.typed(
        x,
        runtime.signature,
        FrameSorts(runtime.frames, setup.frame),
        runtime.frame.meaning,
    )
    assert isinstance(typed, Ty.TypedExpr)
    view = _issue_view(
        typed,
        setup.parent,
        setup.ring.generator(0),
        (SymbolBinding(setup.symbols[0], Role.TARGET, 0),),
        Interpretation.FORMAL,
        ConversionWitness.representation_isomorphism(),
        None,
        None,
        signature=runtime.signature,
    )
    assert isinstance(view, AlgebraView)
    with pytest.raises(ValueError, match="generators"):
        setup.bridge.render(view, setup.ring.one())


def test_the_multivariate_bridge_refuses_a_target_request(runtime):
    setup = multivariate_setup(runtime)
    outcome = _multi_admitted(
        runtime, setup, T.number(1), request=runtime.request
    )
    assert isinstance(outcome, ViewRefused)
    assert "target_role" in outcome.missing


def test_a_target_polynomial_bridge_refuses_a_generator_request(runtime):
    setup = multivariate_setup(runtime)
    typed = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        x_term(runtime),
    )
    outcome = runtime.bridge.to_view(typed, setup.request)
    assert isinstance(outcome, ViewRefused)
    assert "target_role" in outcome.missing


def test_a_rational_bridge_refuses_a_generator_request(runtime):
    setup = multivariate_setup(runtime)
    typed = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        x_term(runtime),
    )
    outcome = rational_bridge(runtime).to_view(typed, setup.request)
    assert isinstance(outcome, ViewRefused)
    assert "target_role" in outcome.missing


def test_a_parameter_bridge_refuses_a_generator_request():
    runtime = bootstrap_parameterized()
    setup = multivariate_setup(runtime)
    typed = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        T.symbol(runtime.variable, "x"),
    )
    outcome = runtime.bridge.to_view(typed, setup.request)
    assert isinstance(outcome, ViewRefused)
    assert "target_role" in outcome.missing


def test_the_multivariate_bridge_refuses_a_parameter_request(runtime):
    setup = multivariate_setup(runtime)
    parameter = runtime.table.intern("p")
    parameter_ring = PolynomialRing((parameter,), runtime.ring.coefficients)
    registry = ParentRegistry()
    parameter_parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=runtime.request.coefficient.spec,
            generators=(parameter,),
            options=(("monomial_order", MonomialOrder.LEX.value),),
        ),
        parameter_ring,
    )
    request = AlgebraRequest(
        runtime.request.coefficient,
        ValueDomain.RATIONAL,
        parameter_parent,
        VariableRoles(
            runtime.variable,
            (parameter,),
            ParameterMode.GENERIC_PARAMETERS,
            runtime.world.id,
            S.REAL,
            (S.REAL,),
        ),
        Interpretation.PARAMETER_FAMILY,
    )
    assert request.roles.parameters == (parameter,)
    outcome = _multi_admitted(runtime, setup, T.number(1), request=request)
    assert isinstance(outcome, ViewRefused)
    assert "target_role" in outcome.missing


def test_the_multivariate_bridge_refuses_another_generator_order(runtime):
    setup = multivariate_setup(runtime)
    roles = replace(
        setup.request.roles,
        variables=tuple(reversed(setup.symbols)),
        variable_sorts=(S.REAL, S.REAL),
    )
    request = replace(setup.request, roles=roles)
    outcome = _multi_admitted(runtime, setup, T.number(1), request=request)
    assert isinstance(outcome, ViewRefused)
    assert "generator_roles" in outcome.missing


def test_the_multivariate_bridge_refuses_a_variable_sort_mismatch(runtime):
    setup = multivariate_setup(
        runtime, request_sorts=(S.RATIONAL, S.RATIONAL)
    )
    x = _multivariate_symbol(runtime, setup, 0)
    outcome = _multi_admitted(runtime, setup, x)
    assert isinstance(outcome, ViewRefused)
    assert "variable_sort" in outcome.missing


def test_the_multivariate_bridge_refuses_an_unbound_symbol(runtime):
    setup = multivariate_setup(runtime)
    extra = runtime.table.intern("z")
    child = runtime.frames.create(
        setup.frame,
        declarations=(Declaration(extra, "z", S.REAL),),
    )
    outcome = admitted(
        runtime,
        T.symbol(extra, "z"),
        frame=child.id,
        bridge=setup.bridge,
        request=setup.request,
    )
    assert isinstance(outcome, ViewRefused)
    assert "symbol_mapping" in outcome.missing


def test_the_multivariate_bridge_refuses_a_foreign_world_source(runtime):
    setup = multivariate_setup(runtime)
    foreign = bootstrap()
    typed = Ty.typed(
        T.symbol(foreign.variable, "x"),
        runtime.signature,
        FrameSorts(foreign.frames, foreign.frame.id),
        foreign.frame.meaning,
    )
    assert isinstance(typed, Ty.TypedExpr)
    outcome = setup.bridge.to_view(typed, setup.request)
    assert isinstance(outcome, ViewRefused)
    assert "world_identity" in outcome.missing


def test_the_multivariate_bridge_refuses_a_non_scalar_free_symbol(runtime):
    setup = multivariate_setup(runtime)
    extra = runtime.table.intern("multi_function")
    environment = InconsistentSortEnvironment(
        extra, S.REAL, S.FunctionSort((S.REAL,), S.REAL)
    )
    typed = Ty.typed(
        T.symbol(extra, "multi_function"),
        runtime.signature,
        environment,
        runtime.frame.meaning,
    )
    assert isinstance(typed, Ty.TypedExpr)
    outcome = setup.bridge.to_view(typed, setup.request)
    assert isinstance(outcome, ViewRefused)
    assert "scalar_symbol" in outcome.missing


def test_the_multivariate_bridge_refuses_outside_its_fragment():
    runtime = bootstrap_elementary()
    setup = multivariate_setup(runtime)
    x = _multivariate_symbol(runtime, setup, 0)
    sine = T.app(T.symbol(runtime.table.intern("sin"), "sin"), x)
    for term, missing in (
        (power(runtime, x, T.number(-1)), "nonnegative_power"),
        (sine, "polynomial_representation"),
        (power(runtime, x, T.number(0)), "defined_zero_power"),
        (T.TRUE, "scalar_source"),
    ):
        outcome = _multi_admitted(runtime, setup, term)
        assert isinstance(outcome, ViewRefused), outcome
        assert missing in outcome.missing


def test_typed_view_admits_a_multivariate_view(runtime):
    setup = multivariate_setup(runtime)
    x = _multivariate_symbol(runtime, setup, 0)
    outcome = typed_view(
        setup.bridge,
        plus(runtime, x, T.number(1)),
        runtime.frames,
        setup.frame,
        runtime.signature,
        setup.request,
    )
    assert isinstance(outcome, AlgebraView), outcome
    assert outcome.generators_for(Role.GENERATOR) == setup.symbols
    assert outcome.interpretation is Interpretation.FORMAL
