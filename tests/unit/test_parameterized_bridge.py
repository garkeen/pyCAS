"""The parameter/coefficient bridge for K[parameters][target]."""

from fractions import Fraction

import pytest
from support import admitted, head_app, render_value, variable, view_of

from cas.language import typing as Ty
from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap_parameterized
from cas.semantics.bridge import (
    ConversionKind,
    ConversionWitness,
    ParameterPolynomialBridge,
    ViewRefused,
)
from cas.semantics.request import Interpretation
from cas.syntax import term as T


def setup():
    runtime = bootstrap_parameterized()
    bridge = runtime.bridge
    assert isinstance(bridge, ParameterPolynomialBridge)
    parameter = T.symbol(runtime.request.parameters[0], "a")
    return runtime, bridge, parameter, variable(runtime)


def applied(runtime, head, *arguments):
    return head_app(runtime.signature, head, *arguments)


def test_parameter_symbols_are_coefficients_and_x_is_the_generator():
    runtime, bridge, parameter, x = setup()
    parameter_view = view_of(runtime, parameter)
    value = parameter_view.value
    assert parameter_view.interpretation is Interpretation.PARAMETER_FAMILY
    assert (
        parameter_view.conversion
        is ConversionKind.REPRESENTATION_ISOMORPHISM
    )
    assert parameter_view.witness == ConversionWitness.representation_isomorphism()
    expected = runtime.ring.constant(bridge.coefficient_ring.generator(0))
    assert runtime.ring.equal(value, expected)

    value_x = view_of(runtime, x).value
    assert runtime.ring.equal(value_x, runtime.ring.generator(0))


def test_products_and_powers_use_parameter_coefficients():
    runtime, bridge, parameter, x = setup()
    term = applied(
        runtime,
        StructuralHead.TIMES,
        parameter,
        applied(runtime, StructuralHead.POWER, x, T.number(2)),
    )
    value = view_of(runtime, term).value
    coefficient = runtime.ring.coefficient(value, (2,))
    assert bridge.coefficient_ring.equal(
        coefficient, bridge.coefficient_ring.generator(0)
    )


def test_expansion_keeps_coefficients_in_the_parameter_ring():
    runtime, bridge, parameter, x = setup()
    source = applied(
        runtime,
        StructuralHead.POWER,
        applied(
            runtime,
            StructuralHead.PLUS,
            applied(
                runtime,
                StructuralHead.TIMES,
                parameter,
                x,
            ),
            T.number(1),
        ),
        T.number(2),
    )
    value = view_of(runtime, source).value
    coefficients = bridge.coefficient_ring
    assert coefficients.equal(
        runtime.ring.coefficient(value, (2,)),
        coefficients.pow(coefficients.generator(0), 2),
    )
    assert coefficients.equal(
        runtime.ring.coefficient(value, (1,)),
        coefficients.mul_int(coefficients.generator(0), 2),
    )
    assert coefficients.equal(
        runtime.ring.coefficient(value, (0,)), coefficients.one()
    )


def test_rational_literals_are_embedded_exactly():
    runtime, bridge, _, _ = setup()
    value = view_of(runtime, T.number(Fraction(1, 2))).value
    expected = runtime.ring.constant(
        bridge.coefficient_ring.constant(Fraction(1, 2))
    )
    assert runtime.ring.equal(value, expected)


def test_outside_the_fragment_the_bridge_is_refused():
    runtime, _, parameter, _ = setup()
    unknown = T.symbol(runtime.table.intern("b"), "b")
    function = T.app(T.symbol(runtime.table.intern("Sin"), "Sin"), parameter)
    refused = [
        (
            applied(
                runtime,
                StructuralHead.POWER,
                parameter,
                T.number(-1),
            ),
            "nonnegative_power",
        ),
        (T.TRUE, "scalar_source"),
        (T.quote(parameter), "scalar_source"),
    ]
    for term, missing in refused:
        outcome = admitted(runtime, term)
        assert isinstance(outcome, ViewRefused), outcome
        assert missing in outcome.missing
    ill_typed = [unknown, function, T.BoundVar(0)]
    for term in ill_typed:
        outcome = admitted(runtime, term)
        assert isinstance(outcome, Ty.TypedExprFailure), outcome


def test_terms_round_trip_through_the_parameter_ring():
    runtime, bridge, parameter, x = setup()
    term = applied(
        runtime,
        StructuralHead.PLUS,
        applied(
            runtime,
            StructuralHead.TIMES,
            parameter,
            applied(runtime, StructuralHead.POWER, x, T.number(2)),
        ),
        applied(runtime, StructuralHead.TIMES, T.number(2), x),
        T.number(3),
    )
    value = view_of(runtime, term).value
    rendered = render_value(runtime, value)
    rebuilt = view_of(runtime, rendered).value
    assert runtime.ring.equal(rebuilt, value)


def test_the_bridge_refuses_role_collisions_and_bad_indices():
    runtime, bridge, _, _ = setup()
    with pytest.raises(ValueError):
        ParameterPolynomialBridge(
            runtime.ring,
            bridge.target_parent,
            bridge.coefficient_ring,
            bridge.coefficient_parent,
            runtime.world.id,
            {runtime.variable: 0},
            runtime.signature,
            runtime.table.name_of,
            bridge.embed_rational,
            T.number,
        )
    with pytest.raises(ValueError):
        ParameterPolynomialBridge(
            runtime.ring,
            bridge.target_parent,
            bridge.coefficient_ring,
            bridge.coefficient_parent,
            runtime.world.id,
            {runtime.request.parameters[0]: 99},
            runtime.signature,
            runtime.table.name_of,
            bridge.embed_rational,
            T.number,
        )


def test_roles_are_separate():
    runtime, _, _, _ = setup()
    assert runtime.ring.generators == (runtime.variable,)
    assert runtime.variable not in runtime.request.parameters
    assert set(runtime.request.parameters).isdisjoint(runtime.ring.generators)
    assert runtime.request.parameter_ring is not None


def test_multiple_parameters_keep_distinct_coefficient_generators():
    runtime = bootstrap_parameterized(("a", "b"))
    bridge = runtime.bridge
    assert isinstance(bridge, ParameterPolynomialBridge)
    second = T.symbol(runtime.request.parameters[1], "b")
    value = view_of(runtime, second).value
    expected = runtime.ring.constant(bridge.coefficient_ring.generator(1))
    assert runtime.ring.equal(value, expected)


def test_zero_power_does_not_confuse_formal_nonzero_with_all_parameter_values():
    runtime, _, parameter, x = setup()
    for base in (parameter, x, T.number(0)):
        source = applied(runtime, StructuralHead.POWER, base, T.number(0))
        outcome = admitted(runtime, source)
        assert isinstance(outcome, ViewRefused), outcome
        assert "defined_zero_power" in outcome.missing
    cancelled = applied(
        runtime, StructuralHead.PLUS, parameter,
        applied(runtime, StructuralHead.TIMES, T.number(-1), parameter),
        T.number(3),
    )
    value = view_of(
        runtime,
        applied(runtime, StructuralHead.POWER, cancelled, T.number(0)),
    ).value
    assert runtime.ring.is_one(value)
