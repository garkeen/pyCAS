"""The parameter/coefficient bridge for K[parameters][target]."""

from fractions import Fraction

import pytest
from support import head_app, variable

from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap_parameterized
from cas.semantics.bridge import ParameterPolynomialBridge
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
    value = bridge.to_value(parameter)
    assert value is not None
    expected = runtime.ring.constant(bridge.coefficient_ring.generator(0))
    assert runtime.ring.equal(value, expected)

    value_x = bridge.to_value(x)
    assert value_x is not None
    assert runtime.ring.equal(value_x, runtime.ring.generator(0))


def test_products_and_powers_use_parameter_coefficients():
    runtime, bridge, parameter, x = setup()
    term = applied(
        runtime,
        StructuralHead.TIMES,
        parameter,
        applied(runtime, StructuralHead.POWER, x, T.number(2)),
    )
    value = bridge.to_value(term)
    assert value is not None
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
    value = bridge.to_value(source)
    assert value is not None
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
    value = bridge.to_value(T.number(Fraction(1, 2)))
    assert value is not None
    expected = runtime.ring.constant(
        bridge.coefficient_ring.constant(Fraction(1, 2))
    )
    assert runtime.ring.equal(value, expected)


def test_outside_the_fragment_the_bridge_returns_none():
    runtime, bridge, parameter, x = setup()
    unknown = T.symbol(runtime.table.intern("b"), "b")
    function = T.app(T.symbol(runtime.table.intern("Sin"), "Sin"), parameter)
    cases = [
        applied(
            runtime,
            StructuralHead.POWER,
            parameter,
            T.number(-1),
        ),
        unknown,
        function,
        T.BoundVar(0),
        T.TRUE,
        T.quote(parameter),
    ]
    for term in cases:
        assert bridge.to_value(term) is None


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
    value = bridge.to_value(term)
    assert value is not None
    rendered = bridge.to_term(value)
    assert rendered is not None
    rebuilt = bridge.to_value(rendered)
    assert rebuilt is not None
    assert runtime.ring.equal(rebuilt, value)


def test_the_bridge_refuses_role_collisions_and_bad_indices():
    runtime, bridge, _, _ = setup()
    with pytest.raises(ValueError):
        ParameterPolynomialBridge(
            runtime.ring,
            bridge.coefficient_ring,
            {runtime.variable: 0},
            runtime.signature,
            runtime.table.name_of,
            bridge.embed_rational,
            T.number,
        )
    with pytest.raises(ValueError):
        ParameterPolynomialBridge(
            runtime.ring,
            bridge.coefficient_ring,
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
    value = bridge.to_value(second)
    assert value is not None
    expected = runtime.ring.constant(bridge.coefficient_ring.generator(1))
    assert runtime.ring.equal(value, expected)
