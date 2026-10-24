"""AlgebraRequest: coefficient structure, roles and request-local orthogonality."""

import pytest

from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId
from cas.language.problems import ParameterMode
from cas.semantics.request import AlgebraRequest, Interpretation, Role

X, A, B = SymbolId(1), SymbolId(2), SymbolId(3)


def family():
    registry = ParentRegistry()
    rationals = RationalField()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    parameter_ring = PolynomialRing((A, B), rationals)
    parameters = registry.intern(
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=(A, B),
        ),
        parameter_ring,
    )
    return coefficient, parameters, parameter_ring


def request(**overrides):
    coefficient, parameters, _ = family()
    values = dict(
        coefficient=coefficient,
        parameter_ring=parameters,
        parameters=(A, B),
        target=X,
        parameter_mode=ParameterMode.GENERIC_PARAMETERS,
        interpretation=Interpretation.PARAMETER_FAMILY,
    )
    values.update(overrides)
    return AlgebraRequest(**values)


def test_roles_are_local_to_the_request():
    algebra = request()
    assert algebra.role_of(X) is Role.TARGET
    assert algebra.role_of(A) is Role.PARAMETER
    assert algebra.role_of(B) is Role.PARAMETER
    assert algebra.role_of(SymbolId(10_000)) is None


def test_the_same_symbol_can_have_another_role_in_another_request():
    registry = ParentRegistry()
    rationals = RationalField()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    first_ring = PolynomialRing((A, B), rationals)
    first_parent = registry.intern(
        ParentSpec("polynomial", base=coefficient.spec, generators=(A, B)),
        first_ring,
    )
    first = AlgebraRequest(
        coefficient,
        first_parent,
        (A, B),
        X,
        ParameterMode.GENERIC_PARAMETERS,
        Interpretation.PARAMETER_FAMILY,
    )
    swapped_ring = PolynomialRing((X, B), rationals)
    swapped_parent = registry.intern(
        ParentSpec("polynomial", base=coefficient.spec, generators=(X, B)),
        swapped_ring,
    )
    second = AlgebraRequest(
        coefficient,
        swapped_parent,
        (X, B),
        A,
        ParameterMode.GENERIC_PARAMETERS,
        Interpretation.PARAMETER_FAMILY,
    )
    assert first.role_of(A) is Role.PARAMETER
    assert second.role_of(A) is Role.TARGET
    assert second.role_of(X) is Role.PARAMETER
    assert registry.count == 3


def test_the_target_cannot_be_a_parameter():
    with pytest.raises(ValueError):
        request(target=A)


def test_parameters_must_be_distinct():
    with pytest.raises(ValueError):
        request(parameters=(A, A))


def test_a_parameter_ring_and_parameters_are_required_together():
    with pytest.raises(ValueError):
        request(parameter_ring=None)
    coefficient, parameters, _ = family()
    with pytest.raises(ValueError):
        request(parameters=(), parameter_mode=ParameterMode.SPECIFIED_VALUES)


def test_the_parameter_ring_generators_must_be_the_declared_parameters():
    with pytest.raises(ValueError):
        request(parameters=(A,))


def test_the_parameter_ring_must_extend_the_coefficient_parent():
    registry = ParentRegistry()
    rationals = RationalField()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    parameter_ring = PolynomialRing((A, B), rationals)
    unrelated = registry.intern(
        ParentSpec("polynomial", base=ParentSpec("Z"), generators=(A, B)),
        parameter_ring,
    )
    with pytest.raises(ValueError):
        AlgebraRequest(
            coefficient,
            unrelated,
            (A, B),
            X,
            ParameterMode.GENERIC_PARAMETERS,
            Interpretation.PARAMETER_FAMILY,
        )


def test_generic_modes_need_parameters():
    coefficient, _, _ = family()
    with pytest.raises(ValueError):
        AlgebraRequest(
            coefficient,
            None,
            (),
            X,
            ParameterMode.GENERIC_PARAMETERS,
            Interpretation.FORMAL,
        )


def test_a_simple_request_has_no_parameter_ring():
    coefficient, _, _ = family()
    simple = AlgebraRequest(
        coefficient,
        None,
        (),
        X,
        ParameterMode.SPECIFIED_VALUES,
        Interpretation.FORMAL,
    )
    assert simple.role_of(X) is Role.TARGET
    assert simple.parameter_ring is None


def test_a_non_polynomial_parameter_ring_with_generators_is_accepted():
    registry = ParentRegistry()
    rationals = RationalField()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    polynomials = UnivariatePolynomialRing(A, rationals)
    parameter_ring = registry.intern(
        ParentSpec(
            "rational_function",
            base=coefficient.spec,
            generators=(A,),
        ),
        RationalFunctionField(polynomials),
    )
    algebra = AlgebraRequest(
        coefficient,
        parameter_ring,
        (A,),
        X,
        ParameterMode.ALL_PARAMETER_VALUES,
        Interpretation.PARAMETER_FAMILY,
    )
    assert algebra.parameter_ring is parameter_ring
    assert algebra.role_of(A) is Role.PARAMETER


def test_a_parameter_ring_without_generators_is_rejected():
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Q"), RationalField())
    with pytest.raises(ValueError):
        AlgebraRequest(
            coefficient,
            coefficient,
            (A,),
            X,
            ParameterMode.ALL_PARAMETER_VALUES,
            Interpretation.PARAMETER_FAMILY,
        )
