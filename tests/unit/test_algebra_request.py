"""AlgebraRequest: coefficient structure, roles and request-local orthogonality."""

import pytest

from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import (
    MonomialOrder,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId, WorldId
from cas.language import sorts as S
from cas.language.problems import (
    InterpretationRequirement,
    ParameterMode,
    Role,
    ValueDomain,
    VariableRoles,
    value_domain_of_sort,
)
from cas.semantics.differential import polynomial_structure
from cas.semantics.request import AlgebraRequest, Interpretation

X, A, B = SymbolId(1), SymbolId(2), SymbolId(3)
WORLD = WorldId(0)


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
            options=(("monomial_order", MonomialOrder.LEX.value),),
        ),
        parameter_ring,
    )
    return coefficient, parameters, parameter_ring


def differential():
    coefficient, _, _ = family()
    ring = UnivariatePolynomialRing(X, RationalField())
    registry = ParentRegistry()
    parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=(X,),
            options=(("monomial_order", MonomialOrder.LEX.value),),
        ),
        ring,
    )
    return coefficient, polynomial_structure(parent, 0)


def request(**overrides):
    coefficient, parameters, _ = family()
    target = overrides.pop("target", X)
    declared = overrides.pop("parameters", (A, B))
    mode = overrides.pop(
        "parameter_mode", ParameterMode.GENERIC_PARAMETERS
    )
    values = dict(
        coefficient=coefficient,
        coefficient_domain=ValueDomain.RATIONAL,
        parameter_ring=parameters,
        roles=VariableRoles(
            target,
            declared,
            mode,
            WORLD,
            S.REAL,
            tuple(S.REAL for _ in declared),
        ),
        interpretation=Interpretation.PARAMETER_FAMILY,
    )
    values.update(overrides)
    return AlgebraRequest(**values)


def test_an_algebra_request_validates_its_field_kinds():
    coefficient, _, _ = family()
    with pytest.raises(TypeError):
        AlgebraRequest(
            object(),  # type: ignore[arg-type]
            ValueDomain.RATIONAL,
            None,
            VariableRoles(X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL),
            Interpretation.FORMAL,
        )
    with pytest.raises(TypeError):
        AlgebraRequest(
            coefficient,
        ValueDomain.RATIONAL,
            ValueDomain.RATIONAL,
            None,
            VariableRoles(
                X,
                (),
                "specified_values",  # type: ignore[arg-type]
                WORLD,
                S.REAL,
            ),
            Interpretation.FORMAL,
        )
    with pytest.raises(TypeError):
        AlgebraRequest(
            coefficient,
        ValueDomain.RATIONAL,
            ValueDomain.RATIONAL,
            None,
            VariableRoles(X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL),
            "formal",  # type: ignore[arg-type]
        )


def test_an_algebra_request_needs_a_world_scoped_role_set():
    coefficient, _, _ = family()
    with pytest.raises(ValueError, match="world"):
        AlgebraRequest(
            coefficient,
            ValueDomain.RATIONAL,
            None,
            VariableRoles(
                X,
                (),
                ParameterMode.SPECIFIED_VALUES,
                None,
                S.REAL,
            ),
            Interpretation.FORMAL,
        )


def test_variable_roles_validate_their_world():
    with pytest.raises(TypeError):
        VariableRoles(
            X,
            (),
            ParameterMode.SPECIFIED_VALUES,
            "world",  # type: ignore[arg-type]
            S.REAL,
        )
    with pytest.raises(TypeError):
        VariableRoles(
            X, (), ParameterMode.SPECIFIED_VALUES, True, S.REAL
        )
    assert VariableRoles(
        X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL
    ).world == WORLD


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
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=(A, B),
            options=(("monomial_order", MonomialOrder.LEX.value),),
        ),
        first_ring,
    )
    first = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        first_parent,
        VariableRoles(X, (A, B), ParameterMode.GENERIC_PARAMETERS, WORLD, S.REAL, (S.REAL, S.REAL)),
        Interpretation.PARAMETER_FAMILY,
    )
    swapped_ring = PolynomialRing((X, B), rationals)
    swapped_parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=(X, B),
            options=(("monomial_order", MonomialOrder.LEX.value),),
        ),
        swapped_ring,
    )
    second = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        swapped_parent,
        VariableRoles(A, (X, B), ParameterMode.GENERIC_PARAMETERS, WORLD, S.REAL, (S.REAL, S.REAL)),
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
        ParentSpec(
            "polynomial",
            base=ParentSpec("Z"),
            generators=(A, B),
            options=(("monomial_order", MonomialOrder.LEX.value),),
        ),
        parameter_ring,
    )
    with pytest.raises(ValueError):
        AlgebraRequest(
            coefficient,
            ValueDomain.RATIONAL,
            unrelated,
            VariableRoles(X, (A, B), ParameterMode.GENERIC_PARAMETERS, WORLD, S.REAL, (S.REAL, S.REAL)),
            Interpretation.PARAMETER_FAMILY,
        )


def test_the_parameter_ring_must_use_the_same_coefficient_structure():
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Q"), RationalField())
    parameter_ring = PolynomialRing((A,), RationalField())
    parameters = registry.intern(
        ParentSpec(
            "polynomial",
            base=ParentSpec("Q"),
            generators=(A,),
            options=(("monomial_order", MonomialOrder.LEX.value),),
        ),
        parameter_ring,
    )
    with pytest.raises(ValueError, match="coefficient"):
        AlgebraRequest(
            coefficient,
            ValueDomain.RATIONAL,
            parameters,
            VariableRoles(X, (A,), ParameterMode.GENERIC_PARAMETERS, WORLD, S.REAL, (S.REAL,)),
            Interpretation.PARAMETER_FAMILY,
        )


def test_generic_modes_need_parameters():
    coefficient, _, _ = family()
    with pytest.raises(ValueError):
        AlgebraRequest(
            coefficient,
            ValueDomain.RATIONAL,
            None,
            VariableRoles(X, (), ParameterMode.GENERIC_PARAMETERS, WORLD, S.REAL),
            Interpretation.FORMAL,
        )


def test_a_simple_request_has_no_parameter_ring():
    coefficient, _, _ = family()
    simple = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        None,
        VariableRoles(X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL),
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
        ValueDomain.RATIONAL,
        parameter_ring,
        VariableRoles(X, (A,), ParameterMode.ALL_PARAMETER_VALUES, WORLD, S.REAL, (S.REAL,)),
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
            ValueDomain.RATIONAL,
            coefficient,
            VariableRoles(X, (A,), ParameterMode.ALL_PARAMETER_VALUES, WORLD, S.REAL, (S.REAL,)),
            Interpretation.PARAMETER_FAMILY,
        )


def test_an_algebra_request_accepts_a_request_local_differential():
    coefficient, structure = differential()
    algebra = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        None,
        VariableRoles(X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL),
        Interpretation.FORMAL,
        differential=structure,
    )
    assert algebra.differential is structure


def test_an_algebra_request_without_a_differential_assumes_no_derivation():
    coefficient, _ = differential()
    roles = VariableRoles(X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL)
    implicit = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        None,
        roles,
        Interpretation.FORMAL,
    )
    explicit = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        None,
        roles,
        Interpretation.FORMAL,
        differential=None,
    )
    assert implicit.differential is None
    assert explicit.differential is None


def test_an_algebra_request_rejects_a_non_differential_payload():
    coefficient, _ = differential()
    with pytest.raises(TypeError, match="differential"):
        AlgebraRequest(
            coefficient,
            ValueDomain.RATIONAL,
            None,
            VariableRoles(
                X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL
            ),
            Interpretation.FORMAL,
            differential="not a differential",
        )


def test_role_sorts_are_required_exactly_with_the_roles():
    with pytest.raises(ValueError, match="target sort"):
        VariableRoles(X, (), ParameterMode.SPECIFIED_VALUES, WORLD)
    with pytest.raises(ValueError, match="parameter sorts"):
        VariableRoles(
            X,
            (A,),
            ParameterMode.GENERIC_PARAMETERS,
            WORLD,
            S.REAL,
        )
    with pytest.raises(TypeError):
        VariableRoles(
            X,
            (),
            ParameterMode.SPECIFIED_VALUES,
            WORLD,
            "real",  # type: ignore[arg-type]
        )
    with pytest.raises(ValueError, match="without a target"):
        VariableRoles(
            None,
            (),
            ParameterMode.SPECIFIED_VALUES,
            WORLD,
            S.REAL,
        )
    with pytest.raises(ValueError, match="without parameters"):
        VariableRoles(
            None,
            (),
            ParameterMode.SPECIFIED_VALUES,
            WORLD,
            None,
            (S.REAL,),
        )


def test_interpretation_requirement_maps_the_request_interpretation():
    assert (
        request().interpretation_requirement
        is InterpretationRequirement.PARAMETER_FAMILY
    )
    coefficient, _, _ = family()
    formal = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        None,
        VariableRoles(
            X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL
        ),
        Interpretation.FORMAL,
    )
    assert (
        formal.interpretation_requirement
        is InterpretationRequirement.FORMAL
    )
    embedded = AlgebraRequest(
        coefficient,
        ValueDomain.RATIONAL,
        None,
        VariableRoles(
            X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL
        ),
        Interpretation.EMBEDDED,
    )
    assert (
        embedded.interpretation_requirement
        is InterpretationRequirement.EMBEDDED
    )


def test_the_value_domain_is_derived_from_the_target_sort():
    algebra = request()
    assert algebra.coefficient_domain is ValueDomain.RATIONAL
    assert algebra.value_domain is ValueDomain.REAL
    assert value_domain_of_sort(S.INTEGER) is ValueDomain.INTEGER
    assert value_domain_of_sort(S.RATIONAL) is ValueDomain.RATIONAL
    assert value_domain_of_sort(S.REAL) is ValueDomain.REAL
    assert value_domain_of_sort(S.COMPLEX) is ValueDomain.COMPLEX
    with pytest.raises(ValueError, match="no scalar value domain"):
        value_domain_of_sort(S.PROPOSITION)


def test_an_algebra_request_needs_a_value_domain_coefficient_domain():
    coefficient, _, _ = family()
    with pytest.raises(TypeError, match="coefficient domain"):
        AlgebraRequest(
            coefficient,
            "rational",  # type: ignore[arg-type]
            None,
            VariableRoles(
                X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.REAL
            ),
            Interpretation.FORMAL,
        )


def test_an_algebra_request_needs_a_scalar_target_sort():
    coefficient, _, _ = family()
    with pytest.raises(ValueError, match="no scalar value domain"):
        AlgebraRequest(
            coefficient,
            ValueDomain.RATIONAL,
            None,
            VariableRoles(
                X, (), ParameterMode.SPECIFIED_VALUES, WORLD, S.PROPOSITION
            ),
            Interpretation.FORMAL,
        )
