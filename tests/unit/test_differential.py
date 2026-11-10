"""Differential structures pair a parent with one explicitly chosen derivation."""

from dataclasses import replace
from fractions import Fraction

import pytest
from support import head_app, view_of

from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.view import (
    DifferentiationView,
    SpecializationView,
)
from cas.runtime.bootstrap import bootstrap_parameterized
from cas.semantics.differential import (
    DifferentialStructure,
    PolynomialDerivation,
    RationalDerivation,
    polynomial_structure,
    rational_structure,
)
from cas.syntax import term as T


def x_term(runtime) -> T.SymbolRef:
    return T.symbol(runtime.variable, "x")


def polynomial(runtime, term: T.Term):
    return view_of(runtime, term).value


def test_the_runtime_derivation_differentiates_polynomials(runtime):
    x = x_term(runtime)
    square = polynomial(
        runtime,
        head_app(
            runtime.signature, StructuralHead.POWER, x, T.number(2)
        ),
    )
    expected = runtime.ring.monomial((1,), Fraction(2))
    assert runtime.ring.equal(runtime.differential.deriv(square), expected)


def test_a_polynomial_structure_pins_one_generator(runtime):
    x = x_term(runtime)
    square = polynomial(
        runtime,
        head_app(
            runtime.signature, StructuralHead.POWER, x, T.number(2)
        ),
    )
    structure = polynomial_structure(runtime.parent, 0)
    assert runtime.ring.equal(
        structure.deriv(square), runtime.ring.monomial((1,), Fraction(2))
    )
    with pytest.raises(IndexError):
        polynomial_structure(runtime.parent, 1)


def test_a_differential_structure_cannot_be_built_by_hand(runtime):
    with pytest.raises(ValueError):
        DifferentialStructure(
            runtime.parent, runtime.differential.derivation, object()
        )


def test_a_rational_structure_derives_fractions(runtime):
    field = RationalFunctionField(runtime.ring)
    registry = ParentRegistry()
    parent = registry.intern(
        ParentSpec(
            "rational_function",
            base=runtime.parent.spec,
            generators=(runtime.variable,),
        ),
        field,
    )
    structure = rational_structure(parent)
    one_over_x = field.fraction(runtime.ring.one(), runtime.ring.generator(0))
    expected = field.fraction(
        runtime.ring.neg(runtime.ring.one()),
        runtime.ring.monomial((2,), Fraction(1)),
    )
    assert field.equal(structure.deriv(one_over_x), expected)
    assert field.equal(
        structure.deriv(field.of_polynomial(runtime.ring.generator(0))),
        field.one(),
    )


def test_structures_refuse_the_wrong_kind_of_parent(runtime):
    field = RationalFunctionField(runtime.ring)
    registry = ParentRegistry()
    rational_parent = registry.intern(
        ParentSpec(
            "rational_function",
            base=runtime.parent.spec,
            generators=(runtime.variable,),
        ),
        field,
    )
    with pytest.raises(TypeError):
        polynomial_structure(rational_parent, 0)
    with pytest.raises(TypeError):
        rational_structure(runtime.parent)


def test_a_polynomial_derivation_selects_one_generator():
    x, y = SymbolId(1), SymbolId(2)
    ring = PolynomialRing((x, y), RationalField())
    value = ring.monomial((1, 1), Fraction(1))
    assert ring.equal(
        PolynomialDerivation(ring, 1).deriv(value), ring.generator(0)
    )
    assert ring.equal(
        PolynomialDerivation(ring, 0).deriv(value), ring.generator(1)
    )
    with pytest.raises(IndexError):
        PolynomialDerivation(ring, 2)


def test_a_rational_derivation_differentiates_constants_to_zero():
    field = RationalFunctionField(
        UnivariatePolynomialRing(SymbolId(1), RationalField())
    )
    derivation = RationalDerivation(field)
    assert field.equal(derivation.deriv(field.one()), field.zero())


def test_a_differentiation_view_requires_the_request_differential(runtime):
    view = runtime.views[0]
    assert isinstance(view, DifferentiationView)
    assert view.request.differential is view.differential
    without = replace(view.request, differential=None)
    with pytest.raises(ValueError, match="request"):
        replace(view, request=without)


def test_a_differentiation_view_rejects_a_second_differential(runtime):
    view = runtime.views[0]
    other = polynomial_structure(runtime.parent, 0)
    assert other is not view.differential
    with pytest.raises(ValueError, match="single derivation authority"):
        replace(view, differential=other)


def test_a_differentiation_view_accepts_the_request_differential(runtime):
    view = runtime.views[0]
    rebuilt = replace(
        view, request=view.request, differential=view.differential
    )
    assert rebuilt.request.differential is rebuilt.differential


def test_a_specialization_view_requires_the_request_differential():
    runtime = bootstrap_parameterized()
    view = runtime.specialization
    assert isinstance(view, SpecializationView)
    assert view.request.differential is view.differential
    without = replace(view.request, differential=None)
    with pytest.raises(ValueError, match="request"):
        replace(view, request=without)


def test_a_specialization_view_rejects_a_second_differential():
    runtime = bootstrap_parameterized()
    view = runtime.specialization
    assert isinstance(view, SpecializationView)
    other = polynomial_structure(view.parent, 0)
    assert other is not view.differential
    with pytest.raises(ValueError, match="single derivation authority"):
        replace(view, differential=other)


def test_a_specialization_view_accepts_the_request_differential():
    runtime = bootstrap_parameterized()
    view = runtime.specialization
    assert isinstance(view, SpecializationView)
    rebuilt = replace(view, request=view.request)
    assert rebuilt.request.differential is rebuilt.differential
