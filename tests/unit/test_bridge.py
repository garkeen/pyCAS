"""Term/polynomial bridge: an explicit fragment and an explicit refusal."""

from fractions import Fraction

import pytest
from support import head_app, structural

from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics.bridge import to_polynomial, to_term
from cas.syntax import term as T


def x_term(runtime) -> T.SymbolRef:
    return T.symbol(runtime.variable, "x")


def bridge(runtime, term: T.Term):
    value = to_polynomial(runtime.ring, term, runtime.signature)
    assert value is not None
    return value


def plus(runtime, *arguments: T.Term) -> T.Apply:
    return head_app(runtime.signature, StructuralHead.PLUS, *arguments)


def times(runtime, *arguments: T.Term) -> T.Apply:
    return head_app(runtime.signature, StructuralHead.TIMES, *arguments)


def power(runtime, base: T.Term, exponent: T.Term) -> T.Apply:
    return head_app(runtime.signature, StructuralHead.POWER, base, exponent)


def render(runtime, value):
    term = to_term(
        runtime.ring,
        value,
        runtime.signature,
        runtime.table.name_of,
        T.number,
    )
    assert term is not None
    return term


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


def test_outside_the_fragment_the_bridge_returns_none(runtime):
    x = x_term(runtime)
    y = T.symbol(runtime.table.intern("y"), "y")
    function = T.app(T.symbol(runtime.table.intern("Sin"), "Sin"), x)
    cases = [
        power(runtime, x, T.number(-1)),
        power(runtime, x, x),
        T.app(structural(runtime.signature, StructuralHead.POWER), x, T.number(2), T.number(3)),
        y,
        function,
        T.BoundVar(0),
        T.TRUE,
        T.quote(x),
    ]
    for term in cases:
        assert to_polynomial(runtime.ring, term, runtime.signature) is None


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


def test_rendering_requires_the_structural_heads(runtime):
    bare = LanguageSignature.build({})
    value = runtime.ring.one()
    assert (
        to_term(runtime.ring, value, bare, runtime.table.name_of, T.number)
        is None
    )


def test_rendering_checks_ownership(runtime):
    other = UnivariatePolynomialRing(runtime.variable, RationalField())
    with pytest.raises(ValueError):
        to_term(
            runtime.ring,
            other.one(),
            runtime.signature,
            runtime.table.name_of,
            T.number,
        )


def test_rational_literals_need_a_rational_embedding(runtime):
    integer_ring = PolynomialRing((runtime.variable,), IntegerRing())
    assert (
        to_polynomial(integer_ring, T.number(Fraction(1, 2)), runtime.signature)
        is None
    )
    assert (
        to_polynomial(integer_ring, T.number(2), runtime.signature) is not None
    )
    assert (
        to_polynomial(integer_ring, x_term(runtime), runtime.signature)
        is not None
    )
