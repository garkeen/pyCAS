"""Parent descriptions and the registry: one stable id per structure."""

import pytest

from cas.algebra.integers import IntegerRing
from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

X = SymbolId(1)
Y = SymbolId(2)


def test_a_description_needs_a_kind():
    with pytest.raises(ValueError):
        ParentSpec("")


def test_option_order_is_canonical_and_repetition_is_refused():
    spec = ParentSpec("polynomial", options=(("order", "lex"), ("dense", "yes")))
    assert spec.options == (("dense", "yes"), ("order", "lex"))
    assert spec == ParentSpec(
        "polynomial", options=(("dense", "yes"), ("order", "lex"))
    )
    with pytest.raises(ValueError):
        ParentSpec("polynomial", options=(("order", "lex"), ("order", "grevlex")))


def test_descriptions_compare_structurally_including_the_base():
    assert ParentSpec("Q") == ParentSpec("Q")
    assert ParentSpec("Q") != ParentSpec("Z")
    assert ParentSpec("polynomial", base=ParentSpec("Q"), generators=(X,)) == (
        ParentSpec("polynomial", base=ParentSpec("Q"), generators=(X,))
    )
    assert ParentSpec("polynomial", base=ParentSpec("Q"), generators=(X,)) != (
        ParentSpec("polynomial", base=ParentSpec("Z"), generators=(X,))
    )


def test_the_registry_issues_one_parent_per_description():
    registry = ParentRegistry()
    ring = RationalField()
    first = registry.intern(ParentSpec("Q"), ring)
    second = registry.intern(ParentSpec("Q"), ring)
    assert first is second
    assert first.id == second.id
    assert registry.count == 1
    assert registry.get(first.id) is first


def test_the_same_description_cannot_be_registered_with_another_structure():
    registry = ParentRegistry()
    registry.intern(ParentSpec("Q"), RationalField())
    with pytest.raises(ValueError):
        registry.intern(ParentSpec("Q"), RationalField())


def test_different_descriptions_get_different_ids():
    registry = ParentRegistry()
    first = registry.intern(ParentSpec("Q"), RationalField())
    second = registry.intern(ParentSpec("Z"), IntegerRing())
    third = registry.intern(
        ParentSpec("polynomial", generators=(X,)),
        UnivariatePolynomialRing(X, RationalField()),
    )
    fourth = registry.intern(
        ParentSpec("polynomial", generators=(Y,)),
        UnivariatePolynomialRing(Y, RationalField()),
    )
    assert len({first.id, second.id, third.id, fourth.id}) == 4
    assert registry.count == 4


def test_capabilities_come_from_the_attached_structure():
    registry = ParentRegistry()
    q = registry.intern(ParentSpec("Q"), RationalField())
    assert q.is_field
    assert q.is_ordered
    assert not q.is_euclidean
    assert q.has_derivation
    assert q.embeds_integers

    z = registry.intern(ParentSpec("Z"), IntegerRing())
    assert not z.is_field
    assert z.is_euclidean
    assert z.is_ordered
    assert z.has_derivation
    assert z.embeds_integers

    polynomials = registry.intern(
        ParentSpec("polynomial", base=ParentSpec("Q"), generators=(X,)),
        UnivariatePolynomialRing(X, RationalField()),
    )
    assert not polynomials.is_field
    assert polynomials.is_euclidean
    assert not polynomials.is_ordered
    assert not polynomials.has_derivation
    assert not polynomials.embeds_integers


def test_membership_is_total_and_structure_specific():
    from fractions import Fraction

    q = ParentRegistry().intern(ParentSpec("Q"), RationalField())
    assert q.contains(Fraction(1, 2))
    assert not q.contains(1)
    assert not q.contains("one")

    z = ParentRegistry().intern(ParentSpec("Z"), IntegerRing())
    assert z.contains(1)
    assert not z.contains(True)
    assert not z.contains(Fraction(1, 1))

    first = UnivariatePolynomialRing(X, RationalField())
    second = UnivariatePolynomialRing(Y, RationalField())
    assert first.contains(first.zero())
    assert not first.contains(second.zero())
    assert not first.contains(Fraction(0))


def test_algebra_values_require_the_owning_parent():
    from fractions import Fraction

    from cas.algebra.parents import AlgebraValue

    q = ParentRegistry().intern(ParentSpec("Q"), RationalField())
    value = q.value(Fraction(1, 2))
    assert isinstance(value, AlgebraValue)
    assert value.parent is q
    assert value.representation == Fraction(1, 2)
    with pytest.raises(ValueError):
        q.value(1)
    with pytest.raises(ValueError):
        AlgebraValue(q, "not a rational")
