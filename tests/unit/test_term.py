"""Pure terms: structural identity, immutability, order and presentation."""

from fractions import Fraction

import pytest

from cas.foundation.ids import SymbolId
from cas.syntax import term as T

X = SymbolId(1)
Y = SymbolId(2)
PLUS = SymbolId(100)


def x(name: str = "x") -> T.SymbolRef:
    return T.symbol(X, name)


def test_number_returns_an_integer_literal_for_integral_values():
    assert T.number(3) == T.IntLit(3)
    integral = T.number(Fraction(4, 2))
    assert isinstance(integral, T.IntLit)
    assert integral.value == 2


def test_number_keeps_a_genuine_fraction_as_a_rational_literal():
    value = T.number(Fraction(2, 4))
    assert isinstance(value, T.RatLit)
    assert value.value == Fraction(1, 2)


def test_rational_literal_normalizes_and_refuses_integrals():
    assert T.RatLit(Fraction(2, 4)).value == Fraction(1, 2)
    with pytest.raises(ValueError):
        T.RatLit(Fraction(2, 1))


def test_boolean_constants():
    assert T.TRUE == T.BoolLit(True)
    assert T.FALSE == T.BoolLit(False)
    assert T.TRUE.value is True
    assert T.TRUE != T.FALSE


def test_symbol_identity_is_the_id_not_the_spelling():
    assert T.symbol(X, "x") == T.symbol(X, "renamed")
    assert hash(T.symbol(X, "x")) == hash(T.symbol(X, "renamed"))
    assert T.symbol(X, "x") != T.symbol(Y, "x")
    with pytest.raises(ValueError):
        T.symbol(X, "")


def test_bound_variable_rejects_a_negative_index():
    with pytest.raises(ValueError):
        T.BoundVar(-1)
    assert T.BoundVar(0) != T.BoundVar(1)


def test_independently_built_terms_are_equal_but_not_shared():
    first = T.app(T.symbol(PLUS, "Plus"), x(), T.number(1))
    second = T.app(T.symbol(PLUS, "Plus"), x(), T.number(1))
    assert first is not second
    assert first == second
    assert hash(first) == hash(second)
    assert {first: "value"}[second] == "value"


def test_application_preserves_operand_order():
    left = T.app(T.symbol(PLUS, "Plus"), x(), T.symbol(Y, "y"))
    right = T.app(T.symbol(PLUS, "Plus"), T.symbol(Y, "y"), x())
    assert left != right


def test_terms_are_immutable_after_construction():
    term = T.app(T.symbol(PLUS, "Plus"), x(), T.number(1))
    with pytest.raises(AttributeError):
        term.arguments = ()
    with pytest.raises(AttributeError):
        term.operator = x()
    with pytest.raises(AttributeError):
        del term.operator


def test_binder_hint_is_presentation_only():
    body = T.app(T.symbol(PLUS, "Plus"), T.BoundVar(0), T.number(1))
    with_hint = T.binder("Lam", 1, body, hint="u")
    without = T.binder("Lam", 1, body)
    renamed = T.binder("Lam", 1, body, hint="v")
    assert with_hint == without == renamed
    assert not with_hint < without
    assert not without < with_hint


def test_binder_structure_takes_part_in_identity():
    body = T.BoundVar(0)
    assert T.binder("Lam", 1, body) != T.binder("Mu", 1, body)
    assert T.binder("Lam", 1, body) != T.binder("Lam", 2, body)


def test_binder_validates_its_shape():
    body = T.BoundVar(0)
    with pytest.raises(ValueError):
        T.binder("", 1, body)
    with pytest.raises(ValueError):
        T.binder("Lam", 0, body)


def test_quote_wraps_held_syntax_structurally():
    held = T.app(T.symbol(PLUS, "Plus"), x(), T.number(1))
    assert T.quote(held) == T.quote(
        T.app(T.symbol(PLUS, "Plus"), x(), T.number(1))
    )
    assert T.quote(held) != held


def test_canonical_order_is_total_and_stable():
    terms = [
        T.quote(T.number(1)),
        T.binder("Lam", 1, T.BoundVar(0)),
        T.app(T.symbol(PLUS, "Plus"), x(), T.number(1)),
        T.BoundVar(0),
        x(),
        T.TRUE,
        T.number(Fraction(1, 2)),
        T.number(1),
    ]
    assert sorted(terms) == sorted(reversed(terms))
    assert len(set(terms)) == len(terms)
    for first, second in zip(sorted(terms), sorted(terms)[1:]):
        assert first < second


def test_literal_renderings_are_plain():
    assert repr(T.number(3)) == "3"
    assert repr(T.number(Fraction(1, 2))) == "1/2"
    assert repr(T.TRUE) == "true"
    assert repr(T.symbol(X, "x")) == "x"
    assert repr(T.BoundVar(2)) == "#2"
    assert repr(T.app(T.symbol(PLUS, "Plus"), T.number(1))) == "Plus(1)"
