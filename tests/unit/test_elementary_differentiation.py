"""Candidate generation for the elementary fragment."""

from fractions import Fraction

from support import head_app

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.elementary import (
    ElementaryDifferentiator,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
)
from cas.math.elementary.declarations import (
    LawOrigin,
    build_elementary,
    default_elementary_source,
    load_elementary,
)
from cas.semantics.services import DerivationUnsupported, Derived
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


def setup(text=None, origin=LawOrigin.BASIS):
    source = (
        default_elementary_source()
        if text is None
        else load_elementary(text, origin=origin)
    )
    table = SymbolTable()
    predicate = table.intern("HasDerivative")
    vocabulary = DerivativeVocabulary(predicate, "HasDerivative")
    library = build_elementary(
        table.intern, source, reserved=frozenset({"x", "HasDerivative"})
    )
    signature = standard_language(
        table,
        operators={predicate: vocabulary.signature, **library.operators},
    )
    variable = table.intern("x")
    return (
        table,
        library,
        signature,
        variable,
        ElementaryDifferentiator(
            library, signature, variable, table.name_of
        ),
    )


def call(table, signature, name, *arguments):
    identifier = table.lookup(name)
    assert identifier is not None
    return T.app(T.symbol(identifier, name), *arguments)


def power(signature, base, exponent):
    return head_app(
        signature, StructuralHead.POWER, base, T.number(exponent)
    )


def plus(signature, *terms):
    return head_app(signature, StructuralHead.PLUS, *terms)


def times(signature, *factors):
    return head_app(signature, StructuralHead.TIMES, *factors)


def test_literals_constants_and_the_variable():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    pi = T.symbol(table.lookup("pi"), "pi")
    e = T.symbol(table.lookup("e"), "e")
    for term in (T.number(0), T.number(7), T.number(Fraction(1, 2)), pi, e):
        outcome = deriver.derive(term)
        assert isinstance(outcome, Derived)
        assert outcome.term == T.number(0)
    outcome = deriver.derive(x)
    assert isinstance(outcome, Derived)
    assert outcome.term == T.number(1)


def test_polynomial_derivatives_are_canonical():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    assert isinstance(deriver.derive(power(signature, x, 2)), Derived)
    assert deriver.derive(power(signature, x, 2)).term == times(
        signature, T.number(2), x
    )
    source = times(signature, T.number(3), power(signature, x, 2))
    assert deriver.derive(source).term == times(
        signature, T.number(6), x
    )
    source = plus(
        signature,
        power(signature, x, 3),
        times(signature, T.number(-1), times(signature, T.number(3), x)),
    )
    expected = plus(
        signature,
        T.number(-3),
        times(signature, T.number(3), power(signature, x, 2)),
    )
    assert deriver.derive(source).term == expected


def test_declared_function_laws_and_the_chain_rule():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    sin_x = call(table, signature, "sin", x)
    cos_x = call(table, signature, "cos", x)
    exp_x = call(table, signature, "exp", x)

    assert deriver.derive(sin_x).term == cos_x
    assert deriver.derive(cos_x).term == times(
        signature, T.number(-1), sin_x
    )
    assert deriver.derive(exp_x).term == exp_x

    sin_square = call(table, signature, "sin", power(signature, x, 2))
    assert deriver.derive(sin_square).term == times(
        signature,
        T.number(2),
        call(table, signature, "cos", power(signature, x, 2)),
        x,
    )

    exp_double = call(
        table, signature, "exp", times(signature, T.number(2), x)
    )
    assert deriver.derive(exp_double).term == times(
        signature, T.number(2), exp_double
    )


def test_product_rule_keeps_declared_terms():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    sin_x = call(table, signature, "sin", x)
    cos_x = call(table, signature, "cos", x)
    source = times(signature, x, sin_x)
    expected = plus(signature, sin_x, times(signature, x, cos_x))
    assert deriver.derive(source).term == expected


def test_a_constant_argument_collapses_to_zero():
    table, _, signature, variable, deriver = setup()
    pi = T.symbol(table.lookup("pi"), "pi")
    assert deriver.derive(call(table, signature, "sin", pi)).term == T.number(0)


def test_conditional_laws_carry_a_restricted_region():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")

    square = deriver.derive(call(table, signature, "sqrt", x))
    assert isinstance(square, Derived)
    assert square.term == times(
        signature,
        T.number(Fraction(1, 2)),
        power(signature, call(table, signature, "sqrt", x), -1),
    )
    domain = head_app(signature, StructuralHead.GE, x, T.number(0))
    interior = head_app(signature, StructuralHead.GT, x, T.number(0))
    assert square.condition == interior
    assert square.defined == domain

    logarithm = deriver.derive(call(table, signature, "log", x))
    assert isinstance(logarithm, Derived)
    assert logarithm.term == power(signature, x, -1)
    assert logarithm.condition == interior
    assert logarithm.defined == interior


def test_a_zero_power_uses_definedness_only():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    powered = power(signature, call(table, signature, "sqrt", x), 0)
    outcome = deriver.derive(powered)
    assert isinstance(outcome, Derived)
    assert outcome.term == T.number(0)
    assert outcome.condition == head_app(
        signature, StructuralHead.GE, x, T.number(0)
    )
    assert outcome.defined == outcome.condition


def test_ground_conditions_collapse_or_refuse():
    table, _, signature, variable, deriver = setup()
    square_one = call(table, signature, "sqrt", T.number(1))
    outcome = deriver.derive(square_one)
    assert isinstance(outcome, Derived)
    assert outcome.term == T.number(0)
    assert outcome.condition is None

    log_one = call(table, signature, "log", T.number(1))
    outcome = deriver.derive(log_one)
    assert isinstance(outcome, Derived)
    assert outcome.term == T.number(0)
    assert outcome.condition is None

    for term in (
        call(table, signature, "sqrt", T.number(-1)),
        call(table, signature, "log", T.number(0)),
    ):
        outcome = deriver.derive(term)
        assert isinstance(outcome, DerivationUnsupported)
        assert outcome.reason is Reason.GUARDED


def test_conditions_are_composed_through_the_chain_rule():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    inner = call(table, signature, "sin", x)
    outcome = deriver.derive(call(table, signature, "log", inner))
    assert isinstance(outcome, Derived)
    expected = head_app(signature, StructuralHead.GT, inner, T.number(0))
    assert outcome.condition == expected
    assert outcome.defined == expected


def test_an_empty_symbolic_domain_or_condition_is_refused():
    domain_text = (
        "function F : Real -> Real on u > 0 and u < 0\n"
        "derivative F(u) = 1\n"
    )
    table, _, signature, variable, deriver = setup(domain_text)
    x = T.symbol(variable, "x")
    outcome = deriver.derive(call(table, signature, "F", x))
    assert isinstance(outcome, DerivationUnsupported)
    assert outcome.reason is Reason.GUARDED

    law_text = (
        "function F : Real -> Real\n"
        "derivative F(u) = 1 on u > 0 and u < 0\n"
    )
    table, _, signature, variable, deriver = setup(law_text)
    x = T.symbol(variable, "x")
    outcome = deriver.derive(call(table, signature, "F", x))
    assert isinstance(outcome, DerivationUnsupported)
    assert outcome.reason is Reason.GUARDED


def test_negative_powers_and_undeclared_symbols_are_refused():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    outcome = deriver.derive(power(signature, x, -1))
    assert isinstance(outcome, DerivationUnsupported)
    assert outcome.reason is Reason.FRAGMENT

    y = T.symbol(table.intern("y"), "y")
    outcome = deriver.derive(y)
    assert isinstance(outcome, DerivationUnsupported)
    assert "dependency contract" in outcome.detail

    outcome = deriver.derive(call(table, signature, "sin", y))
    assert isinstance(outcome, DerivationUnsupported)
    assert "dependency contract" in outcome.detail


def test_unknown_operators_and_structural_forms_are_refused():
    table, _, signature, variable, deriver = setup()
    x = T.symbol(variable, "x")
    unknown = T.app(T.symbol(table.intern("unknown"), "unknown"), x)
    outcome = deriver.derive(unknown)
    assert isinstance(outcome, DerivationUnsupported)
    assert outcome.reason is Reason.FRAGMENT

    for term in (T.TRUE, T.BoundVar(0), T.quote(x)):
        outcome = deriver.derive(term)
        assert isinstance(outcome, DerivationUnsupported)
        assert outcome.reason is Reason.FRAGMENT


def test_a_user_axiom_law_is_not_applied():
    text = """
function F : Real -> Real
derivative F(u) = 1
"""
    table, _, signature, variable, deriver = setup(
        text, origin=LawOrigin.USER_AXIOM
    )
    x = T.symbol(variable, "x")
    outcome = deriver.derive(call(table, signature, "F", x))
    assert isinstance(outcome, DerivationUnsupported)
    assert "user axiom" in outcome.detail


def test_a_function_without_a_law_is_refused():
    text = "function F : Real -> Real\n"
    table, _, signature, variable, deriver = setup(text)
    x = T.symbol(variable, "x")
    outcome = deriver.derive(call(table, signature, "F", x))
    assert isinstance(outcome, DerivationUnsupported)
    assert "no derivative law" in outcome.detail


def test_a_function_domain_becomes_a_condition():
    text = (
        "function F : Real -> Real on u >= 0\n"
        "derivative F(u) = 1\n"
    )
    table, _, signature, variable, deriver = setup(text)
    x = T.symbol(variable, "x")
    outcome = deriver.derive(call(table, signature, "F", x))
    assert isinstance(outcome, Derived)
    assert outcome.term == T.number(1)
    expected = head_app(signature, StructuralHead.GE, x, T.number(0))
    assert outcome.condition == expected
    assert outcome.defined == expected


def test_the_same_symbol_is_not_a_target_by_accident():
    table, _, signature, variable, deriver = setup()
    pi = T.symbol(table.lookup("pi"), "pi")
    outcome = deriver.derive(T.symbol(SymbolId(10_000), "z"))
    assert isinstance(outcome, DerivationUnsupported)
    assert outcome.reason is Reason.FRAGMENT
    # pi remains a constant even when it is the only symbol in the term
    assert deriver.derive(pi).term == T.number(0)
