"""Surface parsing: precedence, literal syntax, names and refusals."""

from fractions import Fraction

import pytest

from cas.frontend.errors import ParseError
from cas.frontend.parser import parse
from cas.language.signatures import StructuralHead
from cas.syntax import term as T


def parse_text(runtime, text: str) -> T.Term:
    return parse(text, runtime.table, runtime.signature)


def head(runtime, kind: StructuralHead) -> T.SymbolRef:
    identifier = runtime.signature.symbol_of(kind)
    assert identifier is not None
    return T.symbol(identifier, kind.value)


def applied(runtime, kind: StructuralHead, *arguments: T.Term) -> T.Apply:
    return T.app(head(runtime, kind), *arguments)


def x(runtime) -> T.SymbolRef:
    return T.symbol(runtime.variable, "x")


def named(runtime, name: str) -> T.SymbolRef:
    identifier = runtime.table.intern(name)
    return T.symbol(identifier, name)


def test_integer_and_boolean_literals(runtime):
    assert parse_text(runtime, "42") == T.number(42)
    assert parse_text(runtime, "true") == T.TRUE
    assert parse_text(runtime, "false") == T.FALSE


def test_rational_literals_are_exact(runtime):
    assert parse_text(runtime, "1/2") == T.number(Fraction(1, 2))
    assert parse_text(runtime, "-1/2") == T.number(Fraction(-1, 2))
    assert parse_text(runtime, "4/2") == T.number(2)


def test_division_is_not_folded_unless_both_sides_are_literals(runtime):
    assert parse_text(runtime, "x/2") == applied(
        runtime,
        StructuralHead.TIMES,
        x(runtime),
        applied(runtime, StructuralHead.POWER, T.number(2), T.number(-1)),
    )
    assert parse_text(runtime, "2/0") == applied(
        runtime,
        StructuralHead.TIMES,
        T.number(2),
        applied(runtime, StructuralHead.POWER, T.number(0), T.number(-1)),
    )


def test_arithmetic_precedence_and_associativity(runtime):
    assert parse_text(runtime, "1 + 2*3") == applied(
        runtime,
        StructuralHead.PLUS,
        T.number(1),
        applied(runtime, StructuralHead.TIMES, T.number(2), T.number(3)),
    )
    assert parse_text(runtime, "(1 + 2)*3") == applied(
        runtime,
        StructuralHead.TIMES,
        applied(runtime, StructuralHead.PLUS, T.number(1), T.number(2)),
        T.number(3),
    )
    assert parse_text(runtime, "2^3^2") == applied(
        runtime,
        StructuralHead.POWER,
        T.number(2),
        applied(runtime, StructuralHead.POWER, T.number(3), T.number(2)),
    )
    assert parse_text(runtime, "x - y - z") == applied(
        runtime,
        StructuralHead.PLUS,
        x(runtime),
        applied(runtime, StructuralHead.TIMES, T.number(-1), named(runtime, "y")),
        applied(runtime, StructuralHead.TIMES, T.number(-1), named(runtime, "z")),
    )
    assert parse_text(runtime, "+x") == x(runtime)


def test_unary_minus_binds_weaker_than_power(runtime):
    assert parse_text(runtime, "-x^2") == applied(
        runtime,
        StructuralHead.TIMES,
        T.number(-1),
        applied(runtime, StructuralHead.POWER, x(runtime), T.number(2)),
    )
    assert parse_text(runtime, "(-x)^2") == applied(
        runtime,
        StructuralHead.POWER,
        applied(runtime, StructuralHead.TIMES, T.number(-1), x(runtime)),
        T.number(2),
    )


def test_application_keeps_argument_order_and_supports_zero_arity(runtime):
    source = "f(x, y + 1)"
    parsed = parse_text(runtime, source)
    function = named(runtime, "f")
    assert parsed == T.app(
        function,
        x(runtime),
        applied(runtime, StructuralHead.PLUS, named(runtime, "y"), T.number(1)),
    )
    assert parse_text(runtime, "f()") == T.app(named(runtime, "f"))
    assert parse_text(runtime, "x + y") != parse_text(runtime, "y + x")


def test_structural_heads_can_be_called_generically(runtime):
    assert parse_text(runtime, "Plus(x, 1)") == parse_text(runtime, "x + 1")
    assert parse_text(runtime, "Times(x, y)") == parse_text(runtime, "x*y")
    assert parse_text(runtime, "Power(x, 2)") == parse_text(runtime, "x^2")


def test_comparisons_map_to_structural_heads(runtime):
    pairs = {
        "==": StructuralHead.EQ,
        "=": StructuralHead.EQ,
        "!=": StructuralHead.NE,
        "<": StructuralHead.LT,
        "<=": StructuralHead.LE,
        ">": StructuralHead.GT,
        ">=": StructuralHead.GE,
    }
    for symbol, kind in pairs.items():
        assert parse_text(runtime, f"x {symbol} 1") == applied(
            runtime, kind, x(runtime), T.number(1)
        )


def test_boolean_precedence_and_implication(runtime):
    comparison = applied(
        runtime,
        StructuralHead.EQ,
        named(runtime, "a"),
        named(runtime, "b"),
    )
    assert parse_text(runtime, "a == b and not c") == applied(
        runtime,
        StructuralHead.AND,
        comparison,
        applied(runtime, StructuralHead.NOT, named(runtime, "c")),
    )
    assert parse_text(runtime, "a or b and c") == applied(
        runtime,
        StructuralHead.OR,
        named(runtime, "a"),
        applied(
            runtime,
            StructuralHead.AND,
            named(runtime, "b"),
            named(runtime, "c"),
        ),
    )
    assert parse_text(runtime, "a => b => c") == applied(
        runtime,
        StructuralHead.IMPLIES,
        named(runtime, "a"),
        applied(
            runtime,
            StructuralHead.IMPLIES,
            named(runtime, "b"),
            named(runtime, "c"),
        ),
    )
    assert parse_text(runtime, "not a == b") == applied(
        runtime, StructuralHead.NOT, comparison
    )


def test_quote_forms_are_distinct(runtime):
    inner = parse_text(runtime, "x + 1")
    assert parse_text(runtime, "quote(x + 1)") == T.quote(inner)
    assert parse_text(runtime, "Quote(x + 1)") == applied(
        runtime, StructuralHead.QUOTE, inner
    )


def test_piecewise_and_guarded_parse_as_structural_calls(runtime):
    condition = parse_text(runtime, "x == 1")
    assert parse_text(runtime, "Guarded(x == 1, x)") == applied(
        runtime, StructuralHead.GUARDED, condition, x(runtime)
    )
    assert parse_text(runtime, "Piecewise(x, x == 1, 0, true)") == applied(
        runtime,
        StructuralHead.PIECEWISE,
        x(runtime),
        condition,
        T.number(0),
        T.TRUE,
    )


def test_names_get_one_stable_id_until_shadowed(runtime):
    first = parse_text(runtime, "u")
    second = parse_text(runtime, "u")
    assert first == second
    identifier = runtime.table.lookup("u")
    assert identifier is not None
    assert first == T.symbol(identifier, "u")
    shadow = runtime.table.fresh("u")
    third = parse_text(runtime, "u")
    assert third == T.symbol(shadow, "u")
    assert third != first


def test_parsing_does_not_simplify(runtime):
    assert parse_text(runtime, "1 + 1") == applied(
        runtime, StructuralHead.PLUS, T.number(1), T.number(1)
    )
    assert parse_text(runtime, "x - x") == applied(
        runtime,
        StructuralHead.PLUS,
        x(runtime),
        applied(runtime, StructuralHead.TIMES, T.number(-1), x(runtime)),
    )
    assert parse_text(runtime, "0*x") == applied(
        runtime, StructuralHead.TIMES, T.number(0), x(runtime)
    )
    assert parse_text(runtime, "x^1") == applied(
        runtime, StructuralHead.POWER, x(runtime), T.number(1)
    )
    assert parse_text(runtime, "x + 0") == applied(
        runtime, StructuralHead.PLUS, x(runtime), T.number(0)
    )


@pytest.mark.parametrize(
    ("text", "fragment"),
    [
        ("", "expected an expression"),
        ("x +", "expected an expression"),
        ("(x", "expected ')'"),
        ("x)", "unexpected token"),
        ("1 2", "unexpected token"),
        ("$", "unexpected character"),
        ("a < b < c", "chained comparison"),
        ("and", "operator"),
        ("quote()", "quote takes exactly one argument"),
        ("quote(x, y)", "quote takes exactly one argument"),
    ],
)
def test_parse_errors_are_explicit(runtime, text, fragment):
    with pytest.raises(ParseError) as caught:
        parse_text(runtime, text)
    assert fragment in str(caught.value)


def test_error_positions_are_reported(runtime):
    with pytest.raises(ParseError) as empty:
        parse_text(runtime, "")
    assert empty.value.position == 0
    assert "column 1" in str(empty.value)
    with pytest.raises(ParseError) as trailing:
        parse_text(runtime, "x +")
    assert trailing.value.position == 3
    assert "column 4" in str(trailing.value)
