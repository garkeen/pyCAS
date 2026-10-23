"""Printing: readable forms and exact source round trips."""

from fractions import Fraction

import pytest

from cas.frontend.parser import parse
from cas.frontend.pprint import to_source, to_str
from cas.language.signatures import StructuralHead
from cas.syntax import term as T


def head(runtime, kind: StructuralHead) -> T.SymbolRef:
    identifier = runtime.signature.symbol_of(kind)
    assert identifier is not None
    return T.symbol(identifier, kind.value)


def x(runtime) -> T.SymbolRef:
    return T.symbol(runtime.variable, "x")


def parsed(runtime, text: str) -> T.Term:
    return parse(text, runtime.table, runtime.signature)


def render(runtime, text: str) -> str:
    return to_str(parsed(runtime, text), runtime.signature)


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        ("x + y", "x + y"),
        ("x^3 - 3*x", "x^3 - 3*x"),
        ("x - (y - z)", "x - (y - z)"),
        ("(x + 1)*y", "(x + 1)*y"),
        ("x^(y + 1)", "x^(y + 1)"),
        ("(x^y)^z", "(x^y)^z"),
        ("-x^2", "-x^2"),
        ("(-x)^2", "(-x)^2"),
        ("(1/2)^x", "(1/2)^x"),
        ("not (a and b)", "not (a and b)"),
        ("a == b and c != d", "a == b and c != d"),
        ("a => b => c", "a => b => c"),
        ("a or b and c", "a or b and c"),
        ("(a or b) and c", "(a or b) and c"),
        ("f(x, y + 1)", "f(x, y + 1)"),
        ("quote(x + 1)", "quote(x + 1)"),
        ("x + 1 == y", "x + 1 == y"),
        ("x^-1", "x^-1"),
        ("2*x", "2*x"),
        ("1*x", "x"),
        ("x*1", "x"),
        ("0*x", "0*x"),
        ("Guarded(x == 1, x)", "Guarded(x == 1, x)"),
        ("Piecewise(x, x == 1, 0, true)", "Piecewise(x, x == 1, 0, true)"),
    ],
)
def test_readable_forms(runtime, source, expected):
    assert render(runtime, source) == expected


def test_literal_renderings(runtime):
    assert to_str(T.number(Fraction(-1, 2)), runtime.signature) == "-1/2"
    assert to_str(T.number(-3), runtime.signature) == "-3"
    assert to_str(T.TRUE, runtime.signature) == "true"
    assert (
        to_str(
            T.app(
                head(runtime, StructuralHead.TIMES),
                T.number(-2),
                x(runtime),
            ),
            runtime.signature,
        )
        == "-2*x"
    )


ROUND_TRIP_SOURCES = [
    "x + 1",
    "x^3 - 3*x",
    "1/2*x + 3",
    "f(x, y + 1)",
    "a == b and not c",
    "a => b or c",
    "quote(x + 1)",
    "Guarded(x == 1, x)",
    "Piecewise(x, x == 1, 0, true)",
    "(-x)^2",
    "x^-1",
    "0*x",
    "1 + 2 + 3",
    "x/(y*z)",
]


@pytest.mark.parametrize("source", ROUND_TRIP_SOURCES)
def test_source_form_round_trips_parsed_terms(runtime, source):
    term = parsed(runtime, source)
    assert parsed(runtime, to_source(term, runtime.signature)) == term


def test_source_form_round_trips_structurally_built_terms(runtime):
    terms = [
        T.app(
            head(runtime, StructuralHead.PLUS),
            T.number(1),
            T.number(2),
            T.number(3),
        ),
        T.app(
            head(runtime, StructuralHead.TIMES), T.number(1), x(runtime)
        ),
        T.app(
            head(runtime, StructuralHead.POWER),
            x(runtime),
            T.number(-1),
        ),
        T.quote(
            T.app(
                head(runtime, StructuralHead.EQ),
                x(runtime),
                T.number(1),
            )
        ),
        T.app(head(runtime, StructuralHead.QUOTE), x(runtime)),
        T.app(T.symbol(runtime.table.intern("f"), "f")),
        T.app(head(runtime, StructuralHead.GUARDED), T.TRUE, x(runtime)),
    ]
    for term in terms:
        source = to_source(term, runtime.signature)
        assert parsed(runtime, source) == term


def test_source_form_refuses_binders(runtime):
    binder = T.binder("Lam", 1, T.BoundVar(0))
    with pytest.raises(ValueError):
        to_source(binder, runtime.signature)
    with pytest.raises(ValueError):
        to_source(T.BoundVar(0), runtime.signature)


def test_source_form_refuses_a_non_symbol_operator(runtime):
    term = T.app(T.app(x(runtime), T.number(1)), T.number(2))
    with pytest.raises(ValueError):
        to_source(term, runtime.signature)
    assert to_str(term, runtime.signature) == "x(1)(2)"


def test_readable_binders_are_renderable(runtime):
    binder = T.binder("Lam", 1, T.BoundVar(0), hint="u")
    assert to_str(binder, runtime.signature) == "Lam[u/1](#0)"
