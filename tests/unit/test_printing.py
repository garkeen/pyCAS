# -*- coding: utf-8 -*-
"""Print names: the display form consumes declarations, the source form must be
reparsable.

Nails:
1. Sym was once remapped by _SYM_REPR, so a user symbol named pi printed as the
   constant pi.
2. src=True was promised as the "parseable source form" yet emitted pi/gamma in
   display form, which the lexer does not accept, breaking round-tripping.
"""

from cas.syntax import term as T
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str


def test_sym_not_remapped():
    assert to_str(T.S("pi")) == "pi"
    assert to_str(T.S("gamma")) == "gamma"


def test_const_uses_declared_print_name():
    assert to_str(parse("pi")) == "π"
    assert to_str(parse("gamma")) == "γ"


def test_display_form_separate_from_source_form():
    for src, disp, code in [("pi", "π", "pi"), ("gamma", "γ", "gamma")]:
        t = parse(src)
        assert to_str(t) == disp                    # display: declared print name
        assert to_str(t, src=True) == code          # source: internal name


def test_source_form_round_trips():
    """The src=True promise: the output is accepted by the lexer and returns the same
    interned term."""
    for s in ["pi", "gamma", "pi + gamma", "2*pi*x", "gamma^2",
              "e^(i*pi)", "sin(x) + pi"]:
        t = parse(s)
        assert parse(to_str(t, src=True)) is t, f"round trip broke: {s}"


def test_syntax_atoms_not_from_declarations():
    """infinity/true/false are language notation, not mathematical constants."""
    assert to_str(parse("infinity")) == "Infinity"
    assert to_str(parse("true")) == "true"
    assert to_str(parse("false")) == "false"


def test_function_head_print_name_same_exit():
    assert to_str(parse("sin(x)")) == "sin(x)"
    assert to_str(parse("cos(x) + log(x)")) == "cos(x) + log(x)"


def test_sqrt_is_declared_alias_not_parser_hardcode():
    """`sqrt`/`ln` are **declared surface aliases** (declarations.dsl); the parser does
    not know them.

    The parser used to special-case `sqrt -> u^(1/2)` and `ln -> Log`, which is
    hardcoding of mathematical-semantics heads (a new notation would require a parser
    change). They now go through the declaration channel."""
    t = parse("sqrt(x)")
    assert t.head.name == "Sqrt"
    assert to_str(t) == "sqrt(x)"
    assert parse("ln(x)").head.name == "Log"
