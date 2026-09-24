"""Print names and source-form round trips."""

from cas.api import fold
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.runtime import Runtime
from cas.syntax import term as T


def test_sym_not_remapped(runtime: Runtime) -> None:
    assert to_str(runtime, T.S("pi")) == "pi"
    assert to_str(runtime, T.S("gamma")) == "gamma"


def test_const_uses_declared_print_name(runtime: Runtime) -> None:
    assert to_str(runtime, parse(runtime, "pi")) == "π"
    assert to_str(runtime, parse(runtime, "gamma")) == "γ"


def test_display_form_separate_from_source_form(runtime: Runtime) -> None:
    for source, display, code in [
        ("pi", "π", "pi"),
        ("gamma", "γ", "gamma"),
    ]:
        term = parse(runtime, source)
        assert to_str(runtime, term) == display
        assert to_str(runtime, term, src=True) == code


def test_source_form_round_trips(runtime: Runtime) -> None:
    for source in [
        "pi",
        "gamma",
        "pi + gamma",
        "2*pi*x",
        "gamma^2",
        "e^(i*pi)",
        "sin(x) + pi",
        "-2*x",
        "x^-2",
        "2/3*x",
        "-3/4*x",
        "-2/3",
        "3*x^-2",
    ]:
        term = parse(runtime, source)
        assert parse(runtime, to_str(runtime, term, src=True)) is term


def test_times_converges_every_numeric_factor(runtime: Runtime) -> None:
    assert to_str(runtime, parse(runtime, "-2*x")) == "-2*x"
    assert to_str(runtime, parse(runtime, "-2*3*x")) == "-6*x"
    assert to_str(runtime, parse(runtime, "x^-2")) == "x^(-2)"
    assert to_str(runtime, parse(runtime, "-3/4*x")) == "-3*x/4"
    assert to_str(runtime, parse(runtime, "6/4")) == "3/2"
    assert to_str(runtime, parse(runtime, "1/2*x/3")) == "x/6"
    assert to_str(runtime, parse(runtime, "1*x")) == "x"


def test_times_round_trip_preserves_the_folded_value(runtime: Runtime) -> None:
    for source in [
        "-2*x",
        "x^-2",
        "1*x",
        "-2*3*x",
        "2/3*x",
        "-3/4*x",
        "x/3",
        "2*x/3",
        "1/2*x/3",
        "6/4",
        "0*3*x",
        "x*y/3",
        "-0.5*x",
    ]:
        term = parse(runtime, source)
        reparsed = parse(runtime, to_str(runtime, term, src=True))
        assert fold(reparsed) is fold(term)


def test_syntax_atoms_not_from_declarations(runtime: Runtime) -> None:
    assert to_str(runtime, parse(runtime, "infinity")) == "Infinity"
    assert to_str(runtime, parse(runtime, "true")) == "true"
    assert to_str(runtime, parse(runtime, "false")) == "false"


def test_function_head_print_name_same_exit(runtime: Runtime) -> None:
    assert to_str(runtime, parse(runtime, "sin(x)")) == "sin(x)"
    assert to_str(runtime, parse(runtime, "cos(x) + log(x)")) == "cos(x) + log(x)"


def test_sqrt_is_declared_alias_not_parser_hardcode(runtime: Runtime) -> None:
    term = parse(runtime, "sqrt(x)")
    assert term.head.name == "Sqrt"
    assert to_str(runtime, term) == "sqrt(x)"
    assert parse(runtime, "ln(x)").head.name == "Log"
