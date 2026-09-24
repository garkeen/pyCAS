"""Subterm abstraction acceptance."""

from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.runtime import Runtime
from cas.syntax import term as T
from cas.syntax.abstract import Abstraction, abstract_subterms, thaw
from cas.syntax.termpath import free_vars, subst


def _is_sin(u):
    return isinstance(u, T.Expr) and u.head.name == "Sin"


def _is_power(u):
    return isinstance(u, T.Expr) and u.head.name == "Power"


def test_same_subterm_shares_symbol(runtime: Runtime) -> None:
    a = abstract_subterms(parse(runtime, "sin(x)^2 + sin(x)"), _is_sin)
    assert len(a.replacements) == 1, [s.name for s, _ in a.replacements]
    sym = a.replacements[0][0]
    assert to_str(runtime, a.term).count(sym.name) == 2


def test_abstraction_is_reversible(runtime: Runtime) -> None:
    term = parse(runtime, "sin(x)^2 + sin(x)")
    abstraction = abstract_subterms(term, _is_sin)
    assert to_str(runtime, abstraction.thaw()) == to_str(runtime, term)
    assert to_str(runtime, thaw(abstraction.term, abstraction.replacements)) == to_str(
        runtime, term
    )


def test_maximal_match_does_not_descend_into_matched(runtime: Runtime) -> None:
    abstraction = abstract_subterms(parse(runtime, "x^2*y"), _is_power)
    assert len(abstraction.replacements) == 1
    assert _is_power(abstraction.replacements[0][1])
    assert to_str(runtime, abstraction.replacements[0][1]) == to_str(
        runtime, parse(runtime, "x^2")
    )


def test_fresh_symbol_avoids_existing_free_vars(runtime: Runtime) -> None:
    abstraction = abstract_subterms(parse(runtime, "_u0 + sin(x)"), _is_sin)
    assert [symbol.name for symbol, _ in abstraction.replacements] == ["_u1"]


def test_identity_when_no_match(runtime: Runtime) -> None:
    term = parse(runtime, "x + y")
    abstraction = abstract_subterms(term, _is_sin)
    assert abstraction.term is term
    assert abstraction.replacements == ()


def test_no_abstraction_inside_binder(runtime: Runtime) -> None:
    term = parse(runtime, "integrate(sin(x), x)")
    abstraction = abstract_subterms(term, _is_sin)
    assert abstraction.term is term
    assert abstraction.replacements == ()


def test_abstraction_result_participates_in_arithmetic(runtime: Runtime) -> None:
    abstraction = abstract_subterms(parse(runtime, "sin(x)^2 + sin(x)"), _is_sin)
    symbol = abstraction.replacements[0][0]
    value = subst(abstraction.term, {symbol: T.N(2)})
    assert isinstance(value, T.Term)
    assert not (free_vars(value) & {symbol})
    assert to_str(runtime, value) == to_str(runtime, parse(runtime, "2^2 + 2"))


def test_abstraction_thaw_matches_environment(runtime: Runtime) -> None:
    abstraction = abstract_subterms(
        parse(runtime, "cos(x)*cos(x)"),
        lambda term: isinstance(term, T.Expr) and term.head.name == "Cos",
    )
    assert isinstance(abstraction, Abstraction)
    assert len(abstraction.replacements) == 1
    assert to_str(runtime, abstraction.thaw()) == to_str(
        runtime, parse(runtime, "cos(x)*cos(x)")
    )
