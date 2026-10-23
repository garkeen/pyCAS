"""The HasDerivative vocabulary: construction, parsing and display independence."""

from support import variable

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
    has_derivative,
    parse_has_derivative,
)
from cas.syntax import term as T


def test_the_predicate_signature_is_region_source_variable_candidate(runtime):
    signature = runtime.vocabulary.signature
    assert signature.arguments == (S.PROPOSITION, S.REAL, S.REAL, S.REAL)
    assert signature.result == S.PROPOSITION


def test_construction_and_parsing_round_trip(runtime):
    x = variable(runtime)
    source = x
    candidate = T.number(1)
    term = has_derivative(runtime.vocabulary, T.TRUE, source, x, candidate)
    claim = parse_has_derivative(runtime.vocabulary, term)
    assert claim is not None
    assert claim.region == T.TRUE
    assert claim.source == source
    assert claim.variable == x
    assert claim.candidate == candidate


def test_parsing_is_by_symbol_id_not_by_spelling(runtime):
    x = variable(runtime)
    term = has_derivative(runtime.vocabulary, T.TRUE, x, x, T.number(1))
    impostor = DerivativeVocabulary(SymbolId(10_000), "HasDerivative")
    assert parse_has_derivative(impostor, term) is None


def test_parsing_rejects_other_shapes(runtime):
    x = variable(runtime)
    assert parse_has_derivative(runtime.vocabulary, T.TRUE) is None
    wrong_arity = T.app(
        T.symbol(runtime.vocabulary.symbol, "HasDerivative"),
        T.TRUE,
        x,
        x,
    )
    assert parse_has_derivative(runtime.vocabulary, wrong_arity) is None
    non_symbolical_variable = T.app(
        T.symbol(runtime.vocabulary.symbol, "HasDerivative"),
        T.TRUE,
        x,
        T.number(1),
        T.number(1),
    )
    assert (
        parse_has_derivative(runtime.vocabulary, non_symbolical_variable)
        is None
    )
    non_symbol_operator = T.app(T.BoundVar(0), T.TRUE, x, x, T.number(1))
    assert parse_has_derivative(runtime.vocabulary, non_symbol_operator) is None
