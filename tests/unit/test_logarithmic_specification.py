"""The `HasRationalLogAntiderivative` specification and canonical log terms."""

from dataclasses import dataclass, replace
from fractions import Fraction
from typing import TYPE_CHECKING

import pytest
from support import elementary_basis, head_app

from cas.language import sorts as S
from cas.language.declarations import (
    Compare,
    Name,
    Negate,
    Num,
    Power,
    Product,
)
from cas.language.sets import set_term
from cas.language.signatures import (
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.math.calculus.integration.logarithmic_specification import (
    LogFunctionSemantics,
    RationalLogAntiderivativeCertificate,
    RationalLogAntiderivativeClaim,
    RationalLogVocabulary,
    certificate_matches_claim,
    has_rational_log_antiderivative,
    parse_rational_log_antiderivative,
    parse_rational_log_terms,
    rational_log_antiderivative_term,
    rational_log_term,
    rational_log_term_set,
    require_log_semantics,
)
from cas.math.elementary.declarations import (
    ElementaryLibrary,
    FunctionSymbol,
    build_elementary,
    default_elementary_declarations,
)
from cas.syntax import term as T

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


@dataclass(frozen=True, slots=True)
class RationalLogSetup:
    runtime: "Runtime"
    signature: LanguageSignature
    vocabulary: RationalLogVocabulary


def rational_log_setup(runtime: "Runtime") -> RationalLogSetup:
    predicate = runtime.table.intern("HasRationalLogAntiderivative")
    log_symbol = runtime.table.intern("Log")
    vocabulary = RationalLogVocabulary(
        predicate,
        "HasRationalLogAntiderivative",
        log_symbol,
        "Log",
    )
    operators = dict(runtime.signature.operators)
    operators[predicate] = vocabulary.signature
    operators[log_symbol] = OperatorSignature((S.REAL,), S.REAL)
    signature = LanguageSignature.build(
        runtime.signature.heads,
        runtime.signature.binders,
        operators,
    )
    return RationalLogSetup(runtime, signature, vocabulary)


def variable(setup: RationalLogSetup) -> T.SymbolRef:
    runtime = setup.runtime
    return T.symbol(runtime.variable, runtime.table.name_of(runtime.variable))


def one() -> T.Term:
    return T.number(1)


def x_plus_one(setup: RationalLogSetup) -> T.Term:
    return head_app(setup.signature, StructuralHead.PLUS, variable(setup), one())


def x_squared_plus_one(setup: RationalLogSetup) -> T.Term:
    return head_app(
        setup.signature,
        StructuralHead.PLUS,
        head_app(
            setup.signature,
            StructuralHead.POWER,
            variable(setup),
            T.number(2),
        ),
        one(),
    )


def log_term(setup: RationalLogSetup, argument: T.Term) -> T.Term:
    return T.app(setup.vocabulary.log_function, argument)


def times(setup: RationalLogSetup, *arguments: T.Term) -> T.Term:
    return head_app(setup.signature, StructuralHead.TIMES, *arguments)


def set_head(setup: RationalLogSetup) -> T.SymbolRef:
    identifier = setup.signature.symbol_of(StructuralHead.SET)
    assert identifier is not None
    return T.symbol(identifier, StructuralHead.SET.value)


def times_head(setup: RationalLogSetup) -> T.SymbolRef:
    identifier = setup.signature.symbol_of(StructuralHead.TIMES)
    assert identifier is not None
    return T.symbol(identifier, StructuralHead.TIMES.value)


def test_the_vocabulary_signature_is_the_rational_log_predicate(runtime):
    setup = rational_log_setup(runtime)
    assert setup.vocabulary.signature == OperatorSignature(
        (S.PROPOSITION, S.REAL, S.REAL, S.REAL, S.SetSort(S.REAL), S.REAL),
        S.PROPOSITION,
    )
    assert setup.vocabulary.name == "HasRationalLogAntiderivative"
    assert setup.vocabulary.log_name == "Log"
    assert setup.vocabulary.log_function == T.symbol(
        setup.vocabulary.log_symbol, "Log"
    )


def test_the_vocabulary_needs_distinct_symbols_and_names(runtime):
    symbol = runtime.table.intern("Predicate")
    log_symbol = runtime.table.intern("Log")
    with pytest.raises(ValueError):
        RationalLogVocabulary(symbol, "", log_symbol, "Log")
    with pytest.raises(ValueError):
        RationalLogVocabulary(symbol, "Predicate", log_symbol, "")
    with pytest.raises(ValueError):
        RationalLogVocabulary(symbol, "Predicate", symbol, "Log")
    with pytest.raises(TypeError):
        RationalLogVocabulary(True, "Predicate", log_symbol, "Log")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        RationalLogVocabulary(symbol, "Predicate", True, "Log")  # type: ignore[arg-type]


def test_has_and_parse_round_trip(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    log_terms = rational_log_term_set(
        setup.signature,
        log,
        (
            (Fraction(1), x_plus_one(setup)),
            (Fraction(-1, 2), x_squared_plus_one(setup)),
        ),
    )
    polynomial_part = T.number(Fraction(3, 2))
    result = rational_log_antiderivative_term(
        setup.signature, polynomial_part, log_terms
    )
    term = has_rational_log_antiderivative(
        setup.vocabulary,
        T.TRUE,
        T.number(1),
        variable(setup),
        polynomial_part,
        log_terms,
        result,
    )
    claim = parse_rational_log_antiderivative(setup.vocabulary, term)
    assert claim is not None
    assert claim.region == T.TRUE
    assert claim.source == T.number(1)
    assert claim.variable.symbol_id == setup.runtime.variable
    assert claim.polynomial_part == polynomial_part
    assert claim.log_terms == log_terms
    assert claim.result == result


def test_parse_rejects_another_predicate_arity_and_variable(runtime):
    setup = rational_log_setup(runtime)
    other = RationalLogVocabulary(
        setup.runtime.table.intern("AnotherPredicate"),
        "AnotherPredicate",
        setup.vocabulary.log_symbol,
        "Log",
    )
    log_terms = rational_log_term_set(setup.signature, setup.vocabulary.log_function, ())
    term = has_rational_log_antiderivative(
        setup.vocabulary,
        T.TRUE,
        T.number(1),
        variable(setup),
        T.number(0),
        log_terms,
        T.number(1),
    )
    assert parse_rational_log_antiderivative(other, term) is None
    wrong_arity = T.app(
        T.symbol(setup.vocabulary.symbol, setup.vocabulary.name),
        T.TRUE,
        T.number(1),
        variable(setup),
        T.number(0),
        log_terms,
    )
    assert parse_rational_log_antiderivative(
        setup.vocabulary, wrong_arity
    ) is None
    not_a_symbol = T.app(
        T.symbol(setup.vocabulary.symbol, setup.vocabulary.name),
        T.TRUE,
        T.number(1),
        T.number(3),
        T.number(0),
        log_terms,
        T.number(1),
    )
    assert parse_rational_log_antiderivative(
        setup.vocabulary, not_a_symbol
    ) is None


def test_the_specification_builders_require_terms_and_a_symbol(runtime):
    setup = rational_log_setup(runtime)
    log_terms = rational_log_term_set(
        setup.signature, setup.vocabulary.log_function, ()
    )
    with pytest.raises(TypeError):
        has_rational_log_antiderivative(
            setup.vocabulary,
            T.TRUE,
            "not a term",  # type: ignore[arg-type]
            variable(setup),
            T.number(0),
            log_terms,
            T.number(1),
        )
    with pytest.raises(TypeError):
        has_rational_log_antiderivative(
            setup.vocabulary,
            T.TRUE,
            T.number(1),
            T.number(3),  # type: ignore[arg-type]
            T.number(0),
            log_terms,
            T.number(1),
        )


def test_certificate_matches_the_claim(runtime):
    setup = rational_log_setup(runtime)
    log_terms = rational_log_term_set(
        setup.signature,
        setup.vocabulary.log_function,
        ((Fraction(1), x_plus_one(setup)),),
    )
    certificate = RationalLogAntiderivativeCertificate(
        T.TRUE,
        T.number(1),
        setup.runtime.variable,
        T.number(0),
        log_terms,
        log_term(setup, x_plus_one(setup)),
    )
    claim = RationalLogAntiderivativeClaim(
        T.TRUE,
        T.number(1),
        variable(setup),
        T.number(0),
        log_terms,
        log_term(setup, x_plus_one(setup)),
    )
    assert certificate_matches_claim(certificate, claim)
    mismatched = RationalLogAntiderivativeCertificate(
        T.TRUE,
        T.number(2),
        setup.runtime.variable,
        T.number(0),
        log_terms,
        log_term(setup, x_plus_one(setup)),
    )
    assert not certificate_matches_claim(mismatched, claim)
    other_variable = RationalLogAntiderivativeCertificate(
        T.TRUE,
        T.number(1),
        setup.runtime.table.intern("other"),
        T.number(0),
        log_terms,
        log_term(setup, x_plus_one(setup)),
    )
    assert not certificate_matches_claim(other_variable, claim)


def test_the_claim_and_certificate_validate_their_structure(runtime):
    setup = rational_log_setup(runtime)
    with pytest.raises(TypeError):
        RationalLogAntiderivativeClaim(
            T.TRUE,
            T.number(1),
            T.number(3),  # type: ignore[arg-type]
            T.number(0),
            T.number(0),
            T.number(1),
        )
    with pytest.raises(TypeError):
        RationalLogAntiderivativeCertificate(
            T.TRUE,
            "not a term",  # type: ignore[arg-type]
            setup.runtime.variable,
            T.number(0),
            T.number(0),
            T.number(1),
        )
    with pytest.raises(TypeError):
        RationalLogAntiderivativeCertificate(
            T.TRUE,
            T.number(1),
            True,  # type: ignore[arg-type]
            T.number(0),
            T.number(0),
            T.number(1),
        )


def test_a_unit_coefficient_is_a_bare_log_application(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    argument = x_plus_one(setup)
    member = rational_log_term(setup.signature, log, Fraction(1), argument)
    assert member == T.app(log, argument)


def test_other_coefficients_are_times_wrappers(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    argument = x_plus_one(setup)
    assert rational_log_term(
        setup.signature, log, Fraction(-1), argument
    ) == times(setup, T.number(-1), T.app(log, argument))
    assert rational_log_term(
        setup.signature, log, Fraction(-1, 2), argument
    ) == times(setup, T.number(Fraction(-1, 2)), T.app(log, argument))


def test_the_log_term_builder_rejects_invalid_coefficients(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    argument = x_plus_one(setup)
    with pytest.raises(ValueError):
        rational_log_term(setup.signature, log, Fraction(0), argument)
    with pytest.raises(TypeError):
        rational_log_term(setup.signature, log, 1, argument)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        rational_log_term(
            setup.signature,
            log,
            Fraction(1),
            "not a term",  # type: ignore[arg-type]
        )


def test_the_log_term_set_round_trips(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    entries = (
        (Fraction(1), x_plus_one(setup)),
        (Fraction(-1, 2), x_squared_plus_one(setup)),
    )
    terms = rational_log_term_set(setup.signature, log, entries)
    parsed = parse_rational_log_terms(setup.signature, log, terms)
    assert parsed is not None
    assert set(parsed) == set(entries)


def test_the_log_term_set_rejects_zero_and_duplicate_coefficients(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    with pytest.raises(ValueError):
        rational_log_term_set(
            setup.signature, log, ((Fraction(0), x_plus_one(setup)),)
        )
    with pytest.raises(ValueError):
        rational_log_term_set(
            setup.signature,
            log,
            (
                (Fraction(1), x_plus_one(setup)),
                (Fraction(1), x_squared_plus_one(setup)),
            ),
        )
    with pytest.raises(TypeError):
        rational_log_term_set(
            setup.signature, log, ((Fraction(1), "not a term"),)  # type: ignore[arg-type]
        )


def test_parse_rejects_a_zero_coefficient(runtime):
    setup = rational_log_setup(runtime)
    member = times(
        setup,
        T.number(0),
        log_term(setup, x_plus_one(setup)),
    )
    terms = set_term(setup.signature, (member,))
    assert parse_rational_log_terms(
        setup.signature, setup.vocabulary.log_function, terms
    ) is None


def test_parse_rejects_a_unit_times_wrapper(runtime):
    setup = rational_log_setup(runtime)
    member = times(
        setup,
        T.number(1),
        log_term(setup, x_plus_one(setup)),
    )
    terms = set_term(setup.signature, (member,))
    assert parse_rational_log_terms(
        setup.signature, setup.vocabulary.log_function, terms
    ) is None


def test_parse_rejects_a_nonliteral_coefficient(runtime):
    setup = rational_log_setup(runtime)
    member = times(
        setup,
        x_plus_one(setup),
        log_term(setup, x_squared_plus_one(setup)),
    )
    terms = set_term(setup.signature, (member,))
    assert parse_rational_log_terms(
        setup.signature, setup.vocabulary.log_function, terms
    ) is None


def test_parse_rejects_wrong_arity_and_nested_wrappers(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    argument = x_plus_one(setup)
    wrong_log_arity = T.app(log, argument, argument)
    wrong_times_arity = T.app(
        times_head(setup),
        T.number(-1),
        T.app(log, argument),
        argument,
    )
    nested = times(
        setup,
        T.number(-1),
        times(setup, T.number(1), T.app(log, argument)),
    )
    for member in (wrong_log_arity, wrong_times_arity, nested):
        terms = set_term(setup.signature, (member,))
        assert parse_rational_log_terms(setup.signature, log, terms) is None


def test_parse_rejects_a_non_log_member(runtime):
    setup = rational_log_setup(runtime)
    terms = set_term(setup.signature, (variable(setup),))
    assert parse_rational_log_terms(
        setup.signature, setup.vocabulary.log_function, terms
    ) is None


def test_parse_rejects_duplicate_coefficients(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    first = times(
        setup,
        T.number(Fraction(1, 2)),
        log_term(setup, x_plus_one(setup)),
    )
    second = times(
        setup,
        T.number(Fraction(1, 2)),
        log_term(setup, x_squared_plus_one(setup)),
    )
    terms = set_term(setup.signature, (first, second))
    assert parse_rational_log_terms(setup.signature, log, terms) is None


def test_parse_rejects_a_noncanonical_member_order(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    canonical = rational_log_term_set(
        setup.signature,
        log,
        (
            (Fraction(1), x_plus_one(setup)),
            (Fraction(-1, 2), x_squared_plus_one(setup)),
        ),
    )
    assert isinstance(canonical, T.Apply)
    reversed_order = T.app(
        set_head(setup), *reversed(canonical.arguments)
    )
    assert parse_rational_log_terms(
        setup.signature, log, reversed_order
    ) is None


def test_the_visible_result_with_no_log_terms_is_the_polynomial_part(runtime):
    setup = rational_log_setup(runtime)
    empty = rational_log_term_set(
        setup.signature, setup.vocabulary.log_function, ()
    )
    part = head_app(
        setup.signature, StructuralHead.PLUS, variable(setup), one()
    )
    assert rational_log_antiderivative_term(
        setup.signature, part, empty
    ) == part


def test_the_visible_result_with_one_log_term_is_that_term(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    terms = rational_log_term_set(
        setup.signature,
        log,
        ((Fraction(1), x_plus_one(setup)),),
    )
    assert rational_log_antiderivative_term(
        setup.signature, T.number(0), terms
    ) == log_term(setup, x_plus_one(setup))


def test_the_visible_result_flattens_the_polynomial_part(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    terms = rational_log_term_set(
        setup.signature,
        log,
        (
            (Fraction(1), x_plus_one(setup)),
            (Fraction(-1, 2), x_squared_plus_one(setup)),
        ),
    )
    part = head_app(
        setup.signature,
        StructuralHead.PLUS,
        head_app(
            setup.signature,
            StructuralHead.POWER,
            variable(setup),
            T.number(2),
        ),
        T.number(3),
    )
    result = rational_log_antiderivative_term(
        setup.signature, part, terms
    )
    assert isinstance(part, T.Apply)
    assert isinstance(result, T.Apply)
    assert result.arguments[:2] == part.arguments
    assert result.arguments[2:] == terms.arguments


def test_the_visible_result_omits_a_literal_zero_part(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    terms = rational_log_term_set(
        setup.signature,
        log,
        (
            (Fraction(1), x_plus_one(setup)),
            (Fraction(-1, 2), x_squared_plus_one(setup)),
        ),
    )
    result = rational_log_antiderivative_term(
        setup.signature, T.number(0), terms
    )
    assert isinstance(result, T.Apply)
    assert result.arguments == terms.arguments
    assert result.arguments[0] != T.number(0)


def test_the_visible_result_requires_a_canonical_set(runtime):
    setup = rational_log_setup(runtime)
    log = setup.vocabulary.log_function
    canonical = rational_log_term_set(
        setup.signature,
        log,
        (
            (Fraction(1), x_plus_one(setup)),
            (Fraction(-1, 2), x_squared_plus_one(setup)),
        ),
    )
    assert isinstance(canonical, T.Apply)
    reversed_order = T.app(set_head(setup), *reversed(canonical.arguments))
    with pytest.raises(ValueError):
        rational_log_antiderivative_term(
            setup.signature, T.number(0), reversed_order
        )
    with pytest.raises(ValueError):
        rational_log_antiderivative_term(
            setup.signature, T.number(0), T.number(0)
        )
def declared_library(runtime):
    declarations = default_elementary_declarations()
    return build_elementary(
        runtime.table.intern,
        declarations,
        reserved=frozenset({"x", "HasDerivative"}),
        basis=elementary_basis(declarations, runtime.world.id),
    )


def declared_semantics(runtime):
    library = declared_library(runtime)
    function = library.functions["log"]
    return library, LogFunctionSemantics(library, function)


def with_function(
    library: ElementaryLibrary, function: FunctionSymbol
) -> ElementaryLibrary:
    functions = dict(library.functions)
    functions[function.name] = function
    by_id = dict(library.functions_by_id)
    by_id[function.symbol] = function
    return replace(
        library, functions=functions, functions_by_id=by_id
    )


def test_the_log_semantics_instantiate_the_declared_domain_and_factor(runtime):
    library, semantics = declared_semantics(runtime)
    argument = T.symbol(
        runtime.variable, runtime.table.name_of(runtime.variable)
    )
    assert semantics.symbol == library.functions["log"].symbol
    assert semantics.name == "log"
    assert semantics.basis == library.basis
    assert semantics.domain(argument, runtime.signature) == head_app(
        runtime.signature,
        StructuralHead.GT,
        argument,
        T.number(0),
    )
    assert semantics.derivative_factor(
        argument, runtime.signature
    ) == head_app(
        runtime.signature,
        StructuralHead.POWER,
        argument,
        T.number(-1),
    )


@pytest.mark.parametrize(
    "domain",
    [
        Compare(">=", Name("u"), Num(Fraction(0))),
        Compare("!=", Name("u"), Num(Fraction(0))),
    ],
)
def test_log_semantics_reject_another_declared_domain(runtime, domain):
    library, _ = declared_semantics(runtime)
    function = library.functions["log"]
    wrong = replace(function, domain=domain)
    with pytest.raises(ValueError):
        LogFunctionSemantics(with_function(library, wrong), wrong)


def test_log_semantics_reject_another_derivative_body(runtime):
    library, _ = declared_semantics(runtime)
    function = library.functions["log"]
    law = function.law
    assert law is not None
    wrong_law = replace(
        law,
        body=Product(
            (
                Num(Fraction(2)),
                Power(Name("u"), Negate(Num(Fraction(1)))),
            )
        ),
    )
    wrong = replace(function, law=wrong_law)
    with pytest.raises(ValueError):
        LogFunctionSemantics(with_function(library, wrong), wrong)


def test_log_semantics_require_the_library_function(runtime):
    library, semantics = declared_semantics(runtime)
    other = replace(
        semantics.function,
        symbol=runtime.table.intern("AnotherLog"),
        name="AnotherLog",
    )
    with pytest.raises(ValueError):
        LogFunctionSemantics(library, other)


def test_the_vocabulary_semantics_must_match_its_log_symbol_and_name(runtime):
    library, semantics = declared_semantics(runtime)
    predicate = runtime.table.intern("Predicate")
    with pytest.raises(ValueError):
        RationalLogVocabulary(
            predicate,
            "Predicate",
            runtime.table.intern("AnotherLog"),
            "log",
            semantics,
        )
    with pytest.raises(ValueError):
        RationalLogVocabulary(
            predicate,
            "Predicate",
            semantics.symbol,
            "Log",
            semantics,
        )
    with pytest.raises(TypeError):
        RationalLogVocabulary(
            predicate,
            "Predicate",
            semantics.symbol,
            "log",
            object(),  # type: ignore[arg-type]
        )


def test_a_bare_vocabulary_has_no_log_semantics(runtime):
    predicate = runtime.table.intern("Predicate")
    log_symbol = runtime.table.intern("log")
    bare = RationalLogVocabulary(
        predicate, "Predicate", log_symbol, "log"
    )
    with pytest.raises(ValueError):
        require_log_semantics(bare)
    with pytest.raises(TypeError):
        require_log_semantics(object())  # type: ignore[arg-type]
