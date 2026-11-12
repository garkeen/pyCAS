"""The `HasFactorization` specification and its encoded factor-set contract."""

from fractions import Fraction

import pytest
from factorization_support import factorization_setup, variable
from support import head_app, structural

from cas.language import sorts as S
from cas.language.sets import set_members, set_term
from cas.language.signatures import OperatorSignature, StructuralHead
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
    FactorizationVocabulary,
    HenselIrreducibilityWitness,
    certificate_matches_claim,
    factorization_factor_set,
    factorization_product_term,
    factorization_radical_term,
    has_factorization,
    parse_factor_entries,
    parse_factorization,
)
from cas.syntax import term as T


def x(setup):
    return variable(setup)


def one():
    return T.number(1)


def two():
    return T.number(2)


def x_plus_one(setup):
    return head_app(setup.signature, StructuralHead.PLUS, x(setup), one())


def x_squared_plus_one(setup):
    return head_app(
        setup.signature,
        StructuralHead.PLUS,
        head_app(setup.signature, StructuralHead.POWER, x(setup), two()),
        one(),
    )


def power_term(setup, base, exponent):
    return head_app(
        setup.signature, StructuralHead.POWER, base, exponent
    )


def test_the_vocabulary_signature_is_the_factorization_predicate(runtime):
    setup = factorization_setup(runtime)
    assert setup.vocabulary.signature == OperatorSignature(
        (S.REAL, S.REAL, S.REAL, S.SetSort(S.REAL)),
        S.PROPOSITION,
    )
    assert setup.vocabulary.name == "HasFactorization"


def test_the_vocabulary_needs_a_name_and_a_symbol(runtime):
    symbol = runtime.table.intern("Factor")
    with pytest.raises(ValueError):
        FactorizationVocabulary(symbol, "")
    with pytest.raises(TypeError):
        FactorizationVocabulary(True, "Factor")  # type: ignore[arg-type]


def test_has_and_parse_round_trip(runtime):
    setup = factorization_setup(runtime)
    factors = set_term(setup.signature, ())
    term = has_factorization(
        setup.vocabulary,
        x(setup),
        x(setup),
        T.number(Fraction(3, 2)),
        factors,
    )
    claim = parse_factorization(setup.vocabulary, term)
    assert claim is not None
    assert claim.source == x(setup)
    assert claim.variable.symbol_id == runtime.variable
    assert claim.unit == T.number(Fraction(3, 2))
    assert claim.factors == factors


def test_parse_rejects_another_predicate_arity_and_variable(runtime):
    setup = factorization_setup(runtime)
    factors = set_term(setup.signature, ())
    other = FactorizationVocabulary(
        runtime.table.intern("AnotherFactorization"), "AnotherFactorization"
    )
    assert (
        parse_factorization(
            other,
            has_factorization(
                setup.vocabulary, x(setup), x(setup), one(), factors
            ),
        )
        is None
    )
    wrong_arity = T.app(
        T.symbol(setup.vocabulary.symbol, setup.vocabulary.name),
        x(setup),
        x(setup),
        one(),
    )
    assert parse_factorization(setup.vocabulary, wrong_arity) is None
    no_symbol = T.app(
        T.symbol(setup.vocabulary.symbol, setup.vocabulary.name),
        x(setup),
        T.number(1),
        one(),
        factors,
    )
    assert parse_factorization(setup.vocabulary, no_symbol) is None
    assert parse_factorization(setup.vocabulary, x(setup)) is None


def test_a_squared_factor_is_a_multiplicity_wrapper(runtime):
    setup = factorization_setup(runtime)
    entries = ((x(setup), 2),)
    factors = factorization_factor_set(setup.signature, entries)
    expected = set_term(
        setup.signature, (power_term(setup, x(setup), two()),)
    )
    assert factors == expected
    assert parse_factor_entries(setup.signature, factors) == entries
    assert set_members(factors, setup.signature) == (
        power_term(setup, x(setup), two()),
    )


def test_a_shifted_factor_uses_the_same_wrapper(runtime):
    setup = factorization_setup(runtime)
    entries = ((x_plus_one(setup), 2),)
    factors = factorization_factor_set(setup.signature, entries)
    expected = set_term(
        setup.signature,
        (power_term(setup, x_plus_one(setup), two()),),
    )
    assert factors == expected
    assert parse_factor_entries(setup.signature, factors) == entries


def test_a_polynomial_base_uses_the_same_wrapper(runtime):
    setup = factorization_setup(runtime)
    base = x_squared_plus_one(setup)
    entries = ((base, 2),)
    factors = factorization_factor_set(setup.signature, entries)
    expected = set_term(
        setup.signature, (power_term(setup, base, two()),)
    )
    assert factors == expected
    assert parse_factor_entries(setup.signature, factors) == entries


def test_a_bare_member_has_multiplicity_one(runtime):
    setup = factorization_setup(runtime)
    factors = set_term(setup.signature, (x_plus_one(setup),))
    assert parse_factor_entries(setup.signature, factors) == (
        (x_plus_one(setup), 1),
    )


@pytest.mark.parametrize(
    "exponent",
    (one(), T.number(0), T.number(-1), T.number(Fraction(1, 2))),
)
def test_a_power_wrapper_needs_a_positive_integer_at_least_two(
    runtime, exponent
):
    setup = factorization_setup(runtime)
    factors = set_term(
        setup.signature, (power_term(setup, x(setup), exponent),)
    )
    assert parse_factor_entries(setup.signature, factors) is None


def test_a_power_wrapper_needs_the_right_arity(runtime):
    setup = factorization_setup(runtime)
    short = set_term(
        setup.signature,
        (T.app(structural(setup.signature, StructuralHead.POWER), x(setup)),),
    )
    long = set_term(
        setup.signature,
        (
            T.app(
                structural(setup.signature, StructuralHead.POWER),
                x(setup),
                two(),
                two(),
            ),
        ),
    )
    assert parse_factor_entries(setup.signature, short) is None
    assert parse_factor_entries(setup.signature, long) is None


def test_duplicate_bases_are_refused_by_both_boundaries(runtime):
    setup = factorization_setup(runtime)
    raw = T.app(structural(setup.signature, StructuralHead.SET), x(setup), x(setup))
    assert parse_factor_entries(setup.signature, raw) is None
    with pytest.raises(ValueError):
        factorization_factor_set(
            setup.signature, ((x(setup), 1), (x(setup), 2))
        )


def test_a_non_canonical_set_order_is_not_parsed(runtime):
    setup = factorization_setup(runtime)
    raw = T.app(
        structural(setup.signature, StructuralHead.SET),
        x_plus_one(setup),
        x(setup),
    )
    assert parse_factor_entries(setup.signature, raw) is None


def test_a_nested_power_wrapper_is_not_parsed(runtime):
    setup = factorization_setup(runtime)
    inner = power_term(setup, x(setup), two())
    outer = power_term(setup, inner, two())
    factors = set_term(setup.signature, (outer,))
    assert parse_factor_entries(setup.signature, factors) is None


def test_a_top_level_power_base_is_ambiguous(runtime):
    setup = factorization_setup(runtime)
    wrapper = power_term(setup, x(setup), two())
    with pytest.raises(ValueError):
        factorization_factor_set(setup.signature, ((wrapper, 1),))
    with pytest.raises(ValueError):
        factorization_radical_term(setup.signature, ((wrapper, 1),))


def test_a_non_set_argument_is_not_parsed(runtime):
    setup = factorization_setup(runtime)
    assert parse_factor_entries(setup.signature, x(setup)) is None
    assert (
        parse_factor_entries(
            setup.signature,
            head_app(
                setup.signature,
                StructuralHead.PLUS,
                x(setup),
                one(),
            ),
        )
        is None
    )


def test_the_product_omits_unit_one_unless_there_are_no_factors(runtime):
    setup = factorization_setup(runtime)
    factors = factorization_factor_set(setup.signature, ((x(setup), 1),))
    assert (
        factorization_product_term(setup.signature, one(), factors)
        == x(setup)
    )
    empty = set_term(setup.signature, ())
    assert (
        factorization_product_term(setup.signature, one(), empty) == one()
    )
    assert (
        factorization_product_term(
            setup.signature, T.number(6), empty
        )
        == T.number(6)
    )


def test_the_product_keeps_a_nonunit_factor(runtime):
    setup = factorization_setup(runtime)
    factors = factorization_factor_set(setup.signature, ((x(setup), 1),))
    product = factorization_product_term(
        setup.signature, T.number(2), factors
    )
    assert product == T.app(
        structural(setup.signature, StructuralHead.TIMES),
        T.number(2),
        x(setup),
    )


def test_the_product_renders_multiplicities_and_multiple_factors(runtime):
    setup = factorization_setup(runtime)
    factors = factorization_factor_set(
        setup.signature,
        ((x(setup), 2), (x_plus_one(setup), 1)),
    )
    product = factorization_product_term(
        setup.signature, one(), factors
    )
    assert product == T.app(
        structural(setup.signature, StructuralHead.TIMES),
        x_plus_one(setup),
        power_term(setup, x(setup), two()),
    )


def test_the_product_keeps_a_negative_unit(runtime):
    setup = factorization_setup(runtime)
    factors = factorization_factor_set(setup.signature, ((x(setup), 1),))
    product = factorization_product_term(
        setup.signature, T.number(-1), factors
    )
    assert product == T.app(
        structural(setup.signature, StructuralHead.TIMES),
        T.number(-1),
        x(setup),
    )


def test_a_zero_unit_is_not_a_product(runtime):
    setup = factorization_setup(runtime)
    factors = factorization_factor_set(setup.signature, ((x(setup), 1),))
    assert (
        factorization_product_term(
            setup.signature, T.number(0), factors
        )
        is None
    )


def test_a_nonliteral_unit_is_not_a_product(runtime):
    setup = factorization_setup(runtime)
    factors = factorization_factor_set(setup.signature, ((x(setup), 1),))
    assert (
        factorization_product_term(setup.signature, x(setup), factors)
        is None
    )
    assert (
        factorization_product_term(
            setup.signature,
            head_app(
                setup.signature,
                StructuralHead.POWER,
                x(setup),
                two(),
            ),
            factors,
        )
        is None
    )


def test_a_malformed_factor_set_is_not_a_product(runtime):
    setup = factorization_setup(runtime)
    assert (
        factorization_product_term(
            setup.signature, one(), x(setup)
        )
        is None
    )
    bad = set_term(
        setup.signature, (power_term(setup, x(setup), one()),)
    )
    assert (
        factorization_product_term(setup.signature, one(), bad) is None
    )


def test_the_radical_uses_each_distinct_base_once(runtime):
    setup = factorization_setup(runtime)
    assert (
        factorization_radical_term(setup.signature, ())
        == one()
    )
    single = factorization_radical_term(
        setup.signature, ((x(setup), 3),)
    )
    assert single == x(setup)
    entries = ((x(setup), 1), (x_plus_one(setup), 2))
    radical = factorization_radical_term(setup.signature, entries)
    assert radical == T.app(
        structural(setup.signature, StructuralHead.TIMES),
        x(setup),
        x_plus_one(setup),
    )


def test_the_radical_is_deterministic_under_entry_order(runtime):
    setup = factorization_setup(runtime)
    forward = factorization_radical_term(
        setup.signature,
        ((x(setup), 1), (x_plus_one(setup), 1)),
    )
    reverse = factorization_radical_term(
        setup.signature,
        ((x_plus_one(setup), 1), (x(setup), 1)),
    )
    assert forward == reverse


def test_the_radical_refuses_duplicate_bases(runtime):
    setup = factorization_setup(runtime)
    with pytest.raises(ValueError):
        factorization_radical_term(
            setup.signature,
            ((x(setup), 1), (x(setup), 2)),
        )


def test_the_certificate_matches_only_its_claim(runtime):
    setup = factorization_setup(runtime)
    factors = factorization_factor_set(setup.signature, ((x(setup), 1),))
    claim = parse_factorization(
        setup.vocabulary,
        has_factorization(
            setup.vocabulary,
            x(setup),
            x(setup),
            one(),
            factors,
        ),
    )
    assert claim is not None
    certificate = FactorizationCertificate(
        x(setup),
        runtime.variable,
        one(),
        factors,
        x(setup),
    )
    assert certificate_matches_claim(certificate, claim)
    assert not certificate_matches_claim(
        FactorizationCertificate(
            x_plus_one(setup),
            runtime.variable,
            one(),
            factors,
            x(setup),
        ),
        claim,
    )
    assert not certificate_matches_claim(
        FactorizationCertificate(
            x(setup),
            runtime.variable,
            T.number(2),
            factors,
            x(setup),
        ),
        claim,
    )
    assert not certificate_matches_claim(
        FactorizationCertificate(
            x(setup),
            runtime.variable,
            one(),
            factorization_factor_set(
                setup.signature, ((x_plus_one(setup), 1),)
            ),
            x(setup),
        ),
        claim,
    )


def test_the_hensel_witness_validates_its_structure_only(runtime):
    with pytest.raises(ValueError):
        HenselIrreducibilityWitness(0, 1, (T.number(1),))
    with pytest.raises(ValueError):
        HenselIrreducibilityWitness(2, 1, ())
    with pytest.raises(ValueError):
        HenselIrreducibilityWitness(2, 0, (T.number(1),))
    with pytest.raises(TypeError):
        HenselIrreducibilityWitness(True, 1, (T.number(1),))  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        HenselIrreducibilityWitness(2, 1, (1,))  # type: ignore[arg-type]
    witness = HenselIrreducibilityWitness(4, 1, (T.number(1),))
    assert witness.prime == 4
    assert witness.precision == 1
    assert witness.lifted == (T.number(1),)


def test_the_certificate_validates_its_structure(runtime):
    factors = set_term(runtime.signature, ())
    with pytest.raises(TypeError):
        FactorizationCertificate(
            T.number(1), True, T.number(1), factors, T.number(1)
        )
    with pytest.raises(TypeError):
        FactorizationCertificate(
            T.number(1), runtime.variable, 1, factors, T.number(1)
        )
    with pytest.raises(TypeError):
        FactorizationCertificate(
            T.number(1),
            runtime.variable,
            T.number(1),
            factors,
            T.number(1),
            "witness",  # type: ignore[arg-type]
        )
