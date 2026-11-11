"""The `HasGroebnerBasis(G, B, O)` specification and cofactor certificate."""

import pytest

from cas.algebra.polynomial import MonomialOrder
from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import OperatorSignature
from cas.math.algebra.groebner_specification import (
    GroebnerCertificate,
    GroebnerClaim,
    GroebnerVocabulary,
    has_groebner_basis,
    parse_groebner,
)
from cas.syntax import term as T

PREDICATE = SymbolId(101)
ORDER = SymbolId(102)
OTHER = SymbolId(103)
SET_HEAD = T.symbol(SymbolId(104), "Set")


def vocabulary(
    *,
    name: str = "HasGroebnerBasis",
    order: MonomialOrder = MonomialOrder.LEX,
    member_sort: S.Sort = S.REAL,
) -> GroebnerVocabulary:
    return GroebnerVocabulary(
        PREDICATE, name, ORDER, order, member_sort
    )


def set_of(*members: T.Term) -> T.Term:
    return T.app(SET_HEAD, *members)


def test_the_signature_reads_two_sets_and_a_quoted_order():
    signature = vocabulary().signature
    assert signature == OperatorSignature(
        (S.SetSort(S.REAL), S.SetSort(S.REAL), S.SYNTAX),
        S.PROPOSITION,
    )
    rational = vocabulary(member_sort=S.RATIONAL).signature
    assert rational.arguments[0] == S.SetSort(S.RATIONAL)
    assert rational.arguments[1] == S.SetSort(S.RATIONAL)


def test_the_order_term_is_the_quoted_order_symbol():
    for order in (
        MonomialOrder.LEX,
        MonomialOrder.GRLEX,
        MonomialOrder.GREVLEX,
    ):
        assert vocabulary(order=order).order_term() == T.quote(
            T.symbol(ORDER, order.value)
        )


def test_build_and_parse_round_trip():
    generators = set_of(T.number(1), T.number(2))
    basis = set_of(T.number(1))
    order = vocabulary().order_term()
    term = has_groebner_basis(vocabulary(), generators, basis, order)
    claim = parse_groebner(vocabulary(), term)
    assert claim == GroebnerClaim(generators, basis, order)


def test_an_empty_cofactor_matrix_is_allowed():
    certificate = GroebnerCertificate(())
    assert certificate.cofactors == ()
    certificate = GroebnerCertificate(((T.number(1),), ()))
    assert certificate.cofactors == ((T.number(1),), ())


def test_a_cofactor_matrix_rejects_non_terms():
    with pytest.raises(TypeError):
        GroebnerCertificate(((T.number(1), object()),))  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        GroebnerCertificate((object(),))  # type: ignore[arg-type]


def test_parse_rejects_another_predicate_and_wrong_arity():
    generators = set_of()
    basis = set_of()
    order = vocabulary().order_term()
    other = T.app(
        T.symbol(OTHER, "OtherPredicate"), generators, basis, order
    )
    assert parse_groebner(vocabulary(), other) is None
    short = T.app(T.symbol(PREDICATE, "HasGroebnerBasis"), generators, basis)
    assert parse_groebner(vocabulary(), short) is None
    long = T.app(
        T.symbol(PREDICATE, "HasGroebnerBasis"),
        generators,
        basis,
        order,
        T.number(1),
    )
    assert parse_groebner(vocabulary(), long) is None
    assert parse_groebner(vocabulary(), T.number(1)) is None


def test_the_vocabulary_validates_its_name_order_and_member_sort():
    with pytest.raises(ValueError):
        vocabulary(name="")
    with pytest.raises(TypeError):
        GroebnerVocabulary(
            PREDICATE,
            "HasGroebnerBasis",
            ORDER,
            "lex",  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError):
        vocabulary(member_sort=object())  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        vocabulary(member_sort=S.SetSort(S.REAL))


def test_a_claim_needs_terms_in_every_position():
    with pytest.raises(TypeError):
        GroebnerClaim(object(), set_of(), set_of())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        GroebnerClaim(set_of(), object(), set_of())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        GroebnerClaim(set_of(), set_of(), object())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        has_groebner_basis(
            vocabulary(), object(), set_of(), set_of()  # type: ignore[arg-type]
        )
