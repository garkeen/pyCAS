"""Propositions: the seal, well-scopedness and the meaning key."""

from dataclasses import replace

import pytest
from support import check_in, head_app, proposition_in, require_proposition

from cas.foundation.ids import SymbolId
from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.signatures import (
    BindingSignature,
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.syntax import term as T


def eq_one(runtime) -> T.Apply:
    x = T.symbol(runtime.variable, "x")
    return head_app(runtime.signature, StructuralHead.EQ, x, T.number(1))


def x_term(runtime) -> T.SymbolRef:
    return T.symbol(runtime.variable, "x")


def power(runtime, base: T.Term, exponent: int) -> T.Apply:
    return head_app(
        runtime.signature, StructuralHead.POWER, base, T.number(exponent)
    )


def ne_zero(runtime, base: T.Term) -> T.Apply:
    return head_app(
        runtime.signature, StructuralHead.NE, base, T.number(0)
    )


def test_negates_recognizes_the_language_not_head(runtime):
    x = T.symbol(runtime.variable, "x")
    not_x = head_app(runtime.signature, StructuralHead.NOT, x)
    assert Pr.negates(not_x, x, runtime.signature)
    assert not Pr.negates(x, not_x, runtime.signature)
    assert not Pr.negates(not_x, T.number(1), runtime.signature)


def test_check_issues_a_proposition_bound_to_the_frame(runtime):
    term = eq_one(runtime)
    proposition = require_proposition(
        check_in(runtime.frames, runtime.frame.id, runtime.signature, term)
    )
    assert proposition.term is term
    assert proposition.meaning == runtime.frame.meaning


def test_a_non_proposition_sort_is_a_type_error(runtime):
    outcome = check_in(
        runtime.frames, runtime.frame.id, runtime.signature, T.number(1)
    )
    assert isinstance(outcome, Ty.IllTyped)


def test_an_undeclared_symbol_is_reported(runtime):
    foreign = T.symbol(SymbolId(10_000), "u")
    term = head_app(runtime.signature, StructuralHead.EQ, foreign, T.number(1))
    outcome = check_in(runtime.frames, runtime.frame.id, runtime.signature, term)
    assert isinstance(outcome, Ty.NeedsDeclaration)
    assert outcome.symbol_id == SymbolId(10_000)


def test_an_escaping_bound_index_is_not_a_proposition(runtime):
    term = head_app(
        runtime.signature, StructuralHead.EQ, T.BoundVar(0), T.number(1)
    )
    outcome = check_in(runtime.frames, runtime.frame.id, runtime.signature, term)
    assert isinstance(outcome, Ty.IllScoped)


def test_the_same_term_read_in_two_frames_gives_different_propositions(runtime):
    term = eq_one(runtime)
    here = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, term
    )
    child = runtime.frames.create(runtime.frame.id)
    there = proposition_in(runtime.frames, child.id, runtime.signature, term)
    assert here.term == there.term
    assert here.meaning != there.meaning
    assert here != there


def test_a_proposition_cannot_be_built_without_the_seal(runtime):
    with pytest.raises(ValueError):
        Pr.Proposition(eq_one(runtime), runtime.frame.meaning)


def test_a_proposition_cannot_be_replaced(runtime):
    proposition = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, eq_one(runtime)
    )
    with pytest.raises(ValueError, match="issued only"):
        replace(proposition, term=T.TRUE)


def test_a_boolean_literal_is_a_proposition(runtime):
    proposition = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, T.TRUE
    )
    assert proposition.term == T.TRUE


def test_propositions_are_immutable(runtime):
    proposition = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, eq_one(runtime)
    )
    with pytest.raises(AttributeError):
        proposition.term = T.TRUE


@pytest.mark.parametrize("exponent", [-2, -1, 0])
def test_nonpositive_integer_powers_record_a_nonzero_premise(
    runtime, exponent
):
    x = x_term(runtime)
    term = head_app(
        runtime.signature,
        StructuralHead.EQ,
        power(runtime, x, exponent),
        T.number(0),
    )
    proposition = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, term
    )
    assert tuple(premise.term for premise in proposition.definedness) == (
        ne_zero(runtime, x),
    )
    assert proposition.definedness[0].definedness == ()
    assert proposition.definedness[0].meaning == proposition.meaning


def test_positive_powers_literals_and_symbols_record_no_premises(runtime):
    x = x_term(runtime)
    for term in (
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            power(runtime, x, 2),
            T.number(0),
        ),
        head_app(runtime.signature, StructuralHead.EQ, x, T.number(1)),
        head_app(
            runtime.signature, StructuralHead.EQ, T.number(1), T.number(1)
        ),
        T.TRUE,
    ):
        proposition = proposition_in(
            runtime.frames, runtime.frame.id, runtime.signature, term
        )
        assert proposition.definedness == ()


def test_nested_nonpositive_powers_record_nested_premises(runtime):
    x = x_term(runtime)
    inner = power(runtime, x, -1)
    outer = power(runtime, inner, -1)
    term = head_app(
        runtime.signature, StructuralHead.EQ, outer, T.number(0)
    )
    proposition = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, term
    )
    expected_outer = ne_zero(runtime, inner)
    expected_inner = ne_zero(runtime, x)
    assert tuple(premise.term for premise in proposition.definedness) == (
        expected_outer,
        expected_inner,
    )
    assert tuple(
        premise.term
        for premise in proposition.definedness[0].definedness
    ) == (expected_inner,)
    assert proposition.definedness[1].definedness == ()


def test_boolean_and_comparison_operands_are_walked(runtime):
    x = x_term(runtime)
    powered = power(runtime, x, -1)
    expected = (ne_zero(runtime, x),)
    cases = (
        head_app(
            runtime.signature,
            StructuralHead.AND,
            head_app(
                runtime.signature,
                StructuralHead.NE,
                powered,
                T.number(0),
            ),
            T.TRUE,
        ),
        head_app(
            runtime.signature,
            StructuralHead.OR,
            head_app(
                runtime.signature,
                StructuralHead.EQ,
                powered,
                T.number(0),
            ),
            T.FALSE,
        ),
        head_app(
            runtime.signature,
            StructuralHead.NOT,
            head_app(
                runtime.signature,
                StructuralHead.EQ,
                powered,
                T.number(0),
            ),
        ),
        head_app(
            runtime.signature,
            StructuralHead.IMPLIES,
            head_app(
                runtime.signature,
                StructuralHead.EQ,
                powered,
                T.number(0),
            ),
            T.TRUE,
        ),
        head_app(
            runtime.signature, StructuralHead.LT, powered, T.number(0)
        ),
    )
    for term in cases:
        proposition = proposition_in(
            runtime.frames, runtime.frame.id, runtime.signature, term
        )
        assert tuple(
            premise.term for premise in proposition.definedness
        ) == expected


def test_guarded_and_piecewise_operands_are_walked_structurally(runtime):
    x = x_term(runtime)
    powered = power(runtime, x, -1)
    guarded = head_app(
        runtime.signature,
        StructuralHead.GUARDED,
        T.TRUE,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            powered,
            T.number(0),
        ),
    )
    piecewise = head_app(
        runtime.signature,
        StructuralHead.PIECEWISE,
        powered,
        T.TRUE,
    )
    cases = (
        guarded,
        head_app(
            runtime.signature,
            StructuralHead.EQ,
            piecewise,
            T.number(0),
        ),
    )
    for term in cases:
        proposition = proposition_in(
            runtime.frames, runtime.frame.id, runtime.signature, term
        )
        assert tuple(
            premise.term for premise in proposition.definedness
        ) == (ne_zero(runtime, x),)


def test_quoted_and_set_payloads_are_not_inspected(runtime):
    x = x_term(runtime)
    powered = power(runtime, x, -1)
    quoted_application = head_app(
        runtime.signature, StructuralHead.QUOTE, powered
    )
    quoted_term = T.quote(powered)
    members = head_app(
        runtime.signature, StructuralHead.SET, powered
    )
    for payload in (quoted_application, quoted_term, members):
        term = head_app(
            runtime.signature, StructuralHead.EQ, payload, payload
        )
        proposition = proposition_in(
            runtime.frames, runtime.frame.id, runtime.signature, term
        )
        assert proposition.definedness == ()


def test_a_declared_function_application_walks_its_arguments_only(runtime):
    f = runtime.table.intern("f")
    signature = LanguageSignature.build(
        runtime.signature.heads,
        binders=runtime.signature.binders,
        operators={
            **runtime.signature.operators,
            f: OperatorSignature((S.REAL,), S.REAL),
        },
    )
    x = x_term(runtime)
    term = head_app(
        signature,
        StructuralHead.EQ,
        T.app(T.symbol(f, "f"), power(runtime, x, -1)),
        T.number(0),
    )
    proposition = proposition_in(
        runtime.frames, runtime.frame.id, signature, term
    )
    assert tuple(
        premise.term for premise in proposition.definedness
    ) == (ne_zero(runtime, x),)


def test_a_binder_body_is_not_inspected_in_this_batch(runtime):
    signature = LanguageSignature.build(
        runtime.signature.heads,
        binders={
            "Lambda": BindingSignature("Lambda", 1, (S.REAL,)),
        },
        operators=runtime.signature.operators,
    )
    body = power(runtime, T.BoundVar(0), -1)
    binder = T.binder("Lambda", 1, body)
    term = head_app(signature, StructuralHead.EQ, binder, binder)
    outcome = check_in(
        runtime.frames, runtime.frame.id, signature, term
    )
    proposition = require_proposition(outcome)
    assert proposition.definedness == ()


def test_a_language_without_ne_refuses_to_drop_a_power_premise(runtime):
    heads = {
        symbol_id: head
        for symbol_id, head in runtime.signature.heads.items()
        if head is not StructuralHead.NE
    }
    signature = LanguageSignature.build(
        heads,
        binders=runtime.signature.binders,
        operators=runtime.signature.operators,
    )
    x = x_term(runtime)
    term = head_app(
        signature,
        StructuralHead.EQ,
        head_app(
            signature, StructuralHead.POWER, x, T.number(-1)
        ),
        T.number(0),
    )
    outcome = check_in(
        runtime.frames, runtime.frame.id, signature, term
    )
    assert isinstance(outcome, Ty.Unsupported)
    assert "inequality head" in outcome.detail


def test_a_definedness_premise_must_share_the_proposition_meaning(runtime):
    term = eq_one(runtime)
    premise = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        ne_zero(runtime, x_term(runtime)),
    )
    child = runtime.frames.create(runtime.frame.id)
    foreign = proposition_in(
        runtime.frames,
        child.id,
        runtime.signature,
        ne_zero(runtime, x_term(runtime)),
    )
    with pytest.raises(ValueError, match="meaning"):
        Pr._issue_proposition(term, runtime.frame.meaning, (foreign,))
    issued = Pr._issue_proposition(
        term, runtime.frame.meaning, (premise,)
    )
    assert issued.definedness == (premise,)


def test_a_proposition_rejects_duplicate_definedness_premises(runtime):
    term = eq_one(runtime)
    premise = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        ne_zero(runtime, x_term(runtime)),
    )
    with pytest.raises(ValueError, match="repeat"):
        Pr._issue_proposition(
            term, runtime.frame.meaning, (premise, premise)
        )


def test_a_proposition_cannot_be_its_own_definedness_premise(runtime):
    term = eq_one(runtime)
    itself = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, term
    )
    with pytest.raises(ValueError, match="its own"):
        Pr._issue_proposition(term, runtime.frame.meaning, (itself,))


def test_proposition_equality_includes_definedness(runtime):
    term = eq_one(runtime)
    premise = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        ne_zero(runtime, x_term(runtime)),
    )
    total = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, term
    )
    partial = Pr._issue_proposition(
        term, runtime.frame.meaning, (premise,)
    )
    assert total != partial
    assert len({total, partial}) == 2


def test_a_proposition_definedness_cannot_be_replaced(runtime):
    proposition = proposition_in(
        runtime.frames, runtime.frame.id, runtime.signature, eq_one(runtime)
    )
    with pytest.raises(ValueError, match="issued only"):
        replace(proposition, definedness=())
