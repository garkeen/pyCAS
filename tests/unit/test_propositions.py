"""Propositions: the seal, well-scopedness and the meaning key."""

import pytest
from support import check_in, head_app, proposition_in, require_proposition

from cas.foundation.ids import SymbolId
from cas.language import propositions as Pr
from cas.language import typing as Ty
from cas.language.signatures import StructuralHead
from cas.syntax import term as T


def eq_one(runtime) -> T.Apply:
    x = T.symbol(runtime.variable, "x")
    return head_app(runtime.signature, StructuralHead.EQ, x, T.number(1))


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
    assert isinstance(outcome, Pr.IllScoped)


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
        Pr.Proposition(eq_one(runtime), runtime.frame.meaning, object())


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
