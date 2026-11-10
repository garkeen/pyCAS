"""Typed expressions and typed problem inputs."""

from dataclasses import replace

import pytest
from support import head_app, typed_in, variable

from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    VariableRoles,
)
from cas.language.sets import set_term
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import bootstrap
from cas.semantics.frames import Declaration, Definition
from cas.syntax import term as T


def _plus_one(runtime, term):
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        term,
        T.number(1),
    )


def _problem(runtime, *inputs):
    return ProblemSpec(
        "differentiate",
        tuple(inputs),
        VariableRoles(
            runtime.variable,
            (),
            ParameterMode.SPECIFIED_VALUES,
            runtime.world.id,
            S.REAL,
        ),
        None,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=runtime.request.value_domain,
        ),
    )


def test_a_typed_expression_carries_term_sort_meaning_and_free_symbols(runtime):
    term = _plus_one(runtime, variable(runtime))
    typed = typed_in(
        runtime.frames, runtime.frame.id, runtime.signature, term
    )
    assert typed.term == term
    assert typed.sort is S.REAL
    assert typed.meaning == runtime.frame.meaning
    assert typed.bindings.symbols == (
        Ty.FreeSymbol(runtime.variable, S.REAL),
    )


def test_alias_expansion_precedes_typing_and_binding(runtime):
    alias = runtime.table.intern("typed_alias")
    frame = runtime.frames.create(
        runtime.frame.id,
        definitions=(Definition(alias, "typed_alias", variable(runtime)),),
    )
    term = _plus_one(runtime, T.symbol(alias, "typed_alias"))
    typed = typed_in(runtime.frames, frame.id, runtime.signature, term)
    assert typed.term == _plus_one(runtime, variable(runtime))
    assert typed.meaning == frame.meaning
    assert typed.bindings.symbols == (
        Ty.FreeSymbol(runtime.variable, S.REAL),
    )


def test_a_typed_expression_cannot_be_constructed_directly(runtime):
    with pytest.raises(ValueError):
        Ty.TypedExpr(
            variable(runtime),
            S.REAL,
            runtime.frame.meaning,
            Ty.BindingView(),
        )


def test_a_typed_expression_cannot_be_replaced(runtime):
    typed = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        variable(runtime),
    )
    with pytest.raises(ValueError, match="issued only"):
        replace(typed, sort=S.INTEGER)


def test_a_forged_typed_expression_cannot_enter_a_problem(runtime):
    typed = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        variable(runtime),
    )
    forged = object.__new__(Ty.TypedExpr)
    for name in ("term", "sort", "meaning", "bindings"):
        object.__setattr__(forged, name, getattr(typed, name))
    with pytest.raises(ValueError, match="issued only"):
        _problem(runtime, forged)


def test_the_empty_set_sort_is_distinct_from_a_nonempty_unknown_set(runtime):
    empty = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        set_term(runtime.signature, ()),
    )
    unknown_members = S.SetSort(S.UNKNOWN_SCALAR, empty=False)
    empty_sort = S.SetSort(S.UNKNOWN_SCALAR, empty=True)
    assert empty.sort == empty_sort
    assert empty.sort.embeds_into(S.SetSort(S.REAL))
    assert not unknown_members.embeds_into(S.SetSort(S.REAL))
    assert not S.SetSort(S.REAL).embeds_into(unknown_members)
    assert not S.SetSort(S.REAL).embeds_into(empty_sort)
    assert S.join(empty_sort, S.SetSort(S.REAL)) == S.SetSort(S.REAL)
    assert S.join(S.SetSort(S.REAL), empty_sort) == S.SetSort(S.REAL)
    assert S.join(empty_sort, empty_sort) == empty_sort
    assert S.join(
        S.SetSort(S.INTEGER), S.SetSort(S.RATIONAL)
    ) == S.SetSort(S.RATIONAL, empty=False)
    with pytest.raises(ValueError):
        S.SetSort(S.REAL, empty=True)


def test_a_nonempty_unknown_scalar_set_is_not_the_empty_set(runtime):
    extra = runtime.table.intern("unknown_member")
    frame = runtime.frames.create(
        runtime.frame.id,
        declarations=(
            Declaration(extra, "unknown_member", S.UNKNOWN_SCALAR),
        ),
    )
    term = set_term(
        runtime.signature, (T.symbol(extra, "unknown_member"),)
    )
    typed = typed_in(runtime.frames, frame.id, runtime.signature, term)
    assert typed.sort == S.SetSort(S.UNKNOWN_SCALAR, empty=False)
    assert not typed.sort.embeds_into(S.SetSort(S.REAL))


def test_a_problem_input_is_a_typed_expression(runtime):
    typed = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        variable(runtime),
    )
    problem = _problem(runtime, typed)
    assert problem.inputs == (typed,)
    with pytest.raises(TypeError):
        _problem(runtime, variable(runtime))


def test_a_problem_rejects_inputs_from_two_worlds(runtime):
    typed = typed_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        variable(runtime),
    )
    other = bootstrap()
    foreign = typed_in(
        other.frames,
        other.frame.id,
        other.signature,
        variable(other),
    )
    with pytest.raises(ValueError):
        _problem(runtime, typed, foreign)
