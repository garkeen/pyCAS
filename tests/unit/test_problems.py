"""Problem specifications: fixed requests, no hidden completeness."""

import dataclasses

import pytest
from support import head_app, proposition_in

from cas.language.problems import (
    Coverage,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.signatures import StructuralHead
from cas.syntax import term as T


def specification(**overrides) -> ProblemSpec:
    values = dict(
        operation="differentiate",
        inputs=(T.number(1),),
        target=None,
        region=None,
        result_language=ResultLanguage.EXPRESSION,
        parameter_mode=ParameterMode.SPECIFIED_VALUES,
        coverage=Coverage.ONE_VERIFIED,
    )
    values.update(overrides)
    return ProblemSpec(**values)


def test_a_problem_fixes_operation_inputs_and_coverage():
    problem = specification()
    assert problem.operation == "differentiate"
    assert problem.inputs == (T.number(1),)
    assert problem.coverage is Coverage.ONE_VERIFIED
    assert problem.allows_unresolved() is False


def test_a_problem_needs_an_operation_and_an_input():
    with pytest.raises(ValueError):
        specification(operation="")
    with pytest.raises(ValueError):
        specification(inputs=())


def test_a_problem_validates_field_kinds():
    with pytest.raises(TypeError):
        specification(inputs=(1,))
    with pytest.raises(TypeError):
        specification(coverage="one_verified")
    with pytest.raises(TypeError):
        specification(result_language="expression")
    with pytest.raises(TypeError):
        specification(externalizable=(T.number(1),))


def test_a_complete_set_request_cannot_externalize_premises(runtime):
    x = T.symbol(runtime.variable, "x")
    condition = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(runtime.signature, StructuralHead.EQ, x, T.number(1)),
    )
    with pytest.raises(ValueError):
        specification(coverage=Coverage.COMPLETE_SET, externalizable=(condition,))


def test_a_sound_set_may_carry_externalized_premises(runtime):
    x = T.symbol(runtime.variable, "x")
    condition = proposition_in(
        runtime.frames,
        runtime.frame.id,
        runtime.signature,
        head_app(runtime.signature, StructuralHead.NE, x, T.number(0)),
    )
    problem = specification(
        coverage=Coverage.SOUND_SET, externalizable=(condition,)
    )
    assert problem.allows_unresolved() is True
    assert problem.externalizable == (condition,)


def test_a_problem_is_an_immutable_value():
    problem = specification()
    with pytest.raises(dataclasses.FrozenInstanceError):
        problem.operation = "integrate"
