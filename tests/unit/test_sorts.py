"""Sorts: the numeric tower, embedding, joins and shape validation."""

import pytest

from cas.language import sorts as S


def test_scalar_sorts_follow_the_numeric_tower():
    assert S.INTEGER.embeds_into(S.RATIONAL)
    assert S.RATIONAL.embeds_into(S.REAL)
    assert S.REAL.embeds_into(S.COMPLEX)
    assert S.INTEGER.embeds_into(S.COMPLEX)
    assert not S.REAL.embeds_into(S.RATIONAL)
    assert not S.COMPLEX.embeds_into(S.REAL)


def test_unknown_is_compatible_only_with_itself():
    assert S.UNKNOWN_SCALAR.embeds_into(S.UNKNOWN_SCALAR)
    assert not S.UNKNOWN_SCALAR.embeds_into(S.REAL)
    assert not S.REAL.embeds_into(S.UNKNOWN_SCALAR)


def test_non_scalars_never_embed_into_scalars():
    assert not S.PROPOSITION.embeds_into(S.REAL)
    assert not S.REAL.embeds_into(S.PROPOSITION)
    assert not S.SYNTAX.embeds_into(S.REAL)


def test_join_returns_the_least_common_sort():
    assert S.join(S.INTEGER, S.RATIONAL) is S.RATIONAL
    assert S.join(S.RATIONAL, S.INTEGER) is S.RATIONAL
    assert S.join(S.REAL, S.COMPLEX) is S.COMPLEX
    assert S.join(S.INTEGER, S.INTEGER) is S.INTEGER


def test_join_reports_no_common_sort_when_there_is_none():
    assert S.join(S.REAL, S.PROPOSITION) is None
    assert S.join(S.PROPOSITION, S.SYNTAX) is None


def test_only_integer_rational_and_real_are_ordered():
    assert S.is_ordered(S.INTEGER)
    assert S.is_ordered(S.RATIONAL)
    assert S.is_ordered(S.REAL)
    assert not S.is_ordered(S.COMPLEX)
    assert not S.is_ordered(S.UNKNOWN_SCALAR)
    assert not S.is_ordered(S.PROPOSITION)


def test_scalar_detection():
    assert S.is_scalar(S.REAL)
    assert not S.is_scalar(S.REGION)


def test_vector_and_matrix_shapes_are_validated():
    vector = S.VectorSort(S.REAL, 3)
    assert vector.element is S.REAL and vector.length == 3
    with pytest.raises(ValueError):
        S.VectorSort(S.REAL, 0)
    matrix = S.MatrixSort(S.RATIONAL, 2, 3)
    assert (matrix.rows, matrix.columns) == (2, 3)
    with pytest.raises(ValueError):
        S.MatrixSort(S.REAL, 0, 1)
    with pytest.raises(ValueError):
        S.MatrixSort(S.REAL, 1, 0)


def test_function_sorts_carry_arguments_and_result():
    function = S.FunctionSort((S.INTEGER, S.RATIONAL), S.REAL)
    assert function.arguments == (S.INTEGER, S.RATIONAL)
    assert function.result is S.REAL
    assert function == S.FunctionSort((S.INTEGER, S.RATIONAL), S.REAL)


def test_sorts_are_structural_values():
    assert S.REAL == S.ScalarSort(S.NumberSystem.REAL)
    assert hash(S.REAL) == hash(S.ScalarSort(S.NumberSystem.REAL))
    assert S.REAL != S.RATIONAL


def test_interval_sort_is_a_structural_non_scalar_sort():
    interval = S.IntervalSort()
    assert interval == S.IntervalSort()
    assert not S.is_scalar(interval)
    assert not S.is_ordered(interval)
    assert interval.embeds_into(interval)
    assert not interval.embeds_into(S.REAL)
    assert S.join(interval, interval) == interval
