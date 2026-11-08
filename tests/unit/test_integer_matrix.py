"""Integer matrices: Bareiss determinant, Hermite form and Smith form."""

import random
from itertools import permutations

import pytest

from cas.algebra.integer_matrix import IntegerMatrixSpace

SEED = 20261107


def det_by_permutations(rows):
    size = len(rows)
    total = 0
    for permutation in permutations(range(size)):
        sign = 1
        for left in range(size):
            for right in range(left + 1, size):
                if permutation[left] > permutation[right]:
                    sign = -sign
        term = sign
        for row in range(size):
            term *= rows[row][permutation[row]]
        total += term
    return total


def random_matrix(rng, rows, columns, bound=4):
    return tuple(
        tuple(rng.randint(-bound, bound) for _ in range(columns))
        for _ in range(rows)
    )


def is_unimodular(space, matrix):
    return abs(space.determinant(matrix)) == 1


def test_integer_matrix_ownership_and_shape():
    space = IntegerMatrixSpace(2, 3)
    matrix = space.matrix(((1, 2, 3), (4, 5, 6)))
    assert matrix.row_count == 2
    assert matrix.column_count == 3
    assert matrix.entry(1, 2) == 6
    with pytest.raises(ValueError):
        space.matrix(((1, 2),))
    with pytest.raises(TypeError):
        space.matrix((("x", 2, 3), (4, 5, 6)))  # type: ignore[arg-type]
    other = IntegerMatrixSpace(2, 3)
    with pytest.raises(ValueError):
        other.equal(matrix, other.zero())


def test_bareiss_determinant_matches_the_permutation_definition():
    rng = random.Random(SEED)
    for size in range(1, 5):
        space = IntegerMatrixSpace(size, size)
        for _ in range(40):
            rows = random_matrix(rng, size, size)
            matrix = space.matrix(rows)
            assert space.determinant(matrix) == det_by_permutations(rows)
    singular = IntegerMatrixSpace(3, 3).matrix(
        ((1, 2, 3), (2, 4, 6), (0, 1, 1))
    )
    assert singular.owner.determinant(singular) == 0


def test_bareiss_handles_a_zero_first_pivot_by_row_swap():
    space = IntegerMatrixSpace(2, 2)
    matrix = space.matrix(((0, 1), (1, 0)))
    assert space.determinant(matrix) == -1


def test_hermite_normal_form_has_a_unimodular_left_transform():
    rng = random.Random(SEED + 1)
    for rows in range(1, 5):
        for columns in range(1, 5):
            space = IntegerMatrixSpace(rows, columns)
            for _ in range(30):
                matrix = space.matrix(random_matrix(rng, rows, columns))
                form = space.hermite_normal_form(matrix)
                product = form.transform.owner.mul(form.transform, matrix)
                expected = product.owner.matrix(form.reduced.rows)
                assert product.owner.equal(product, expected)
                assert is_unimodular(form.transform.owner, form.transform)
                pivots = []
                zero_row_seen = False
                for row in range(rows):
                    pivot = next(
                        (
                            column
                            for column in range(columns)
                            if form.reduced.entry(row, column) != 0
                        ),
                        None,
                    )
                    if pivot is None:
                        zero_row_seen = True
                        assert all(
                            form.reduced.entry(index, column) == 0
                            for index in range(row, rows)
                            for column in range(columns)
                        )
                        continue
                    assert not zero_row_seen
                    assert form.reduced.entry(row, pivot) > 0
                    pivots.append(pivot)
                    for above in range(row):
                        entry = form.reduced.entry(above, pivot)
                        assert 0 <= entry < form.reduced.entry(row, pivot)
                assert pivots == sorted(pivots)
                assert len(set(pivots)) == len(pivots)


def test_smith_normal_form_has_unimodular_transforms_and_divides():
    rng = random.Random(SEED + 2)
    for rows in range(1, 5):
        for columns in range(1, 5):
            space = IntegerMatrixSpace(rows, columns)
            for _ in range(30):
                matrix = space.matrix(random_matrix(rng, rows, columns))
                form = space.smith_normal_form(matrix)
                left_product = form.left.owner.mul(form.left, matrix)
                product = left_product.owner.mul(left_product, form.right)
                expected = product.owner.matrix(form.diagonal.rows)
                assert product.owner.equal(product, expected)
                assert is_unimodular(form.left.owner, form.left)
                assert is_unimodular(form.right.owner, form.right)
                for row in range(rows):
                    for column in range(columns):
                        if row != column:
                            assert form.diagonal.entry(row, column) == 0
                factors = form.invariant_factors
                assert all(factor >= 0 for factor in factors)
                nonzero = [factor for factor in factors if factor != 0]
                assert all(
                    following % current == 0
                    for current, following in zip(nonzero, nonzero[1:])
                )
                assert all(
                    factor == 0 for factor in factors[len(nonzero):]
                )


def test_hermite_and_smith_forms_handle_zero_and_one_by_one_matrices():
    zero_space = IntegerMatrixSpace(3, 2)
    zero = zero_space.zero()
    hermite = zero_space.hermite_normal_form(zero)
    assert hermite.reduced.rows == zero.rows
    assert hermite.transform.owner.equal(
        hermite.transform, hermite.transform.owner.one()
    )
    smith = zero_space.smith_normal_form(zero)
    assert smith.diagonal.rows == zero.rows
    assert smith.invariant_factors == (0, 0)
    one_space = IntegerMatrixSpace(1, 1)
    negative = one_space.matrix(((-3,),))
    negative_hermite = one_space.hermite_normal_form(negative)
    assert negative_hermite.reduced.rows == ((3,),)
    negative_smith = one_space.smith_normal_form(negative)
    assert negative_smith.invariant_factors == (3,)


def test_smith_normal_form_of_known_matrices():
    space = IntegerMatrixSpace(2, 2)
    diagonal = space.smith_normal_form(space.matrix(((2, 0), (0, 3))))
    assert diagonal.invariant_factors == (1, 6)
    rank_one = space.smith_normal_form(space.matrix(((2, 4), (4, 8))))
    assert rank_one.invariant_factors == (2, 0)
    zero = space.smith_normal_form(space.zero())
    assert zero.invariant_factors == (0, 0)
    rectangular_space = IntegerMatrixSpace(2, 3)
    rectangular = rectangular_space.smith_normal_form(
        rectangular_space.matrix(((1, 2, 3), (2, 4, 6)))
    )
    assert rectangular.invariant_factors == (1, 0)


def test_normal_forms_do_not_claim_a_field_operation():
    space = IntegerMatrixSpace(2, 2)
    with pytest.raises(ValueError):
        space.determinant(IntegerMatrixSpace(2, 3).zero())
    with pytest.raises(ValueError):
        IntegerMatrixSpace(2, 3).one()
