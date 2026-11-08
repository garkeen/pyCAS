"""Exact linear algebra over Q: elimination, solutions and witnesses."""

from fractions import Fraction

import pytest

from cas.algebra.linear import (
    AffineSolution,
    Inconsistent,
    MatrixSpace,
)
from cas.algebra.rationals import RationalField

Q = RationalField()
M = MatrixSpace(Q, 2, 3)
S = MatrixSpace(Q, 2, 2)


def q(rows):
    return tuple(tuple(Fraction(entry) for entry in row) for row in rows)


def test_matrix_space_owns_shape_and_members():
    matrix = M.matrix(q(((1, 2, 3), (4, 5, 6))))
    assert matrix.row_count == 2
    assert matrix.column_count == 3
    assert matrix.entry(1, 2) == 6
    with pytest.raises(ValueError):
        M.matrix(q(((1, 2),)))
    with pytest.raises(ValueError):
        M.matrix(q(((1, 2, 3),)))
    with pytest.raises(TypeError):
        M.matrix((("x", 2, 3), (4, 5, 6)))  # type: ignore[arg-type]
    other = MatrixSpace(Q, 2, 3)
    with pytest.raises(ValueError):
        other.add(matrix, other.zero())
    assert not other.contains(matrix)


def test_rref_reports_pivots_and_a_row_transform():
    matrix = M.matrix(q(((1, 2, 3), (2, 4, 7))))
    form = M.rref(matrix)
    assert form.rank == 2
    assert form.pivots == (0, 2)
    assert form.reduced.rows == (
        (Fraction(1), Fraction(2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    product = form.transform.owner.mul(form.transform, matrix)
    expected = product.owner.matrix(form.reduced.rows)
    assert product.owner.equal(product, expected)


def test_unique_solution_and_no_free_direction():
    coefficients = S.matrix(q(((2, 1), (1, -1))))
    solution = S.solve(coefficients, (Fraction(5), Fraction(1)))
    assert isinstance(solution, AffineSolution)
    assert solution.particular == (Fraction(2), Fraction(1))
    assert solution.nullspace_basis == ()
    assert solution.rank == 2
    assert solution.pivot_columns == (0, 1)


def test_free_directions_are_complete_not_dropped():
    space = MatrixSpace(Q, 1, 2)
    coefficients = space.matrix(q(((1, -1),)))
    solution = space.solve(coefficients, (Fraction(2),))
    assert isinstance(solution, AffineSolution)
    assert solution.rank == 1
    assert solution.particular == (Fraction(2), Fraction(0))
    assert solution.nullspace_basis == ((Fraction(1), Fraction(1)),)
    for row in coefficients.rows:
        assert sum(
            (coefficient * entry
             for coefficient, entry in zip(row, solution.particular)),
            Fraction(0),
        ) == 2
        assert sum(
            (coefficient * entry
             for coefficient, entry in zip(row, solution.nullspace_basis[0])),
            Fraction(0),
        ) == 0


def test_inconsistent_system_carries_a_row_combination_witness():
    coefficients = S.matrix(q(((1, 1), (1, 1))))
    solution = S.solve(coefficients, (Fraction(1), Fraction(2)))
    assert isinstance(solution, Inconsistent)
    witness = solution.witness
    assert len(witness) == 2
    combined = [
        Q.add(Q.mul(witness[0], coefficients.rows[0][column]),
              Q.mul(witness[1], coefficients.rows[1][column]))
        for column in range(2)
    ]
    assert combined == [Fraction(0), Fraction(0)]
    rhs = Q.add(
        Q.mul(witness[0], Fraction(1)), Q.mul(witness[1], Fraction(2))
    )
    assert rhs != 0


def test_nullspace_basis_annihilates_the_matrix():
    matrix = M.matrix(q(((1, 2, 3), (2, 4, 6))))
    basis = M.nullspace(matrix)
    assert len(basis) == 2
    for vector in basis:
        for row in matrix.rows:
            assert sum(
                (coefficient * entry for coefficient, entry in zip(row, vector)),
                Fraction(0),
            ) == 0


def test_determinant_and_inverse_are_exact():
    matrix = S.matrix(q(((2, 1), (1, 3))))
    assert S.determinant(matrix) == 5
    inverse = S.inverse(matrix)
    product = S.mul(matrix, inverse)
    assert product.owner.equal(product, product.owner.matrix(S.one().rows))
    singular = S.matrix(q(((1, 2), (2, 4))))
    assert S.determinant(singular) == 0
    with pytest.raises(ZeroDivisionError):
        S.inverse(singular)


def test_matrix_equality_uses_the_owning_field():
    left = S.matrix(q(((Fraction(1, 2), 0), (0, 1))))
    right = S.matrix(q(((Fraction(2, 4), 0), (0, 1))))
    assert S.equal(left, right)


def matvec(space, matrix, vector):
    field = space.field
    return tuple(
        sum(
            (field.mul(entry, coefficient)
             for entry, coefficient in zip(row, vector)),
            field.zero(),
        )
        for row in matrix.rows
    )


def test_random_solutions_and_determinants_obey_their_contracts():
    import random

    rng = random.Random(20261105)
    space = MatrixSpace(Q, 3, 3)
    for _ in range(40):
        rows = tuple(
            tuple(Fraction(rng.randint(-5, 5)) for _ in range(3))
            for _ in range(3)
        )
        matrix = space.matrix(rows)
        source = tuple(Fraction(rng.randint(-5, 5)) for _ in range(3))
        rhs = matvec(space, matrix, source)
        solution = space.solve(matrix, rhs)
        assert isinstance(solution, AffineSolution)
        assert matvec(space, matrix, solution.particular) == rhs
        for vector in solution.nullspace_basis:
            assert matvec(space, matrix, vector) == (
                Fraction(0), Fraction(0), Fraction(0)
            )
        difference = tuple(
            source[index] - solution.particular[index] for index in range(3)
        )
        assert matvec(space, matrix, difference) == (
            Fraction(0), Fraction(0), Fraction(0)
        )

        second = space.matrix(
            tuple(
                tuple(Fraction(rng.randint(-5, 5)) for _ in range(3))
                for _ in range(3)
            )
        )
        product = space.mul(matrix, second)
        assert product.owner.determinant(product) == (
            space.determinant(matrix) * space.determinant(second)
        )
        transposed = space.transpose(matrix)
        assert space.rank(matrix) == transposed.owner.rank(transposed)
