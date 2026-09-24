"""Linear algebra over an explicit coefficient field."""

from __future__ import annotations

from collections.abc import Sequence
from typing import TypeAlias

from cas.math.domains.base import DomainElement, Ring, RingError

CoefficientRow: TypeAlias = list[DomainElement]
Matrix: TypeAlias = list[CoefficientRow]


def _copy(rows: Sequence[Sequence[DomainElement]]) -> Matrix:
    return [list(row) for row in rows]


def echelon(
    ring: Ring,
    rows: Sequence[Sequence[DomainElement]],
    ncols: int | None = None,
) -> tuple[Matrix, list[int]]:
    """Return row-echelon form and pivot columns over a field."""
    if not ring.is_field:
        raise RingError("row elimination requires field coefficients")
    matrix = _copy(rows)
    row_count = len(matrix)
    width = len(matrix[0]) if matrix else 0
    column_count = width if ncols is None else ncols
    pivots: list[int] = []
    pivot_row = 0
    for column in range(column_count):
        if pivot_row >= row_count:
            break
        pivot: int | None = None
        for index in range(pivot_row, row_count):
            if not ring.is_zero(matrix[index][column]):
                pivot = index
                break
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        inverse = ring.div_exact(ring.from_int(1), matrix[pivot_row][column])
        matrix[pivot_row] = [
            ring.mul(value, inverse) for value in matrix[pivot_row]
        ]
        for index in range(row_count):
            if index == pivot_row or ring.is_zero(matrix[index][column]):
                continue
            factor = matrix[index][column]
            matrix[index] = [
                ring.sub(matrix[index][column_index], ring.mul(factor, matrix[pivot_row][column_index]))
                for column_index in range(width)
            ]
        pivots.append(column)
        pivot_row += 1
    return matrix, pivots


def rank(ring: Ring, rows: Sequence[Sequence[DomainElement]]) -> int:
    _, pivots = echelon(ring, rows)
    return len(pivots)


def nullspace(
    ring: Ring,
    rows: Sequence[Sequence[DomainElement]],
) -> list[tuple[DomainElement, ...]]:
    """Return a basis for the nullspace of a matrix."""
    matrix, pivots = echelon(ring, rows)
    column_count = len(matrix[0]) if matrix else 0
    free_columns = [
        column for column in range(column_count) if column not in pivots
    ]
    basis: list[tuple[DomainElement, ...]] = []
    for free_column in free_columns:
        vector: list[DomainElement] = [ring.from_int(0)] * column_count
        vector[free_column] = ring.from_int(1)
        for row_index, pivot_column in enumerate(pivots):
            vector[pivot_column] = ring.neg(matrix[row_index][free_column])
        basis.append(tuple(vector))
    return basis


def solve_system(
    ring: Ring,
    rows: Sequence[Sequence[DomainElement]],
    right_hand_side: Sequence[DomainElement],
) -> tuple[tuple[DomainElement, ...], list[tuple[DomainElement, ...]]] | None:
    """Solve ``Ax = b`` or return ``None`` for an inconsistent system."""
    augmented = [
        list(row) + [value]
        for row, value in zip(rows, right_hand_side)
    ]
    column_count = len(rows[0]) if rows else 0
    matrix, pivots = echelon(ring, augmented, ncols=column_count)
    for row_index, row in enumerate(matrix):
        if row_index >= len(pivots) and all(
            ring.is_zero(value) for value in row[:column_count]
        ):
            if not ring.is_zero(row[column_count]):
                return None
    particular: list[DomainElement] = [ring.from_int(0)] * column_count
    for row_index, pivot_column in enumerate(pivots):
        particular[pivot_column] = matrix[row_index][column_count]
    return tuple(particular), nullspace(ring, rows)


def det_bareiss(matrix: Sequence[Sequence[int]]) -> int:
    """Compute an integer determinant with fraction-free Bareiss elimination."""
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("not a square matrix")
    if size == 0:
        return 1
    work: list[list[int]] = [list(row) for row in matrix]
    sign = 1
    previous = 1
    for index in range(size - 1):
        if work[index][index] == 0:
            swap = next(
                (row for row in range(index + 1, size) if work[row][index] != 0),
                None,
            )
            if swap is None:
                return 0
            work[index], work[swap] = work[swap], work[index]
            sign = -sign
        for row in range(index + 1, size):
            for column in range(index + 1, size):
                numerator = (
                    work[index][index] * work[row][column]
                    - work[row][index] * work[index][column]
                )
                if numerator % previous != 0:
                    raise ArithmeticError("Bareiss divisibility violated")
                work[row][column] = numerator // previous
        previous = work[index][index]
    return sign * work[size - 1][size - 1]
