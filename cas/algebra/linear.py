"""Exact linear algebra over one field.

A matrix belongs to a `MatrixSpace`; the space owns the field, the shape and the
equality relation.  One reduced row-echelon computation serves rank, affine
solutions, nullspace bases and inconsistency witnesses, as required by the
architecture: callers do not run elimination separately for each query.

The solution result is a closed union:

    Inconsistent(witness)                 -- a row combination proving 0 = c != 0
    AffineSolution(particular, nullspace) -- the complete affine solution set

Over a field the affine description is complete: every solution is the
particular solution plus a linear combination of the nullspace basis.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Generic, Sequence, TypeAlias, TypeVar

from cas.algebra.protocols import Field

E = TypeVar("E")

_SEAL = object()

Vector = tuple[E, ...]


@dataclass(frozen=True, slots=True, eq=False)
class Matrix(Generic[E]):
    """An immutable matrix owned by one space."""

    owner: MatrixSpace[E]
    rows: tuple[Vector[E], ...]
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError("a matrix is issued only by its space")

    @property
    def row_count(self) -> int:
        return len(self.rows)

    @property
    def column_count(self) -> int:
        return self.owner.columns

    def entry(self, row: int, column: int) -> E:
        return self.rows[row][column]


@dataclass(frozen=True, slots=True)
class EchelonForm(Generic[E]):
    """One elimination result shared by every query on the same matrix.

    `transform * matrix == reduced`, `pivots` lists the pivot columns, and
    `rank` is the number of pivots.  The transform is kept because an
    inconsistency witness is a row of it, not a second elimination.
    """

    reduced: Matrix[E]
    transform: Matrix[E]
    pivots: tuple[int, ...]
    rank: int


@dataclass(frozen=True, slots=True)
class Inconsistent(Generic[E]):
    """The system has no solution; `witness` is a row combination of `A`.

    `witness` has one entry per row of `A`; its combination of the rows of `A`
    is zero while the same combination of `b` is nonzero.
    """

    witness: Vector[E]


@dataclass(frozen=True, slots=True)
class AffineSolution(Generic[E]):
    """A particular solution and a basis of the nullspace.

    `rank` and `pivot_columns` are the rank witness: the number of pivots is the
    dimension of the row space, and the free columns generate every direction of
    the nullspace.  `nullspace_basis` is empty exactly when the solution is
    unique.
    """

    particular: Vector[E]
    nullspace_basis: tuple[Vector[E], ...]
    rank: int
    pivot_columns: tuple[int, ...]


LinearSolution: TypeAlias = Inconsistent[E] | AffineSolution[E]


class MatrixSpace(Generic[E]):
    """`M_{rows x columns}(F)` for one explicit field `F`."""

    __slots__ = ("_field", "_rows", "_columns")

    def __init__(self, field: Field[E], rows: int, columns: int) -> None:
        if not isinstance(field, Field):
            raise TypeError("a matrix space needs a field")
        if rows < 1 or columns < 1:
            raise ValueError("a matrix space needs a positive shape")
        self._field = field
        self._rows = rows
        self._columns = columns

    @property
    def field(self) -> Field[E]:
        return self._field

    @property
    def rows(self) -> int:
        return self._rows

    @property
    def columns(self) -> int:
        return self._columns

    def contains(self, value: object) -> bool:
        return isinstance(value, Matrix) and value.owner is self

    def _own(self, value: Matrix[E]) -> None:
        if value.owner is not self:
            raise ValueError("a matrix belongs to another space")

    def _make(self, rows: Sequence[Sequence[E]]) -> Matrix[E]:
        if len(rows) != self._rows:
            raise ValueError(
                f"expected {self._rows} rows, got {len(rows)}"
            )
        materialized: list[Vector[E]] = []
        for row in rows:
            entries = tuple(row)
            if len(entries) != self._columns:
                raise ValueError(
                    f"expected {self._columns} columns, got {len(entries)}"
                )
            if any(not self._field.contains(entry) for entry in entries):
                raise TypeError("a matrix entry is not a field member")
            materialized.append(entries)
        return Matrix(self, tuple(materialized), _SEAL)

    # --- construction ---

    def zero(self) -> Matrix[E]:
        zero = self._field.zero()
        return self._make(
            tuple(tuple(zero for _ in range(self._columns))
                  for _ in range(self._rows))
        )

    def one(self) -> Matrix[E]:
        if self._rows != self._columns:
            raise ValueError("a multiplicative identity needs a square space")
        zero = self._field.zero()
        one = self._field.one()
        return self._make(
            tuple(
                tuple(one if row == column else zero for column in range(self._columns))
                for row in range(self._rows)
            )
        )

    def matrix(self, rows: Sequence[Sequence[E]]) -> Matrix[E]:
        return self._make(rows)

    # --- ring operations ---

    def add(self, left: Matrix[E], right: Matrix[E]) -> Matrix[E]:
        self._own(left)
        self._own(right)
        field = self._field
        return self._make(
            tuple(
                tuple(field.add(a, b) for a, b in zip(left_row, right_row))
                for left_row, right_row in zip(left.rows, right.rows)
            )
        )

    def neg(self, value: Matrix[E]) -> Matrix[E]:
        self._own(value)
        field = self._field
        return self._make(
            tuple(tuple(field.neg(entry) for entry in row) for row in value.rows)
        )

    def sub(self, left: Matrix[E], right: Matrix[E]) -> Matrix[E]:
        return self.add(left, self.neg(right))

    def scalar_mul(self, scalar: E, value: Matrix[E]) -> Matrix[E]:
        self._own(value)
        field = self._field
        return self._make(
            tuple(tuple(field.mul(scalar, entry) for entry in row)
                  for row in value.rows)
        )

    def mul(self, left: Matrix[E], right: Matrix[E]) -> Matrix[E]:
        self._own(left)
        if not isinstance(right, Matrix):
            raise TypeError("a matrix product needs two matrices")
        if right.owner.field is not self._field:
            raise ValueError("matrix factors live over different fields")
        if right.row_count != self._columns:
            raise ValueError("matrix shapes do not compose")
        target = MatrixSpace(self._field, self._rows, right.column_count)
        field = self._field
        product = []
        for row in left.rows:
            entries = []
            for column in range(right.column_count):
                total = field.zero()
                for index in range(self._columns):
                    total = field.add(
                        total,
                        field.mul(row[index], right.rows[index][column]),
                    )
                entries.append(total)
            product.append(tuple(entries))
        return target._make(product)

    def equal(self, left: Matrix[E], right: Matrix[E]) -> bool:
        self._own(left)
        self._own(right)
        field = self._field
        return all(
            field.equal(a, b)
            for left_row, right_row in zip(left.rows, right.rows)
            for a, b in zip(left_row, right_row)
        )

    def transpose(self, value: Matrix[E]) -> Matrix[E]:
        self._own(value)
        target = MatrixSpace(self._field, self._columns, self._rows)
        return target._make(
            tuple(
                tuple(value.rows[row][column] for row in range(self._rows))
                for column in range(self._columns)
            )
        )

    # --- elimination ---

    def rref(self, value: Matrix[E]) -> EchelonForm[E]:
        """Reduced row-echelon form and the row operations that produced it."""
        self._own(value)
        field = self._field
        rows = [list(row) for row in value.rows]
        transform = [
            [field.one() if row == column else field.zero()
             for column in range(self._rows)]
            for row in range(self._rows)
        ]
        pivots: list[int] = []
        pivot_row = 0
        for column in range(self._columns):
            source = next(
                (
                    row
                    for row in range(pivot_row, self._rows)
                    if not field.is_zero(rows[row][column])
                ),
                None,
            )
            if source is None:
                continue
            if source != pivot_row:
                rows[pivot_row], rows[source] = rows[source], rows[pivot_row]
                transform[pivot_row], transform[source] = (
                    transform[source],
                    transform[pivot_row],
                )
            pivot = rows[pivot_row][column]
            inverse = field.inv(pivot)
            rows[pivot_row] = [
                field.mul(inverse, entry) for entry in rows[pivot_row]
            ]
            transform[pivot_row] = [
                field.mul(inverse, entry)
                for entry in transform[pivot_row]
            ]
            for row in range(self._rows):
                if row == pivot_row:
                    continue
                factor = rows[row][column]
                if field.is_zero(factor):
                    continue
                rows[row] = [
                    field.sub(
                        rows[row][index],
                        field.mul(factor, rows[pivot_row][index]),
                    )
                    for index in range(self._columns)
                ]
                transform[row] = [
                    field.sub(
                        transform[row][index],
                        field.mul(factor, transform[pivot_row][index]),
                    )
                    for index in range(self._rows)
                ]
            pivots.append(column)
            pivot_row += 1
            if pivot_row == self._rows:
                break
        reduced = self._make(rows)
        transform_matrix = MatrixSpace(
            field, self._rows, self._rows
        )._make(transform)
        return EchelonForm(
            reduced, transform_matrix, tuple(pivots), len(pivots)
        )

    def rank(self, value: Matrix[E]) -> int:
        return self.rref(value).rank

    def solve(self, coefficients: Matrix[E], rhs: Sequence[E]) -> LinearSolution[E]:
        """Solve `coefficients * x = rhs` completely over the field."""
        self._own(coefficients)
        values = tuple(rhs)
        if len(values) != self._rows:
            raise ValueError("the right-hand side has the wrong length")
        if any(not self._field.contains(value) for value in values):
            raise TypeError("a right-hand side entry is not a field member")
        augmented_space = MatrixSpace(
            self._field, self._rows, self._columns + 1
        )
        augmented = augmented_space._make(
            tuple(
                tuple(coefficients.rows[row]) + (values[row],)
                for row in range(self._rows)
            )
        )
        form = augmented_space.rref(augmented)
        reduced = form.reduced
        for row in range(self._rows):
            left = reduced.rows[row][: self._columns]
            value = reduced.rows[row][self._columns]
            if all(self._field.is_zero(entry) for entry in left) and not (
                self._field.is_zero(value)
            ):
                witness = tuple(
                    form.transform.rows[row][index]
                    for index in range(self._rows)
                )
                return Inconsistent(witness)

        particular = [self._field.zero() for _ in range(self._columns)]
        pivot_rows: dict[int, int] = {}
        for row, column in enumerate(form.pivots):
            if column >= self._columns:
                continue
            pivot_rows[column] = row
            particular[column] = reduced.rows[row][self._columns]
        free_columns = tuple(
            column
            for column in range(self._columns)
            if column not in pivot_rows
        )
        basis: list[Vector[E]] = []
        for free in free_columns:
            vector = [self._field.zero() for _ in range(self._columns)]
            vector[free] = self._field.one()
            for pivot, row in pivot_rows.items():
                vector[pivot] = self._field.neg(
                    reduced.rows[row][free]
                )
            basis.append(tuple(vector))
        return AffineSolution(
            tuple(particular),
            tuple(basis),
            len(form.pivots),
            tuple(form.pivots),
        )

    def nullspace(self, value: Matrix[E]) -> tuple[Vector[E], ...]:
        solution = self.solve(
            value, tuple(self._field.zero() for _ in range(self._rows))
        )
        if isinstance(solution, Inconsistent):
            raise AssertionError("a homogeneous system cannot be inconsistent")
        return solution.nullspace_basis

    def determinant(self, value: Matrix[E]) -> E:
        """Determinant by field elimination; the zero matrix has determinant 0."""
        self._own(value)
        if self._rows != self._columns:
            raise ValueError("a determinant needs a square matrix")
        field = self._field
        rows = [list(row) for row in value.rows]
        sign = 1
        determinant = field.one()
        for column in range(self._columns):
            source = next(
                (
                    row
                    for row in range(column, self._rows)
                    if not field.is_zero(rows[row][column])
                ),
                None,
            )
            if source is None:
                return field.zero()
            if source != column:
                rows[column], rows[source] = rows[source], rows[column]
                sign = -sign
            pivot = rows[column][column]
            determinant = field.mul(determinant, pivot)
            for row in range(column + 1, self._rows):
                factor = field.div(rows[row][column], pivot)
                if field.is_zero(factor):
                    continue
                for index in range(column, self._columns):
                    rows[row][index] = field.sub(
                        rows[row][index],
                        field.mul(factor, rows[column][index]),
                    )
        return determinant if sign > 0 else field.neg(determinant)

    def inverse(self, value: Matrix[E]) -> Matrix[E]:
        """Inverse by the same elimination; raises on a singular matrix."""
        self._own(value)
        if self._rows != self._columns:
            raise ValueError("an inverse needs a square matrix")
        field = self._field
        augmented_space = MatrixSpace(
            field, self._rows, self._columns * 2
        )
        augmented = augmented_space._make(
            tuple(
                tuple(value.rows[row])
                + tuple(
                    field.one() if row == column else field.zero()
                    for column in range(self._columns)
                )
                for row in range(self._rows)
            )
        )
        form = augmented_space.rref(augmented)
        left_rank = sum(
            1 for pivot in form.pivots if pivot < self._columns
        )
        if left_rank < self._columns:
            raise ZeroDivisionError("a singular matrix has no inverse")
        target = MatrixSpace(field, self._rows, self._columns)
        return target._make(
            tuple(
                tuple(form.reduced.rows[row][self._columns :])
                for row in range(self._rows)
            )
        )


__all__ = [
    "AffineSolution",
    "EchelonForm",
    "Inconsistent",
    "LinearSolution",
    "Matrix",
    "MatrixSpace",
]
