"""Integer matrices, fraction-free elimination and normal forms.

`Z` is a Euclidean ring, not a field, so an integer matrix is a different
parent from `MatrixSpace` over a field: unimodular row/column operations replace
field elimination, and the canonical forms are Hermite and Smith forms rather
than RREF.

The algorithms are the standard integer-matrix algorithms:

- Bareiss fraction-free elimination for the determinant
  (Bareiss, "Sylvester's identity and multistep integer-preserving Gaussian
  elimination", Math. Comp. 22 (1968); Cohen, *A Course in Computational
  Algebraic Number Theory*, Algorithm 2.2.6).
- Row Hermite normal form by gcd elimination with a recorded unimodular left
  transform (Cohen, §2.4.2; FriCAS `src/algebra/smith.spad`).
- Smith normal form by repeated gcd row/column elimination
  (Cohen, §2.4.3; FriCAS `src/algebra/smith.spad` and `smith2.spad`).

The normal forms return the transformations that were actually applied:
`U*A == H` for the Hermite form and `U*A*V == D` for the Smith form.  The
transformations are checked to be unimodular by the tests; a caller can verify
them independently with `determinant`.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

from cas.algebra.integers import IntegerRing

_SEAL = object()

Rows = tuple[tuple[int, ...], ...]


@dataclass(frozen=True, slots=True, eq=False)
class IntegerMatrix:
    """An immutable matrix over `Z`, owned by one integer matrix space."""

    owner: IntegerMatrixSpace
    rows: Rows
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError("an integer matrix is issued only by its space")

    @property
    def row_count(self) -> int:
        return len(self.rows)

    @property
    def column_count(self) -> int:
        return self.owner.columns

    def entry(self, row: int, column: int) -> int:
        return self.rows[row][column]


@dataclass(frozen=True, slots=True)
class HermiteForm:
    """`U*A == H`, with `H` in row Hermite normal form."""

    reduced: IntegerMatrix
    transform: IntegerMatrix

    def __post_init__(self) -> None:
        if self.reduced.row_count != self.transform.row_count:
            raise ValueError("the Hermite transform has the wrong row count")
        if self.transform.row_count != self.transform.column_count:
            raise ValueError("the Hermite transform must be square")


@dataclass(frozen=True, slots=True)
class SmithForm:
    """`U*A*V == D`, with `D` diagonal and `d_i | d_{i+1}`."""

    diagonal: IntegerMatrix
    left: IntegerMatrix
    right: IntegerMatrix

    def __post_init__(self) -> None:
        rows = self.diagonal.row_count
        columns = self.diagonal.column_count
        if self.left.row_count != rows or self.left.column_count != rows:
            raise ValueError("the Smith left transform has the wrong shape")
        if self.right.row_count != columns or self.right.column_count != columns:
            raise ValueError("the Smith right transform has the wrong shape")

    @property
    def invariant_factors(self) -> tuple[int, ...]:
        """The diagonal entries, including trailing zeros."""
        size = min(self.diagonal.row_count, self.diagonal.column_count)
        return tuple(self.diagonal.entry(index, index) for index in range(size))


class IntegerMatrixSpace:
    """`M_{rows x columns}(Z)` for one explicit shape."""

    __slots__ = ("_rows", "_columns", "_ring")

    def __init__(self, rows: int, columns: int) -> None:
        if rows < 1 or columns < 1:
            raise ValueError("an integer matrix space needs a positive shape")
        self._rows = rows
        self._columns = columns
        self._ring = IntegerRing()

    @property
    def ring(self) -> IntegerRing:
        return self._ring

    @property
    def rows(self) -> int:
        return self._rows

    @property
    def columns(self) -> int:
        return self._columns

    def contains(self, value: object) -> bool:
        return isinstance(value, IntegerMatrix) and value.owner is self

    def _own(self, value: IntegerMatrix) -> None:
        if value.owner is not self:
            raise ValueError("an integer matrix belongs to another space")

    def _make(self, rows: Sequence[Sequence[int]]) -> IntegerMatrix:
        if len(rows) != self._rows:
            raise ValueError(f"expected {self._rows} rows, got {len(rows)}")
        materialized: list[tuple[int, ...]] = []
        for row in rows:
            entries = tuple(row)
            if len(entries) != self._columns:
                raise ValueError(
                    f"expected {self._columns} columns, got {len(entries)}"
                )
            if any(
                not isinstance(entry, int) or isinstance(entry, bool)
                for entry in entries
            ):
                raise TypeError("an integer matrix entry is not an integer")
            materialized.append(entries)
        return IntegerMatrix(self, tuple(materialized), _SEAL)

    # --- construction and ring operations ---

    def zero(self) -> IntegerMatrix:
        return self._make(
            tuple(tuple(0 for _ in range(self._columns))
                  for _ in range(self._rows))
        )

    def one(self) -> IntegerMatrix:
        if self._rows != self._columns:
            raise ValueError("a multiplicative identity needs a square space")
        return self._make(
            tuple(
                tuple(1 if row == column else 0
                      for column in range(self._columns))
                for row in range(self._rows)
            )
        )

    def matrix(self, rows: Sequence[Sequence[int]]) -> IntegerMatrix:
        return self._make(rows)

    def equal(self, left: IntegerMatrix, right: IntegerMatrix) -> bool:
        self._own(left)
        self._own(right)
        return left.rows == right.rows

    def mul(
        self,
        left: IntegerMatrix,
        right: IntegerMatrix,
    ) -> IntegerMatrix:
        self._own(left)
        if not isinstance(right, IntegerMatrix):
            raise TypeError("an integer matrix product needs two matrices")
        if right.row_count != self._columns:
            raise ValueError("integer matrix shapes do not compose")
        target = IntegerMatrixSpace(self._rows, right.column_count)
        product: list[list[int]] = []
        for row in left.rows:
            entries: list[int] = []
            for column in range(right.column_count):
                entries.append(
                    sum(
                        row[index] * right.rows[index][column]
                        for index in range(self._columns)
                    )
                )
            product.append(entries)
        return target._make(product)

    def transpose(self, value: IntegerMatrix) -> IntegerMatrix:
        self._own(value)
        target = IntegerMatrixSpace(self._columns, self._rows)
        return target._make(
            tuple(
                tuple(value.rows[row][column] for row in range(self._rows))
                for column in range(self._columns)
            )
        )

    # --- fraction-free determinant ---

    def determinant(self, value: IntegerMatrix) -> int:
        """Bareiss fraction-free determinant of a square integer matrix.

        Every intermediate division is exact.  A zero pivot is resolved by a
        row swap; if no nonzero entry remains in the column, the determinant is
        zero.
        """
        self._own(value)
        if self._rows != self._columns:
            raise ValueError("a determinant needs a square matrix")
        size = self._rows
        work = [list(row) for row in value.rows]
        sign = 1
        previous = 1
        for column in range(size - 1):
            if work[column][column] == 0:
                source = next(
                    (
                        row
                        for row in range(column + 1, size)
                        if work[row][column] != 0
                    ),
                    None,
                )
                if source is None:
                    return 0
                work[column], work[source] = work[source], work[column]
                sign = -sign
            pivot = work[column][column]
            for row in range(column + 1, size):
                for inner in range(column + 1, size):
                    numerator = (
                        work[row][inner] * pivot
                        - work[row][column] * work[column][inner]
                    )
                    if numerator % previous != 0:
                        raise AssertionError(
                            "Bareiss elimination lost exact divisibility"
                        )
                    work[row][inner] = numerator // previous
            previous = pivot
        return sign * work[size - 1][size - 1]

    # --- Hermite normal form ---

    def hermite_normal_form(self, value: IntegerMatrix) -> HermiteForm:
        """Row Hermite normal form with `U*A == H`.

        The reduced matrix has zero rows at the bottom, strictly increasing
        pivot columns, positive pivots, and entries above each pivot reduced
        into `[0, pivot)`.  The left transform is unimodular because every step
        is a row swap, sign change or a Bezout row combination with
        determinant one.
        """
        self._own(value)
        rows, columns = self._rows, self._columns
        reduced = [list(row) for row in value.rows]
        transform = [
            [1 if row == column else 0 for column in range(rows)]
            for row in range(rows)
        ]
        ring = self._ring
        pivot_row = 0
        for column in range(columns):
            if pivot_row >= rows:
                break
            source = next(
                (
                    row
                    for row in range(pivot_row, rows)
                    if reduced[row][column] != 0
                ),
                None,
            )
            if source is None:
                continue
            if source != pivot_row:
                reduced[pivot_row], reduced[source] = (
                    reduced[source],
                    reduced[pivot_row],
                )
                transform[pivot_row], transform[source] = (
                    transform[source],
                    transform[pivot_row],
                )
            row = pivot_row + 1
            while row < rows:
                if reduced[row][column] == 0:
                    row += 1
                    continue
                left = reduced[pivot_row][column]
                right = reduced[row][column]
                gcd, first, second = ring.xgcd(left, right)
                old_pivot = reduced[pivot_row][:]
                old_row = reduced[row][:]
                reduced[pivot_row] = [
                    first * old_pivot[index] + second * old_row[index]
                    for index in range(columns)
                ]
                reduced[row] = [
                    (-right // gcd) * old_pivot[index]
                    + (left // gcd) * old_row[index]
                    for index in range(columns)
                ]
                old_transform_pivot = transform[pivot_row][:]
                old_transform_row = transform[row][:]
                transform[pivot_row] = [
                    first * old_transform_pivot[index]
                    + second * old_transform_row[index]
                    for index in range(rows)
                ]
                transform[row] = [
                    (-right // gcd) * old_transform_pivot[index]
                    + (left // gcd) * old_transform_row[index]
                    for index in range(rows)
                ]
                row += 1
            if reduced[pivot_row][column] < 0:
                reduced[pivot_row] = [
                    -entry for entry in reduced[pivot_row]
                ]
                transform[pivot_row] = [
                    -entry for entry in transform[pivot_row]
                ]
            pivot = reduced[pivot_row][column]
            for above in range(pivot_row):
                quotient = reduced[above][column] // pivot
                if quotient:
                    reduced[above] = [
                        reduced[above][index]
                        - quotient * reduced[pivot_row][index]
                        for index in range(columns)
                    ]
                    transform[above] = [
                        transform[above][index]
                        - quotient * transform[pivot_row][index]
                        for index in range(rows)
                    ]
            pivot_row += 1
        return HermiteForm(
            self._make(reduced),
            IntegerMatrixSpace(rows, rows)._make(transform),
        )

    # --- Smith normal form ---

    def smith_normal_form(self, value: IntegerMatrix) -> SmithForm:
        """Smith normal form with `U*A*V == D`.

        The diagonal entries are nonnegative, zero entries are at the end, and
        each nonzero diagonal entry divides the next.  The left and right
        transforms are unimodular; they are built from row/column swaps and
        Bezout combinations only.
        """
        self._own(value)
        rows, columns = self._rows, self._columns
        diagonal = [list(row) for row in value.rows]
        left = [
            [1 if row == column else 0 for column in range(rows)]
            for row in range(rows)
        ]
        right = [
            [1 if row == column else 0 for column in range(columns)]
            for row in range(columns)
        ]
        ring = self._ring

        def swap_rows(first: int, second: int) -> None:
            diagonal[first], diagonal[second] = (
                diagonal[second],
                diagonal[first],
            )
            left[first], left[second] = left[second], left[first]

        def swap_columns(first: int, second: int) -> None:
            for row in diagonal:
                row[first], row[second] = row[second], row[first]
            for row in right:
                row[first], row[second] = row[second], row[first]

        def combine_rows(
            first: int,
            second: int,
            a: int,
            b: int,
            gcd: int,
            coefficient_a: int,
            coefficient_b: int,
        ) -> None:
            old_first = diagonal[first][:]
            old_second = diagonal[second][:]
            diagonal[first] = [
                coefficient_a * old_first[index]
                + coefficient_b * old_second[index]
                for index in range(columns)
            ]
            diagonal[second] = [
                (-b // gcd) * old_first[index]
                + (a // gcd) * old_second[index]
                for index in range(columns)
            ]
            old_left_first = left[first][:]
            old_left_second = left[second][:]
            left[first] = [
                coefficient_a * old_left_first[index]
                + coefficient_b * old_left_second[index]
                for index in range(rows)
            ]
            left[second] = [
                (-b // gcd) * old_left_first[index]
                + (a // gcd) * old_left_second[index]
                for index in range(rows)
            ]

        def combine_columns(
            first: int,
            second: int,
            a: int,
            b: int,
            gcd: int,
            coefficient_a: int,
            coefficient_b: int,
        ) -> None:
            old_first = [row[first] for row in diagonal]
            old_second = [row[second] for row in diagonal]
            for row in range(rows):
                diagonal[row][first] = (
                    coefficient_a * old_first[row]
                    + coefficient_b * old_second[row]
                )
                diagonal[row][second] = (
                    (-b // gcd) * old_first[row]
                    + (a // gcd) * old_second[row]
                )
            old_right_first = [row[first] for row in right]
            old_right_second = [row[second] for row in right]
            for row in range(columns):
                right[row][first] = (
                    coefficient_a * old_right_first[row]
                    + coefficient_b * old_right_second[row]
                )
                right[row][second] = (
                    (-b // gcd) * old_right_first[row]
                    + (a // gcd) * old_right_second[row]
                )

        for pivot_index in range(min(rows, columns)):
            position = next(
                (
                    (row, column)
                    for row in range(pivot_index, rows)
                    for column in range(pivot_index, columns)
                    if diagonal[row][column] != 0
                ),
                None,
            )
            if position is None:
                break
            row, column = position
            if row != pivot_index:
                swap_rows(pivot_index, row)
            if column != pivot_index:
                swap_columns(pivot_index, column)

            while True:
                for row in range(pivot_index + 1, rows):
                    if diagonal[row][pivot_index] != 0:
                        a = diagonal[pivot_index][pivot_index]
                        b = diagonal[row][pivot_index]
                        gcd, first, second = ring.xgcd(a, b)
                        combine_rows(
                            pivot_index, row, a, b, gcd, first, second
                        )
                for column in range(pivot_index + 1, columns):
                    if diagonal[pivot_index][column] != 0:
                        a = diagonal[pivot_index][pivot_index]
                        b = diagonal[pivot_index][column]
                        gcd, first, second = ring.xgcd(a, b)
                        combine_columns(
                            pivot_index, column, a, b, gcd, first, second
                        )

                pivot = diagonal[pivot_index][pivot_index]
                if pivot == 0:
                    replacement = next(
                        (
                            (row, column)
                            for row in range(pivot_index, rows)
                            for column in range(pivot_index, columns)
                            if diagonal[row][column] != 0
                        ),
                        None,
                    )
                    if replacement is None:
                        break
                    row, column = replacement
                    if row != pivot_index:
                        swap_rows(pivot_index, row)
                    if column != pivot_index:
                        swap_columns(pivot_index, column)
                    continue

                pivot = abs(pivot)
                obstruction: tuple[str, int, int] | None = None
                for row in range(pivot_index + 1, rows):
                    if diagonal[row][pivot_index] % pivot != 0:
                        obstruction = ("row", row, 0)
                        break
                if obstruction is None:
                    for column in range(pivot_index + 1, columns):
                        if diagonal[pivot_index][column] % pivot != 0:
                            obstruction = ("column", 0, column)
                            break
                if obstruction is None:
                    for row in range(pivot_index + 1, rows):
                        for column in range(pivot_index + 1, columns):
                            if diagonal[row][column] % pivot != 0:
                                obstruction = ("entry", row, column)
                                break
                        if obstruction is not None:
                            break
                if obstruction is None:
                    for row in range(pivot_index + 1, rows):
                        if diagonal[row][pivot_index] != 0:
                            quotient = (
                                diagonal[row][pivot_index] // pivot
                            )
                            diagonal[row] = [
                                diagonal[row][index]
                                - quotient * diagonal[pivot_index][index]
                                for index in range(columns)
                            ]
                            left[row] = [
                                left[row][index]
                                - quotient * left[pivot_index][index]
                                for index in range(rows)
                            ]
                    for column in range(pivot_index + 1, columns):
                        if diagonal[pivot_index][column] != 0:
                            quotient = (
                                diagonal[pivot_index][column] // pivot
                            )
                            for row in range(rows):
                                diagonal[row][column] -= (
                                    quotient * diagonal[row][pivot_index]
                                )
                            for row in range(columns):
                                right[row][column] -= (
                                    quotient * right[row][pivot_index]
                                )
                    if diagonal[pivot_index][pivot_index] < 0:
                        diagonal[pivot_index] = [
                            -entry for entry in diagonal[pivot_index]
                        ]
                        left[pivot_index] = [
                            -entry for entry in left[pivot_index]
                        ]
                    break

                kind, first, second = obstruction
                if kind == "column":
                    for row in range(rows):
                        diagonal[row][pivot_index] += diagonal[row][second]
                    for row in range(columns):
                        right[row][pivot_index] += right[row][second]
                else:
                    diagonal[pivot_index] = [
                        diagonal[pivot_index][index]
                        + diagonal[first][index]
                        for index in range(columns)
                    ]
                    left[pivot_index] = [
                        left[pivot_index][index] + left[first][index]
                        for index in range(rows)
                    ]

        size = min(rows, columns)
        if any(
            diagonal[row][column] != 0
            for row in range(rows)
            for column in range(columns)
            if row != column
        ):
            raise AssertionError("Smith elimination left a nonzero off-diagonal")
        factors = [diagonal[index][index] for index in range(size)]
        nonzero = [factor for factor in factors if factor != 0]
        if any(factor < 0 for factor in factors):
            raise AssertionError("Smith elimination left a negative factor")
        if any(
            following % current != 0
            for current, following in zip(nonzero, nonzero[1:])
        ):
            raise AssertionError("Smith factors do not divide one another")
        return SmithForm(
            self._make(diagonal),
            IntegerMatrixSpace(rows, rows)._make(left),
            IntegerMatrixSpace(columns, columns)._make(right),
        )


__all__ = [
    "HermiteForm",
    "IntegerMatrix",
    "IntegerMatrixSpace",
    "SmithForm",
]
