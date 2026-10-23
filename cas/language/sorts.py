"""Mathematical sorts: what a value is, never how it is represented.

A sort states which values an expression denotes. Several parents may represent
the same sort, and a sort does not by itself decide whether a particular
representation can decide equality.

`Real` is a sort, not a representation: it does not promise that every real
expression is representable or decidable.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


class NumberSystem(Enum):
    """The numeric tower. Declaration order is the embedding order."""

    INTEGER = "integer"
    RATIONAL = "rational"
    REAL = "real"
    COMPLEX = "complex"
    UNKNOWN = "unknown"


_EMBEDDING_RANK = {
    NumberSystem.INTEGER: 0,
    NumberSystem.RATIONAL: 1,
    NumberSystem.REAL: 2,
    NumberSystem.COMPLEX: 3,
}

_ORDERED = frozenset(
    {NumberSystem.INTEGER, NumberSystem.RATIONAL, NumberSystem.REAL}
)


class Sort:
    """Closed hierarchy of value sorts."""

    __slots__ = ()

    def embeds_into(self, target: Sort) -> bool:
        """Whether every value of this sort is a value of `target`."""
        return self == target


@dataclass(frozen=True, slots=True)
class ScalarSort(Sort):
    number_system: NumberSystem

    def embeds_into(self, target: Sort) -> bool:
        if not isinstance(target, ScalarSort):
            return False
        if (
            self.number_system is NumberSystem.UNKNOWN
            or target.number_system is NumberSystem.UNKNOWN
        ):
            return self.number_system is target.number_system
        return (
            _EMBEDDING_RANK[target.number_system]
            >= _EMBEDDING_RANK[self.number_system]
        )


@dataclass(frozen=True, slots=True)
class VectorSort(Sort):
    element: Sort
    length: int

    def __post_init__(self) -> None:
        if self.length < 1:
            raise ValueError("a vector needs at least one entry")


@dataclass(frozen=True, slots=True)
class MatrixSort(Sort):
    element: Sort
    rows: int
    columns: int

    def __post_init__(self) -> None:
        if self.rows < 1 or self.columns < 1:
            raise ValueError("a matrix needs at least one row and column")


@dataclass(frozen=True, slots=True)
class FunctionSort(Sort):
    arguments: tuple[Sort, ...]
    result: Sort


@dataclass(frozen=True, slots=True)
class PropositionSort(Sort):
    """The sort of a formula that can be true or false."""


@dataclass(frozen=True, slots=True)
class RegionSort(Sort):
    """The sort of a region description."""


@dataclass(frozen=True, slots=True)
class SyntaxSort(Sort):
    """The sort of quoted syntax data."""


INTEGER = ScalarSort(NumberSystem.INTEGER)
RATIONAL = ScalarSort(NumberSystem.RATIONAL)
REAL = ScalarSort(NumberSystem.REAL)
COMPLEX = ScalarSort(NumberSystem.COMPLEX)
UNKNOWN_SCALAR = ScalarSort(NumberSystem.UNKNOWN)
PROPOSITION = PropositionSort()
REGION = RegionSort()
SYNTAX = SyntaxSort()


def is_scalar(sort: Sort) -> bool:
    return isinstance(sort, ScalarSort)


def is_ordered(sort: Sort) -> bool:
    """Whether order comparisons are meaningful on this sort."""
    return isinstance(sort, ScalarSort) and sort.number_system in _ORDERED


def join(left: Sort, right: Sort) -> Sort | None:
    """The least sort both sides embed into, or None when there is none."""
    if left == right:
        return left
    if left.embeds_into(right):
        return right
    if right.embeds_into(left):
        return left
    return None


__all__ = [
    "COMPLEX",
    "FunctionSort",
    "INTEGER",
    "MatrixSort",
    "NumberSystem",
    "PROPOSITION",
    "PropositionSort",
    "RATIONAL",
    "REAL",
    "REGION",
    "RegionSort",
    "SYNTAX",
    "ScalarSort",
    "Sort",
    "SyntaxSort",
    "UNKNOWN_SCALAR",
    "VectorSort",
    "is_ordered",
    "is_scalar",
    "join",
]
