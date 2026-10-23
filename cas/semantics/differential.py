"""Differential structures: a parent plus the derivation chosen on it.

A parent is not a derivation. A polynomial ring admits infinitely many
derivations, and a rational-function field admits none until one is chosen.
`DifferentialStructure` binds the choice explicitly, and the constructors here
are the only way to build one, so a derivation can never be paired with a parent
it does not act on.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Generic, TypeVar

from cas.algebra.parents import Parent
from cas.algebra.polynomial import Polynomial, PolynomialRing
from cas.algebra.protocols import Derivation
from cas.algebra.rational import RationalFunction, RationalFunctionField

E = TypeVar("E")

_SEAL = object()


@dataclass(frozen=True, slots=True)
class DifferentialStructure(Generic[E]):
    """A parent and the derivation this computation uses on it."""

    parent: Parent[E]
    derivation: Derivation[E]
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError(
                "a differential structure is built by polynomial_structure "
                "or rational_structure"
            )

    def deriv(self, value: E) -> E:
        return self.derivation.deriv(value)


class PolynomialDerivation(Derivation[Polynomial[E]], Generic[E]):
    """The formal partial derivative with respect to one generator."""

    __slots__ = ("_ring", "_index")

    def __init__(self, ring: PolynomialRing[E], index: int) -> None:
        if not 0 <= index < len(ring.generators):
            raise IndexError(f"generator index out of range: {index}")
        self._ring = ring
        self._index = index

    def deriv(self, value: Polynomial[E]) -> Polynomial[E]:
        return self._ring.derivative(value, self._index)


class RationalDerivation(Derivation[RationalFunction[E]], Generic[E]):
    """`D(x) = 1` on the single generator of a rational-function field."""

    __slots__ = ("_field",)

    def __init__(self, field: RationalFunctionField[E]) -> None:
        self._field = field

    def deriv(self, value: RationalFunction[E]) -> RationalFunction[E]:
        return self._field.derivative(value)


def polynomial_structure(
    parent: Parent[Polynomial[E]],
    index: int,
) -> DifferentialStructure[Polynomial[E]]:
    """Pair a polynomial parent with the derivative in generator `index`."""
    if not isinstance(parent.ring, PolynomialRing):
        raise TypeError("a polynomial structure needs a polynomial parent")
    return DifferentialStructure(parent, PolynomialDerivation(parent.ring, index), _SEAL)


def rational_structure(
    parent: Parent[RationalFunction[E]],
) -> DifferentialStructure[RationalFunction[E]]:
    """Pair a rational-function parent with `D(x) = 1`."""
    if not isinstance(parent.ring, RationalFunctionField):
        raise TypeError("a rational structure needs a rational-function parent")
    return DifferentialStructure(parent, RationalDerivation(parent.ring), _SEAL)


__all__ = [
    "DifferentialStructure",
    "PolynomialDerivation",
    "RationalDerivation",
    "polynomial_structure",
    "rational_structure",
]
