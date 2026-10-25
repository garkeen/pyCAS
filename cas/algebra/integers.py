"""The integers as a Euclidean ring.

Z is not a field: division is division with remainder. The derivation is the
explicit zero map of a constant structure.
"""

from __future__ import annotations

from cas.algebra.protocols import (
    Derivation,
    Euclidean,
    IntegerEmbedding,
    Ordered,
)


class IntegerRing(
    Euclidean[int],
    Ordered[int],
    IntegerEmbedding[int],
    Derivation[int],
):
    """Exact integer arithmetic."""

    def zero(self) -> int:
        return 0

    def one(self) -> int:
        return 1

    def add(self, left: int, right: int) -> int:
        return left + right

    def neg(self, value: int) -> int:
        return -value

    def mul(self, left: int, right: int) -> int:
        return left * right

    @property
    def parent_kind(self) -> str:
        return "Z"

    @property
    def parent_requires_base(self) -> bool:
        return False

    @property
    def parent_options(self) -> tuple[tuple[str, str], ...]:
        return ()

    def contains(self, value: object) -> bool:
        return isinstance(value, int) and not isinstance(value, bool)

    def equal(self, left: int, right: int) -> bool:
        return left == right

    def divmod(self, left: int, right: int) -> tuple[int, int]:
        if right == 0:
            raise ZeroDivisionError("integer division by zero")
        return left // right, left % right

    def gcd(self, left: int, right: int) -> int:
        """Greatest common divisor, normalised to a nonnegative value."""
        return abs(super().gcd(left, right))

    def sign(self, value: int) -> int:
        return (value > 0) - (value < 0)

    def of_int(self, value: int) -> int:
        return int(value)

    def deriv(self, value: int) -> int:
        return 0


__all__ = ["IntegerRing"]
