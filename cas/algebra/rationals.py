"""The rationals as a field.

Q is ordered, embeds the integers, and carries the explicit zero derivation of a
constant structure. It is not a representation of all reals.
"""

from __future__ import annotations

from fractions import Fraction

from cas.algebra.protocols import (
    Derivation,
    Field,
    IntegerEmbedding,
    Ordered,
    RationalEmbedding,
)


class RationalField(
    Field[Fraction],
    Ordered[Fraction],
    IntegerEmbedding[Fraction],
    RationalEmbedding[Fraction],
    Derivation[Fraction],
):
    """Exact rational arithmetic over `Fraction`."""

    def zero(self) -> Fraction:
        return Fraction(0)

    def one(self) -> Fraction:
        return Fraction(1)

    def add(self, left: Fraction, right: Fraction) -> Fraction:
        return left + right

    def neg(self, value: Fraction) -> Fraction:
        return -value

    def mul(self, left: Fraction, right: Fraction) -> Fraction:
        return left * right

    @property
    def parent_kind(self) -> str:
        return "Q"

    @property
    def parent_requires_base(self) -> bool:
        return False

    @property
    def parent_options(self) -> tuple[tuple[str, str], ...]:
        return ()

    def contains(self, value: object) -> bool:
        return isinstance(value, Fraction)

    def equal(self, left: Fraction, right: Fraction) -> bool:
        return left == right

    def inv(self, value: Fraction) -> Fraction:
        if value == 0:
            raise ZeroDivisionError("zero has no inverse in Q")
        return Fraction(1, 1) / value

    def sign(self, value: Fraction) -> int:
        return (value > 0) - (value < 0)

    def of_int(self, value: int) -> Fraction:
        return Fraction(value)

    def of_rational(self, numerator: int, denominator: int) -> Fraction:
        if denominator == 0:
            raise ZeroDivisionError("a rational needs a nonzero denominator")
        return Fraction(numerator, denominator)

    def of_fraction(self, value: Fraction) -> Fraction:
        return Fraction(value)

    def div_exact(self, left: Fraction, right: Fraction) -> Fraction:
        return self.div(left, right)

    def div_int(self, value: Fraction, factor: int) -> Fraction:
        if factor == 0:
            raise ZeroDivisionError("division by zero")
        return value / factor

    @property
    def characteristic(self) -> int:
        return 0

    def deriv(self, value: Fraction) -> Fraction:
        return Fraction(0)


__all__ = ["RationalField"]
