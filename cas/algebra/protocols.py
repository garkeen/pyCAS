"""Effective algebraic structures.

A structure accepts members and provides exact operations on them. Capabilities
are separate interfaces, so nothing is silently promoted: a ring is not assumed
to be a field, and a missing derivation is never replaced by the zero map.

Contracts every implementation must satisfy:

- `equal` is total on the members the structure accepts; it never returns
  "unknown". A value outside the structure is a caller error, not a third
  truth value.
- `zero`, `one`, `add`, `neg`, `mul` obey the ring axioms in the structure.
- An `Ordered` structure exposes a total order through `sign`, with
  `sign(0) == 0` and a positive cone closed under addition and multiplication.
- A `Derivation` satisfies additivity and Leibniz. A constant structure may
  implement it as zero; that is an explicit statement about the structure, not
  a default.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Generic, TypeVar

E = TypeVar("E")


class Ring(ABC, Generic[E]):
    """Exact arithmetic on the members of one structure."""

    @abstractmethod
    def zero(self) -> E:
        """The additive identity."""

    @abstractmethod
    def one(self) -> E:
        """The multiplicative identity."""

    @abstractmethod
    def add(self, left: E, right: E) -> E:
        """Sum of two members."""

    @abstractmethod
    def neg(self, value: E) -> E:
        """Additive inverse."""

    @abstractmethod
    def mul(self, left: E, right: E) -> E:
        """Product of two members."""

    @abstractmethod
    def equal(self, left: E, right: E) -> bool:
        """Decide equality of two members."""

    def sub(self, left: E, right: E) -> E:
        return self.add(left, self.neg(right))

    def is_zero(self, value: E) -> bool:
        return self.equal(value, self.zero())

    def is_one(self, value: E) -> bool:
        return self.equal(value, self.one())

    def pow(self, value: E, exponent: int) -> E:
        """Exponentiation by squaring for a nonnegative exponent."""
        if exponent < 0:
            raise ValueError("a ring power needs a nonnegative exponent")
        result = self.one()
        base = value
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = self.mul(result, base)
            base = self.mul(base, base)
            remaining >>= 1
        return result

    def mul_int(self, value: E, factor: int) -> E:
        """Repeated addition, available in every ring without an embedding.

        A ring always carries a Z-algebra structure; this is that structure, not
        a claim that the integers embed injectively.
        """
        if factor < 0:
            return self.neg(self.mul_int(value, -factor))
        result = self.zero()
        base = value
        remaining = factor
        while remaining:
            if remaining & 1:
                result = self.add(result, base)
            base = self.add(base, base)
            remaining >>= 1
        return result


class Field(Ring[E], ABC):
    """A ring in which every nonzero member has an inverse."""

    @abstractmethod
    def inv(self, value: E) -> E:
        """The multiplicative inverse; raises `ZeroDivisionError` on zero."""

    def div(self, left: E, right: E) -> E:
        return self.mul(left, self.inv(right))


class Euclidean(Ring[E], ABC):
    """A ring with division and a remainder of strictly smaller size."""

    @abstractmethod
    def divmod(self, left: E, right: E) -> tuple[E, E]:
        """Return `(quotient, remainder)` with `left = right*quotient + remainder`."""

    def gcd(self, left: E, right: E) -> E:
        """Greatest common divisor, normalised by the structure's convention."""
        current, following = left, right
        while not self.is_zero(following):
            _, remainder = self.divmod(current, following)
            current, following = following, remainder
        return current


class Ordered(Ring[E], ABC):
    """A ring with a total order, exposed through the sign of a difference."""

    @abstractmethod
    def sign(self, value: E) -> int:
        """Return -1, 0 or 1 according to the element's position to zero."""

    def compare(self, left: E, right: E) -> int:
        return self.sign(self.sub(left, right))

    def less(self, left: E, right: E) -> bool:
        return self.compare(left, right) < 0

    def less_equal(self, left: E, right: E) -> bool:
        return self.compare(left, right) <= 0


class IntegerEmbedding(ABC, Generic[E]):
    """The canonical embedding of the integers into a structure."""

    @abstractmethod
    def of_int(self, value: int) -> E:
        """Embed an integer."""


class Derivation(ABC, Generic[E]):
    """A derivation on the members of a structure."""

    @abstractmethod
    def deriv(self, value: E) -> E:
        """Apply the derivation. Constant structures state this as zero."""


__all__ = [
    "Derivation",
    "Euclidean",
    "Field",
    "IntegerEmbedding",
    "Ordered",
    "Ring",
]
