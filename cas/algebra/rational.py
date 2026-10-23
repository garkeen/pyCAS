"""Rational functions `K(x)` over a univariate polynomial ring.

An element is a reduced fraction: the denominator is nonzero and monic, and the
numerator and denominator are coprime. Reduction is part of construction, so
comparing representatives is comparing field elements.

A zero numerator is stored as `0/1`. Division by zero raises; there is no
"undefined element".

The field does not assume a derivation. `derivative` is the formal derivative
with `D(x) = 1`; binding it as the chosen derivation of a differential structure
is the caller's act.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.protocols import Field

E = TypeVar("E")

_SEAL = object()


@dataclass(frozen=True, slots=True, eq=False)
class RationalFunction(Generic[E]):
    """A reduced fraction owned by one field.

    The seal makes the canonical form unrepresentable-by-hand: only
    `fraction` issues elements, so the denominator is nonzero and monic and the
    numerator is coprime to it.
    """

    owner: RationalFunctionField[E]
    numerator: Polynomial[E]
    denominator: Polynomial[E]
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError("a rational function is issued only by its field")


class RationalFunctionField(Field[RationalFunction[E]], Generic[E]):
    """The fraction field of a univariate polynomial ring over a field."""

    __slots__ = ("_polynomials",)

    def __init__(self, polynomials: UnivariatePolynomialRing[E]) -> None:
        if not isinstance(polynomials, UnivariatePolynomialRing):
            raise TypeError("K(x) needs a univariate polynomial ring")
        self._polynomials = polynomials

    @property
    def polynomials(self) -> UnivariatePolynomialRing[E]:
        return self._polynomials

    def contains(self, value: RationalFunction[E]) -> bool:
        return value.owner is self

    def _own(self, value: RationalFunction[E]) -> None:
        if value.owner is not self:
            raise ValueError("a rational function belongs to another field")

    def fraction(
        self,
        numerator: Polynomial[E],
        denominator: Polynomial[E],
    ) -> RationalFunction[E]:
        """Build the reduced fraction `numerator/denominator`."""
        polynomials = self._polynomials
        if not polynomials.contains(numerator):
            raise ValueError("a numerator belongs to another polynomial ring")
        if not polynomials.contains(denominator):
            raise ValueError("a denominator belongs to another polynomial ring")
        if denominator.is_zero():
            raise ZeroDivisionError("a rational function needs a nonzero denominator")
        if numerator.is_zero():
            return RationalFunction(
                self, polynomials.zero(), polynomials.one(), _SEAL
            )
        divisor = polynomials.gcd(numerator, denominator)
        if not polynomials.is_one(divisor):
            numerator, _ = polynomials.divmod(numerator, divisor)
            denominator, _ = polynomials.divmod(denominator, divisor)
        leading = polynomials.coefficient(
            denominator, (polynomials.degree(denominator, 0),)
        )
        if not polynomials.coefficients.is_one(leading):
            scale = polynomials.monomial(
                (0,), polynomials.coefficients.inv(leading)
            )
            numerator = polynomials.mul(numerator, scale)
            denominator = polynomials.mul(denominator, scale)
        return RationalFunction(self, numerator, denominator, _SEAL)

    def of_polynomial(self, value: Polynomial[E]) -> RationalFunction[E]:
        return self.fraction(value, self._polynomials.one())

    # --- field operations ---

    def zero(self) -> RationalFunction[E]:
        return self.fraction(self._polynomials.zero(), self._polynomials.one())

    def one(self) -> RationalFunction[E]:
        return self.fraction(self._polynomials.one(), self._polynomials.one())

    def add(
        self,
        left: RationalFunction[E],
        right: RationalFunction[E],
    ) -> RationalFunction[E]:
        self._own(left)
        self._own(right)
        polynomials = self._polynomials
        numerator = polynomials.add(
            polynomials.mul(left.numerator, right.denominator),
            polynomials.mul(right.numerator, left.denominator),
        )
        denominator = polynomials.mul(left.denominator, right.denominator)
        return self.fraction(numerator, denominator)

    def neg(self, value: RationalFunction[E]) -> RationalFunction[E]:
        self._own(value)
        return self.fraction(self._polynomials.neg(value.numerator), value.denominator)

    def mul(
        self,
        left: RationalFunction[E],
        right: RationalFunction[E],
    ) -> RationalFunction[E]:
        self._own(left)
        self._own(right)
        polynomials = self._polynomials
        return self.fraction(
            polynomials.mul(left.numerator, right.numerator),
            polynomials.mul(left.denominator, right.denominator),
        )

    def equal(
        self,
        left: RationalFunction[E],
        right: RationalFunction[E],
    ) -> bool:
        """Both representatives are canonical, so comparing them is sound."""
        self._own(left)
        self._own(right)
        polynomials = self._polynomials
        return polynomials.equal(
            left.numerator, right.numerator
        ) and polynomials.equal(left.denominator, right.denominator)

    def inv(self, value: RationalFunction[E]) -> RationalFunction[E]:
        self._own(value)
        if value.numerator.is_zero():
            raise ZeroDivisionError("zero has no inverse in K(x)")
        return self.fraction(value.denominator, value.numerator)

    # --- calculus ---

    def derivative(
        self,
        value: RationalFunction[E],
        index: int = 0,
    ) -> RationalFunction[E]:
        """Formal derivative `(n'd - nd') / d^2` with `D(x) = 1`."""
        self._own(value)
        if index != 0:
            raise IndexError(f"the field has one generator, got index {index}")
        polynomials = self._polynomials
        numerator = polynomials.sub(
            polynomials.mul(
                polynomials.derivative(value.numerator, 0), value.denominator
            ),
            polynomials.mul(
                value.numerator, polynomials.derivative(value.denominator, 0)
            ),
        )
        denominator = polynomials.mul(value.denominator, value.denominator)
        return self.fraction(numerator, denominator)


__all__ = ["RationalFunction", "RationalFunctionField"]
