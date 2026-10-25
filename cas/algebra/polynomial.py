"""Multivariate polynomials over an explicit coefficient ring.

Representation: a canonical tuple of `(exponents, coefficient)` pairs. The
coefficient ring owns the coefficients, so no syntax term appears here.

The ring owns its members: an element records the ring that produced it and
every operation refuses an element from another ring. Comparison of elements
goes through the coefficient ring's `equal`, which is the authority — comparing
coefficients with Python `==` would bypass it.

Storage order is the ring's declared monomial order. It is part of the parent's
representation choice, not a hidden default of an algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import StrEnum
from typing import Generic, TypeVar, cast

from cas.algebra.protocols import Euclidean, Field, Ring
from cas.foundation.ids import SymbolId

E = TypeVar("E")

Exponents = tuple[int, ...]

_SEAL = object()


class MonomialOrder(StrEnum):
    """A declared ordering of monomials with a fixed number of variables."""

    LEX = "lex"
    GRLEX = "grlex"
    GREVLEX = "grevlex"

    def key(self, exponents: Exponents) -> tuple[object, ...]:
        if self is MonomialOrder.LEX:
            return (exponents,)
        degree = sum(exponents)
        if self is MonomialOrder.GRLEX:
            return (degree, exponents)
        return (degree, tuple(-exponent for exponent in reversed(exponents)))


@dataclass(frozen=True, slots=True, eq=False)
class Polynomial(Generic[E]):
    """A polynomial owned by one ring.

    `eq=False` on purpose: two elements are equal when the owning ring says so,
    not when Python compares their internal tuples. The seal makes the canonical
    form unrepresentable-by-hand: only `_make` issues elements, so terms are
    always sorted, duplicate-free and free of zero coefficients.
    """

    owner: PolynomialRing[E]
    terms: tuple[tuple[Exponents, E], ...]
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError("a polynomial is issued only by its ring")

    def is_zero(self) -> bool:
        return not self.terms


class PolynomialRing(Ring[Polynomial[E]], Generic[E]):
    """`K[x₁,…,xₙ]` for a fixed coefficient ring `K`."""

    __slots__ = ("_generators", "_coefficients", "_order")

    def __init__(
        self,
        generators: tuple[SymbolId, ...],
        coefficients: Ring[E],
        order: MonomialOrder = MonomialOrder.LEX,
    ) -> None:
        if not generators:
            raise ValueError("a polynomial ring needs at least one generator")
        if len(set(generators)) != len(generators):
            raise ValueError("polynomial generators must be distinct")
        if not isinstance(coefficients, Ring):
            raise TypeError("polynomial coefficients must form a ring")
        if not isinstance(order, MonomialOrder):
            raise TypeError("a polynomial ring needs a monomial order")
        self._generators = tuple(generators)
        self._coefficients = coefficients
        self._order = order

    @property
    def generators(self) -> tuple[SymbolId, ...]:
        return self._generators

    @property
    def coefficients(self) -> Ring[E]:
        return self._coefficients

    @property
    def monomial_order(self) -> MonomialOrder:
        return self._order

    @property
    def parent_kind(self) -> str:
        return "polynomial"

    @property
    def parent_requires_base(self) -> bool:
        return True

    @property
    def parent_options(self) -> tuple[tuple[str, str], ...]:
        return (("monomial_order", self._order.value),)

    # --- ownership ---

    def contains(self, value: object) -> bool:
        return isinstance(value, Polynomial) and value.owner is self

    def _own(self, value: Polynomial[E]) -> None:
        if value.owner is not self:
            raise ValueError("a polynomial belongs to another ring")

    def _check_exponents(self, exponents: Exponents) -> None:
        if len(exponents) != len(self._generators):
            raise ValueError(
                f"expected {len(self._generators)} exponents, got {len(exponents)}"
            )
        if any(exponent < 0 for exponent in exponents):
            raise ValueError("monomial exponents must be nonnegative")

    def _check_index(self, index: int) -> None:
        if not 0 <= index < len(self._generators):
            raise IndexError(f"generator index out of range: {index}")

    def _make(self, terms: dict[Exponents, E]) -> Polynomial[E]:
        kept = tuple(
            (exponents, coefficient)
            for exponents, coefficient in sorted(
                terms.items(), key=lambda item: self._order.key(item[0])
            )
            if not self._coefficients.is_zero(coefficient)
        )
        return Polynomial(self, kept, _SEAL)

    # --- construction ---

    def zero(self) -> Polynomial[E]:
        return Polynomial(self, (), _SEAL)

    def one(self) -> Polynomial[E]:
        return self._make({(0,) * len(self._generators): self._coefficients.one()})

    def constant(self, coefficient: E) -> Polynomial[E]:
        if self._coefficients.is_zero(coefficient):
            return self.zero()
        return self._make({(0,) * len(self._generators): coefficient})

    def monomial(self, exponents: Exponents, coefficient: E) -> Polynomial[E]:
        self._check_exponents(exponents)
        return self._make({exponents: coefficient})

    def generator(self, index: int) -> Polynomial[E]:
        self._check_index(index)
        exponents = tuple(
            1 if position == index else 0
            for position in range(len(self._generators))
        )
        return self.monomial(exponents, self._coefficients.one())

    # --- ring operations ---

    def add(self, left: Polynomial[E], right: Polynomial[E]) -> Polynomial[E]:
        self._own(left)
        self._own(right)
        coefficients = self._coefficients
        terms = dict(left.terms)
        for exponents, coefficient in right.terms:
            terms[exponents] = coefficients.add(
                terms.get(exponents, coefficients.zero()), coefficient
            )
        return self._make(terms)

    def neg(self, value: Polynomial[E]) -> Polynomial[E]:
        self._own(value)
        coefficients = self._coefficients
        return self._make(
            {
                exponents: coefficients.neg(coefficient)
                for exponents, coefficient in value.terms
            }
        )

    def mul(self, left: Polynomial[E], right: Polynomial[E]) -> Polynomial[E]:
        self._own(left)
        self._own(right)
        coefficients = self._coefficients
        terms: dict[Exponents, E] = {}
        zero = coefficients.zero()
        for left_exponents, left_coefficient in left.terms:
            for right_exponents, right_coefficient in right.terms:
                exponents = tuple(
                    first + second
                    for first, second in zip(left_exponents, right_exponents)
                )
                terms[exponents] = coefficients.add(
                    terms.get(exponents, zero),
                    coefficients.mul(left_coefficient, right_coefficient),
                )
        return self._make(terms)

    def equal(self, left: Polynomial[E], right: Polynomial[E]) -> bool:
        self._own(left)
        self._own(right)
        if len(left.terms) != len(right.terms):
            return False
        coefficients = self._coefficients
        for (left_exponents, left_coefficient), (
            right_exponents,
            right_coefficient,
        ) in zip(left.terms, right.terms):
            if left_exponents != right_exponents:
                return False
            if not coefficients.equal(left_coefficient, right_coefficient):
                return False
        return True

    # --- structure-specific queries and operations ---

    def degree(self, value: Polynomial[E], index: int) -> int:
        """Degree in one generator; the zero polynomial has degree -1."""
        self._own(value)
        self._check_index(index)
        if not value.terms:
            return -1
        return max(exponents[index] for exponents, _ in value.terms)

    def coefficient(self, value: Polynomial[E], exponents: Exponents) -> E:
        self._own(value)
        self._check_exponents(exponents)
        for stored, coefficient in value.terms:
            if stored == exponents:
                return coefficient
        return self._coefficients.zero()

    def derivative(self, value: Polynomial[E], index: int) -> Polynomial[E]:
        """Formal derivative with respect to one generator."""
        self._own(value)
        self._check_index(index)
        coefficients = self._coefficients
        terms: dict[Exponents, E] = {}
        for exponents, coefficient in value.terms:
            power = exponents[index]
            if power == 0:
                continue
            lowered = tuple(
                exponent - (1 if position == index else 0)
                for position, exponent in enumerate(exponents)
            )
            terms[lowered] = coefficients.mul_int(coefficient, power)
        return self._make(terms)


class UnivariatePolynomialRing(PolynomialRing[E], Euclidean[Polynomial[E]]):
    """`K[x]` for a field `K`: the one case where polynomial division exists.

    Division is defined only for a single generator over a field; a multivariate
    ring never advertises the Euclidean capability.
    """

    __slots__ = ()

    def __init__(
        self,
        generator: SymbolId,
        coefficients: Field[E],
        order: MonomialOrder = MonomialOrder.LEX,
    ) -> None:
        if not isinstance(coefficients, Field):
            raise TypeError("univariate division needs a field of coefficients")
        super().__init__((generator,), coefficients, order)

    @property
    def coefficients(self) -> Field[E]:
        """Narrowed on purpose: this ring was built with field coefficients."""
        return cast("Field[E]", self._coefficients)

    def divmod(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> tuple[Polynomial[E], Polynomial[E]]:
        """Long division; the remainder has strictly smaller degree."""
        self._own(left)
        self._own(right)
        if right.is_zero():
            raise ZeroDivisionError("polynomial division by zero")
        coefficients = self.coefficients
        divisor_degree = self.degree(right, 0)
        divisor_leading = self.coefficient(right, (divisor_degree,))
        quotient = self.zero()
        remainder = left
        while not remainder.is_zero():
            degree = self.degree(remainder, 0)
            if degree < divisor_degree:
                break
            leading = self.coefficient(remainder, (degree,))
            factor = self.monomial(
                (degree - divisor_degree,),
                coefficients.div(leading, divisor_leading),
            )
            quotient = self.add(quotient, factor)
            remainder = self.sub(remainder, self.mul(factor, right))
        return quotient, remainder

    def gcd(self, left: Polynomial[E], right: Polynomial[E]) -> Polynomial[E]:
        """Greatest common divisor, normalised to a monic polynomial."""
        self._own(left)
        self._own(right)
        current = super().gcd(left, right)
        if current.is_zero():
            return self.zero()
        leading = self.coefficient(current, (self.degree(current, 0),))
        return self.mul(
            self.monomial((0,), self.coefficients.inv(leading)),
            current,
        )
