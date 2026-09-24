"""Coefficient-ring and number-domain protocols plus value-owned domain catalogs."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Protocol, TypeAlias

from cas.syntax.term import Sym, Term

# The one sanctioned opaque mathematical-value boundary in the math layer.
# Callers pass these values back to the ring/domain that produced them; they
# never inspect their concrete representation.
DomainElement: TypeAlias = object

DomainPredicate: TypeAlias = Callable[["Domain"], bool]


class RingError(Exception):
    """A requested coefficient-ring operation is unavailable."""


class Ring(ABC):
    """Exact coefficient arithmetic over opaque domain elements."""

    is_field: bool = False
    is_euclidean: bool = False
    supports_rational_evaluation: bool = False

    @abstractmethod
    def from_int(self, value: int) -> DomainElement:
        """Embed an integer."""

    @abstractmethod
    def from_frac(self, value: Fraction) -> DomainElement:
        """Embed a rational or refuse when the ring does not contain Q."""

    def to_fraction(self, value: DomainElement) -> Fraction:
        """Decode a coefficient for exact rational real-root algorithms."""

        raise RingError(
            f"{type(self).__name__} does not support rational real evaluation"
        )

    @abstractmethod
    def add(self, left: DomainElement, right: DomainElement) -> DomainElement:
        """Add two coefficients."""

    @abstractmethod
    def neg(self, value: DomainElement) -> DomainElement:
        """Negate one coefficient."""

    @abstractmethod
    def mul(self, left: DomainElement, right: DomainElement) -> DomainElement:
        """Multiply two coefficients."""

    @abstractmethod
    def equal(self, left: DomainElement, right: DomainElement) -> bool:
        """Decide coefficient equality."""

    def is_zero(self, value: DomainElement) -> bool:
        return self.equal(value, self.from_int(0))

    def sub(self, left: DomainElement, right: DomainElement) -> DomainElement:
        return self.add(left, self.neg(right))

    def divmod_(
        self,
        left: DomainElement,
        right: DomainElement,
    ) -> tuple[DomainElement, DomainElement]:
        """Divide with remainder for a Euclidean ring."""

        raise RingError(f"{type(self).__name__} is not a Euclidean ring")

    def div_exact(self, left: DomainElement, right: DomainElement) -> DomainElement:
        """Divide exactly in a field."""

        raise RingError(f"{type(self).__name__} has no exact division")

    def xgcd(
        self,
        left: DomainElement,
        right: DomainElement,
    ) -> tuple[DomainElement, DomainElement, DomainElement]:
        """Return ``(gcd, s, t)`` for ``s*left + t*right = gcd``."""

        raise RingError(f"{type(self).__name__} has no extended-gcd operation")

    def integer_value(self, value: DomainElement) -> int | None:
        """Return the integer represented by a coefficient, if it is integral."""

        return None

    def deriv(self, value: DomainElement) -> DomainElement:
        """Apply the coefficient derivation (zero for a constant domain)."""

        return self.from_int(0)

    def pow_pos(self, value: DomainElement, exponent: int) -> DomainElement:
        """Exponentiation by squaring for a nonnegative exponent."""

        if exponent < 0:
            raise ValueError("negative exponent")
        result = self.from_int(1)
        base = value
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = self.mul(result, base)
            base = self.mul(base, base)
            remaining >>= 1
        return result

    def render_coefficient(self, value: DomainElement) -> Term:
        """Render a coefficient as a syntax term."""

        raise TypeError(f"ring {self!r} cannot render coefficient {value!r}")


class FracRing(Ring):
    """Shared implementation for rings containing Q."""

    is_field = True

    def div_exact(self, left: DomainElement, right: DomainElement) -> DomainElement:
        if self.is_zero(right):
            raise ZeroDivisionError("division by zero")
        if not isinstance(left, Fraction) or not isinstance(right, Fraction):
            raise RingError(f"{type(self).__name__} cannot divide its element type")
        return left / right

    def equal(self, left: DomainElement, right: DomainElement) -> bool:
        return left == right

    def integer_value(self, value: DomainElement) -> int | None:
        if not isinstance(value, Fraction):
            return None
        return value.numerator if value.denominator == 1 else None


@dataclass(frozen=True, slots=True)
class DomainCapabilities:
    """The fixed capability record queried by mathematical algorithms."""

    field: bool = False
    ordered: bool = False
    euclidean: bool = False
    scoped: bool = False


DEFAULT_CAPABILITIES = DomainCapabilities()

Monomial: TypeAlias = tuple[tuple[int, ...], DomainElement]


class PolynomialView(Protocol):
    """Narrow structural capability returned by polynomial-consuming domains."""

    vars: tuple[Sym, ...]
    monos: tuple[Monomial, ...]

    def is_zero(self) -> bool:
        """Whether the represented polynomial is zero."""

        ...


class Domain(ABC):
    """A number domain consuming and producing its own opaque elements."""

    name: str = "?"
    capabilities: DomainCapabilities = DEFAULT_CAPABILITIES
    ring: Ring | None = None
    vars: tuple[Sym, ...] | None = None

    @property
    def is_field(self) -> bool:
        return self.capabilities.field

    @property
    def is_ordered(self) -> bool:
        return self.capabilities.ordered

    @property
    def is_euclidean(self) -> bool:
        return self.capabilities.euclidean

    @property
    def scoped(self) -> bool:
        return self.capabilities.scoped

    @abstractmethod
    def member(self, term: Term) -> bool:
        """Whether ``term`` belongs to this domain."""

    @abstractmethod
    def normalize(self, term: Term) -> Term | None:
        """Return the domain normal form, or ``None`` for a non-member."""

    @abstractmethod
    def equal(self, left: Term, right: Term) -> bool | None:
        """Decide equality for members; return ``None`` for a caller bounds error."""

    def element_is_zero(self, element: DomainElement) -> bool:
        """Consume one projected element and decide whether it is zero."""

        raise NotImplementedError(
            f"domain {type(self).__name__} ({self.name}) does not consume "
            "projected elements: implement element_is_zero")

    def element_to_term(self, element: DomainElement) -> Term:
        """Render one projected element in the domain's normal form."""

        raise NotImplementedError(
            f"domain {type(self).__name__} ({self.name}) does not consume "
            "projected elements: implement element_to_term")

    def element_poly(self, element: DomainElement) -> PolynomialView | None:
        """Return a polynomial sharing the element's vanishing, when exposed."""

        return None

    def element_as_poly(self, element: DomainElement) -> PolynomialView | None:
        """Return the element itself as a polynomial, when exposed."""

        return None


@dataclass(frozen=True, slots=True)
class DomainCatalog:
    """Immutable resident and computation-scoped domain collections."""

    resident: tuple[Domain, ...] = ()
    scoped: tuple[Domain, ...] = ()

    def __post_init__(self) -> None:
        resident_names = [domain.name for domain in self.resident]
        if len(set(resident_names)) != len(resident_names):
            raise ValueError("resident domain names must be unique")
        for domain in self.resident:
            if domain.scoped:
                raise ValueError(
                    f"scoped domain cannot be resident: {domain.name}")
        scoped_names = [domain.name for domain in self.scoped]
        if len(set(scoped_names)) != len(scoped_names):
            raise ValueError("scoped domain names must be unique")
        overlap = set(resident_names) & set(scoped_names)
        if overlap:
            raise ValueError(f"scoped domains shadow resident domains: {sorted(overlap)}")

    def lookup(self, name: str) -> Domain | None:
        """Return the innermost matching scoped or resident domain."""

        for domain in reversed(self.scoped):
            if domain.name == name:
                return domain
        for domain in self.resident:
            if domain.name == name:
                return domain
        return None

    def find(self, predicate: DomainPredicate) -> tuple[Domain, ...]:
        """Return resident domains matching a capability predicate in order."""

        return tuple(domain for domain in self.resident if predicate(domain))

    def require_unique(
        self,
        predicate: DomainPredicate,
        requirement: str,
    ) -> Domain:
        """Return the unique matching resident domain or refuse ambiguity."""

        matches = self.find(predicate)
        if len(matches) != 1:
            names = [domain.name for domain in matches]
            raise RingError(
                f"{requirement} needs a unique domain, matched {names}")
        return matches[0]

    def with_scoped(self, *domains: Domain) -> DomainCatalog:
        """Return a nested computation view containing explicit scoped domains."""

        additions = tuple(domains)
        for domain in additions:
            if not domain.scoped:
                raise ValueError(f"resident domain cannot enter a scope: {domain.name}")
        return replace(self, scoped=self.scoped + additions)
