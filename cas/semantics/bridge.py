"""Conversions between syntax terms and parent elements.

The bridge accepts one explicit fragment: literals, the ring's generators, sums,
products and nonnegative integer powers. Anything else returns `None`; it never
guesses a domain, a representation or a coercion.

The return direction renders elements back into terms using the language's
structural heads. A world without those heads cannot render, and the bridge says
so by returning `None` instead of inventing spines.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from fractions import Fraction
from types import MappingProxyType
from typing import Generic, Protocol, TypeVar, cast

from cas.algebra.polynomial import Polynomial, PolynomialRing
from cas.algebra.protocols import RationalEmbedding
from cas.foundation.ids import SymbolId
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.syntax import term as T

E = TypeVar("E")


class PolynomialBridge(Protocol[E]):
    """An explicit conversion between terms and one polynomial ring."""

    def to_value(self, term: T.Term) -> Polynomial[E] | None:
        """Convert a term into a member of the target ring, or None."""

    def to_term(self, value: Polynomial[E]) -> T.Term | None:
        """Render a member as a term, or None without the structural heads."""


@dataclass(frozen=True, slots=True)
class SimplePolynomialBridge(Generic[E]):
    """The bridge for a ring whose coefficients are base literals."""

    ring: PolynomialRing[E]
    signature: LanguageSignature
    name_of: Callable[[SymbolId], str]
    render_coefficient: Callable[[E], T.Term]

    def to_value(self, term: T.Term) -> Polynomial[E] | None:
        return to_polynomial(self.ring, term, self.signature)

    def to_term(self, value: Polynomial[E]) -> T.Term | None:
        return to_term(
            self.ring,
            value,
            self.signature,
            self.name_of,
            self.render_coefficient,
        )


@dataclass(frozen=True, slots=True)
class ParameterPolynomialBridge(Generic[E]):
    """A bridge for `K[parameters][target]`.

    Parameter symbols become constants of the target ring (elements of the
    coefficient ring), while target symbols become target generators. The two
    maps are explicit and disjoint; no symbol is guessed to be a coefficient or
    a variable from its name or position.
    """

    ring: PolynomialRing[Polynomial[E]]
    coefficient_ring: PolynomialRing[E]
    parameters: Mapping[SymbolId, int]
    signature: LanguageSignature
    name_of: Callable[[SymbolId], str]
    embed_rational: Callable[[Fraction], Polynomial[E]]
    render_base: Callable[[E], T.Term]

    def __post_init__(self) -> None:
        parameters = MappingProxyType(dict(self.parameters))
        object.__setattr__(self, "parameters", parameters)
        if set(parameters) & set(self.ring.generators):
            raise ValueError("a symbol cannot be both a target and a parameter")
        for index in parameters.values():
            if not 0 <= index < len(self.coefficient_ring.generators):
                raise ValueError("a parameter index is outside the coefficient ring")

    def to_value(self, term: T.Term) -> Polynomial[Polynomial[E]] | None:
        target = self.ring
        coefficient_ring = self.coefficient_ring
        target_indices = {
            symbol_id: index
            for index, symbol_id in enumerate(target.generators)
        }
        parameters = dict(self.parameters)

        def convert(current: T.Term) -> Polynomial[Polynomial[E]] | None:
            if isinstance(current, T.IntLit):
                return target.constant(
                    self.embed_rational(Fraction(current.value))
                )
            if isinstance(current, T.RatLit):
                return target.constant(self.embed_rational(current.value))
            if isinstance(current, T.SymbolRef):
                index = target_indices.get(current.symbol_id)
                if index is not None:
                    return target.generator(index)
                parameter = parameters.get(current.symbol_id)
                if parameter is not None:
                    return target.constant(
                        coefficient_ring.generator(parameter)
                    )
                return None
            if not isinstance(current, T.Apply) or not isinstance(
                current.operator, T.SymbolRef
            ):
                return None
            head = self.signature.head_of(current.operator.symbol_id)
            if head is StructuralHead.PLUS:
                total = target.zero()
                for argument in current.arguments:
                    converted = convert(argument)
                    if converted is None:
                        return None
                    total = target.add(total, converted)
                return total
            if head is StructuralHead.TIMES:
                product = target.one()
                for argument in current.arguments:
                    converted = convert(argument)
                    if converted is None:
                        return None
                    product = target.mul(product, converted)
                return product
            if head is StructuralHead.POWER:
                if len(current.arguments) != 2:
                    return None
                base_term, exponent_term = current.arguments
                if (
                    not isinstance(exponent_term, T.IntLit)
                    or exponent_term.value < 0
                ):
                    return None
                base = convert(base_term)
                return (
                    None
                    if base is None
                    else target.pow(base, exponent_term.value)
                )
            return None

        return convert(term)

    def to_term(self, value: Polynomial[Polynomial[E]]) -> T.Term | None:
        def render_coefficient(coefficient: Polynomial[E]) -> T.Term:
            rendered = to_term(
                self.coefficient_ring,
                coefficient,
                self.signature,
                self.name_of,
                self.render_base,
            )
            if rendered is None:
                raise ValueError(
                    "a coefficient cannot be rendered in this language"
                )
            return rendered

        return to_term(
            self.ring,
            value,
            self.signature,
            self.name_of,
            render_coefficient,
        )


def to_polynomial(
    ring: PolynomialRing[E],
    term: T.Term,
    signature: LanguageSignature,
) -> Polynomial[E] | None:
    """Convert a term into a member of `ring`, or return None outside the fragment."""
    coefficients = ring.coefficients
    indices = {
        symbol_id: index for index, symbol_id in enumerate(ring.generators)
    }

    def convert(current: T.Term) -> Polynomial[E] | None:
        if isinstance(current, T.IntLit):
            return ring.constant(
                coefficients.mul_int(coefficients.one(), current.value)
            )
        if isinstance(current, T.RatLit):
            if not isinstance(coefficients, RationalEmbedding):
                return None
            embedding = cast(RationalEmbedding[E], coefficients)
            value = current.value
            return ring.constant(
                embedding.of_rational(value.numerator, value.denominator)
            )
        if isinstance(current, T.SymbolRef):
            index = indices.get(current.symbol_id)
            return None if index is None else ring.generator(index)
        if not isinstance(current, T.Apply) or not isinstance(
            current.operator, T.SymbolRef
        ):
            return None
        head = signature.head_of(current.operator.symbol_id)
        if head is StructuralHead.PLUS:
            total = ring.zero()
            for argument in current.arguments:
                converted = convert(argument)
                if converted is None:
                    return None
                total = ring.add(total, converted)
            return total
        if head is StructuralHead.TIMES:
            product = ring.one()
            for argument in current.arguments:
                converted = convert(argument)
                if converted is None:
                    return None
                product = ring.mul(product, converted)
            return product
        if head is StructuralHead.POWER:
            if len(current.arguments) != 2:
                return None
            base_term, exponent_term = current.arguments
            if not isinstance(exponent_term, T.IntLit) or exponent_term.value < 0:
                return None
            base = convert(base_term)
            return None if base is None else ring.pow(base, exponent_term.value)
        return None

    return convert(term)


def to_term(
    ring: PolynomialRing[E],
    value: Polynomial[E],
    signature: LanguageSignature,
    name_of: Callable[[SymbolId], str],
    render_coefficient: Callable[[E], T.Term],
) -> T.Term | None:
    """Render a polynomial member as a term, or return None without the heads."""
    if not ring.contains(value):
        raise ValueError("the polynomial belongs to another ring")
    plus_id = signature.symbol_of(StructuralHead.PLUS)
    times_id = signature.symbol_of(StructuralHead.TIMES)
    power_id = signature.symbol_of(StructuralHead.POWER)
    if plus_id is None or times_id is None or power_id is None:
        return None
    plus = T.symbol(plus_id, "Plus")
    times = T.symbol(times_id, "Times")
    power = T.symbol(power_id, "Power")
    coefficients = ring.coefficients
    if not value.terms:
        return render_coefficient(coefficients.zero())
    rendered: list[T.Term] = []
    for exponents, coefficient in value.terms:
        factors: list[T.Term] = []
        if not coefficients.is_one(coefficient):
            factors.append(render_coefficient(coefficient))
        for index, exponent in enumerate(exponents):
            if exponent == 0:
                continue
            generator_id = ring.generators[index]
            generator = T.symbol(generator_id, name_of(generator_id))
            if exponent == 1:
                factors.append(generator)
            else:
                factors.append(T.app(power, generator, T.number(exponent)))
        if not factors:
            factors.append(render_coefficient(coefficients.one()))
        rendered.append(
            factors[0] if len(factors) == 1 else T.app(times, *factors)
        )
    return rendered[0] if len(rendered) == 1 else T.app(plus, *rendered)


__all__ = [
    "ParameterPolynomialBridge",
    "PolynomialBridge",
    "SimplePolynomialBridge",
    "to_polynomial",
    "to_term",
]
