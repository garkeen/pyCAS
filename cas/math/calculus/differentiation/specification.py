"""The `HasDerivative(U, f, x, g)` specification.

The predicate's identity is a `SymbolId` assigned by assembly; the display name
is presentation only. This record carries the arity only so the language can
type the application — the mathematical meaning lives in the checker and its
independent verifier, never in the shape of this record.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import OperatorSignature
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class DerivativeVocabulary:
    """The predicate symbol this world uses for derivative claims."""

    symbol: SymbolId
    name: str

    @property
    def signature(self) -> OperatorSignature:
        """`(region, source, variable, candidate) -> proposition`."""
        return OperatorSignature(
            (S.PROPOSITION, S.REAL, S.REAL, S.REAL),
            S.PROPOSITION,
        )


@dataclass(frozen=True, slots=True)
class DerivativeClaim:
    """The parts of one `HasDerivative` application."""

    region: T.Term
    source: T.Term
    variable: T.SymbolRef
    candidate: T.Term


def has_derivative(
    vocabulary: DerivativeVocabulary,
    region: T.Term,
    source: T.Term,
    variable: T.SymbolRef,
    candidate: T.Term,
) -> T.Term:
    """Build the specification term. It is data until a checker accepts it."""
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        region,
        source,
        variable,
        candidate,
    )


def certificate_matches_claim(
    certificate: DerivativeCertificate,
    claim: DerivativeClaim,
) -> bool:
    """Whether a certificate names exactly the claimed derivative instance."""
    return (
        certificate.region == claim.region
        and certificate.source == claim.source
        and certificate.variable == claim.variable.symbol_id
        and certificate.candidate == claim.candidate
    )


def parse_has_derivative(
    vocabulary: DerivativeVocabulary,
    term: T.Term,
) -> DerivativeClaim | None:
    """Recognize this predicate's application, or return None."""
    if not isinstance(term, T.Apply):
        return None
    if not isinstance(term.operator, T.SymbolRef):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 4:
        return None
    region, source, variable, candidate = term.arguments
    if not isinstance(variable, T.SymbolRef):
        return None
    return DerivativeClaim(region, source, variable, candidate)


__all__ = [
    "DerivativeClaim",
    "DerivativeVocabulary",
    "certificate_matches_claim",
    "has_derivative",
    "parse_has_derivative",
]
