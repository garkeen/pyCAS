"""The `HasPolynomialGCD(f, g, x, d)` specification.

The predicate states that `d` is the monic greatest common divisor of `f` and
`g` in the declared univariate polynomial ring.  The certificate carries the
Bezout coefficients, so the checker can prove maximality without calling the
ring's gcd or xgcd search.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import OperatorSignature
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class GcdVocabulary:
    """The predicate symbol one world uses for polynomial gcd claims."""

    symbol: SymbolId
    name: str

    @property
    def signature(self) -> OperatorSignature:
        """`(left, right, variable, gcd) -> proposition`."""
        return OperatorSignature(
            (S.REAL, S.REAL, S.REAL, S.REAL),
            S.PROPOSITION,
        )


@dataclass(frozen=True, slots=True)
class GcdClaim:
    """The parts of one polynomial-gcd application."""

    left: T.Term
    right: T.Term
    variable: T.SymbolRef
    candidate: T.Term

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (self.left, self.right, self.candidate)
        ):
            raise TypeError("a gcd claim needs term arguments")
        if not isinstance(self.variable, T.SymbolRef):
            raise TypeError("a gcd claim needs a variable symbol")


@dataclass(frozen=True, slots=True)
class GcdCertificate:
    """The inputs, candidate and Bezout coefficients of one gcd claim."""

    left: T.Term
    right: T.Term
    variable: SymbolId
    candidate: T.Term
    left_coefficient: T.Term
    right_coefficient: T.Term

    def __post_init__(self) -> None:
        for item in (
            self.left,
            self.right,
            self.candidate,
            self.left_coefficient,
            self.right_coefficient,
        ):
            if not isinstance(item, T.Term):
                raise TypeError("a gcd certificate carries terms")
        if isinstance(self.variable, bool) or not isinstance(
            self.variable, int
        ):
            raise TypeError("a gcd certificate needs a variable id")


def has_gcd(
    vocabulary: GcdVocabulary,
    left: T.Term,
    right: T.Term,
    variable: T.Term,
    candidate: T.Term,
) -> T.Term:
    """Build a polynomial-gcd specification term."""
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        left,
        right,
        variable,
        candidate,
    )


def certificate_matches_claim(
    certificate: GcdCertificate,
    claim: GcdClaim,
) -> bool:
    """Whether the certificate names exactly the claimed instance."""
    return (
        certificate.left == claim.left
        and certificate.right == claim.right
        and certificate.variable == claim.variable.symbol_id
        and certificate.candidate == claim.candidate
    )


def parse_gcd(
    vocabulary: GcdVocabulary,
    term: T.Term,
) -> GcdClaim | None:
    """Recognize this predicate's application, or return None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 4:
        return None
    left, right, variable, candidate = term.arguments
    if not isinstance(variable, T.SymbolRef):
        return None
    return GcdClaim(left, right, variable, candidate)


__all__ = [
    "GcdCertificate",
    "GcdClaim",
    "GcdVocabulary",
    "certificate_matches_claim",
    "has_gcd",
    "parse_gcd",
]
