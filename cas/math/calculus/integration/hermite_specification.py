"""The `HasHermiteReduction(U, f, x, v, r)` specification.

The claim states that on region `U`,

    f = D(v) + r

and that `r` has a squarefree denominator.  The predicate is data: its
mathematical meaning lives in the independent checker, not in the shape of the
application.  The operation proposes `r` as the visible result while the
certificate carries `v` and the original `f`.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import OperatorSignature
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class HermiteVocabulary:
    """The predicate symbol this world uses for Hermite reductions."""

    symbol: SymbolId
    name: str

    @property
    def signature(self) -> OperatorSignature:
        """`(region, f, x, v, r) -> proposition`."""
        return OperatorSignature(
            (S.PROPOSITION, S.REAL, S.REAL, S.REAL, S.REAL),
            S.PROPOSITION,
        )


@dataclass(frozen=True, slots=True)
class HermiteClaim:
    """The parts of one `HasHermiteReduction` application."""

    region: T.Term
    source: T.Term
    variable: T.SymbolRef
    polynomial_part: T.Term
    remainder: T.Term


@dataclass(frozen=True, slots=True)
class HermiteCertificate:
    """The decomposition data a checker interprets."""

    region: T.Term
    source: T.Term
    variable: SymbolId
    polynomial_part: T.Term
    remainder: T.Term


def has_hermite_reduction(
    vocabulary: HermiteVocabulary,
    region: T.Term,
    source: T.Term,
    variable: T.SymbolRef,
    polynomial_part: T.Term,
    remainder: T.Term,
) -> T.Term:
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        region,
        source,
        variable,
        polynomial_part,
        remainder,
    )


def parse_hermite_reduction(
    vocabulary: HermiteVocabulary,
    term: T.Term,
) -> HermiteClaim | None:
    if not isinstance(term, T.Apply):
        return None
    if not isinstance(term.operator, T.SymbolRef):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 5:
        return None
    region, source, variable, polynomial_part, remainder = term.arguments
    if not isinstance(variable, T.SymbolRef):
        return None
    return HermiteClaim(
        region, source, variable, polynomial_part, remainder
    )


def certificate_matches_claim(
    certificate: HermiteCertificate,
    claim: HermiteClaim,
) -> bool:
    return (
        certificate.region == claim.region
        and certificate.source == claim.source
        and certificate.variable == claim.variable.symbol_id
        and certificate.polynomial_part == claim.polynomial_part
        and certificate.remainder == claim.remainder
    )


__all__ = [
    "HermiteCertificate",
    "HermiteClaim",
    "HermiteVocabulary",
    "certificate_matches_claim",
    "has_hermite_reduction",
    "parse_hermite_reduction",
]
