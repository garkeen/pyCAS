"""The `HasResultant(f, g, x, r)` specification.

The predicate states the resultant of two univariate polynomials with respect
to the declared variable.  The checker rebuilds the Sylvester matrix and
evaluates its determinant by fraction-free integer elimination, independently
of the ring's resultant routine.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import OperatorSignature
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class ResultantVocabulary:
    """The predicate symbol one world uses for resultant claims."""

    symbol: SymbolId
    name: str

    @property
    def signature(self) -> OperatorSignature:
        """`(left, right, variable, resultant) -> proposition`."""
        return OperatorSignature(
            (S.REAL, S.REAL, S.REAL, S.REAL),
            S.PROPOSITION,
        )


@dataclass(frozen=True, slots=True)
class ResultantClaim:
    left: T.Term
    right: T.Term
    variable: T.SymbolRef
    result: T.Term

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (self.left, self.right, self.result)
        ):
            raise TypeError("a resultant claim needs term arguments")
        if not isinstance(self.variable, T.SymbolRef):
            raise TypeError("a resultant claim needs a variable symbol")


@dataclass(frozen=True, slots=True)
class ResultantCertificate:
    left: T.Term
    right: T.Term
    variable: SymbolId
    result: T.Term

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (self.left, self.right, self.result)
        ):
            raise TypeError("a resultant certificate carries terms")
        if isinstance(self.variable, bool) or not isinstance(
            self.variable, int
        ):
            raise TypeError("a resultant certificate needs a variable id")


def has_resultant(
    vocabulary: ResultantVocabulary,
    left: T.Term,
    right: T.Term,
    variable: T.Term,
    result: T.Term,
) -> T.Term:
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        left,
        right,
        variable,
        result,
    )


def certificate_matches_claim(
    certificate: ResultantCertificate,
    claim: ResultantClaim,
) -> bool:
    return (
        certificate.left == claim.left
        and certificate.right == claim.right
        and certificate.variable == claim.variable.symbol_id
        and certificate.result == claim.result
    )


def parse_resultant(
    vocabulary: ResultantVocabulary,
    term: T.Term,
) -> ResultantClaim | None:
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 4:
        return None
    left, right, variable, result = term.arguments
    if not isinstance(variable, T.SymbolRef):
        return None
    return ResultantClaim(left, right, variable, result)


__all__ = [
    "ResultantCertificate",
    "ResultantClaim",
    "ResultantVocabulary",
    "certificate_matches_claim",
    "has_resultant",
    "parse_resultant",
]
