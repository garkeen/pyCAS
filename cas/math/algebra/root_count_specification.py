"""The `HasRootCount(p, a, b, n)` real-root-count specification.

The predicate states that the squarefree univariate polynomial `p` has exactly
`n` distinct real roots in the open interval `(a, b)`.  The certificate carries
the Sturm chain itself, so the independent checker can rebuild the chain
recurrence and sign variations without calling the search algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import OperatorSignature
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class RootCountVocabulary:
    """The predicate symbol one world uses for real-root-count claims."""

    symbol: SymbolId
    name: str

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a root-count predicate needs a name")

    @property
    def signature(self) -> OperatorSignature:
        """`(polynomial, lower, upper, count) -> proposition`."""
        return OperatorSignature(
            (S.REAL, S.REAL, S.REAL, S.REAL),
            S.PROPOSITION,
        )


@dataclass(frozen=True, slots=True)
class RootCountClaim:
    """The parts of one `HasRootCount` application."""

    polynomial: T.Term
    lower: T.Term
    upper: T.Term
    count: T.Term

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (
                self.polynomial,
                self.lower,
                self.upper,
                self.count,
            )
        ):
            raise TypeError("a root-count claim needs term arguments")


@dataclass(frozen=True, slots=True)
class RootCountCertificate:
    """The inputs, claimed count and Sturm chain behind one count claim.

    The chain is a sequence of terms in the same variable as the polynomial.
    It is not trusted as a result: the checker independently elaborates every
    entry and verifies the Sturm recurrence before recomputing the count.
    """

    polynomial: T.Term
    lower: T.Term
    upper: T.Term
    count: T.Term
    chain: tuple[T.Term, ...]

    def __post_init__(self) -> None:
        for item in (
            self.polynomial,
            self.lower,
            self.upper,
            self.count,
        ):
            if not isinstance(item, T.Term):
                raise TypeError("a root-count certificate carries terms")
        chain = tuple(self.chain)
        if not chain:
            raise ValueError("a root-count certificate needs a Sturm chain")
        if any(not isinstance(item, T.Term) for item in chain):
            raise TypeError("a Sturm chain carries terms")
        object.__setattr__(self, "chain", chain)


def has_root_count(
    vocabulary: RootCountVocabulary,
    polynomial: T.Term,
    lower: T.Term,
    upper: T.Term,
    count: T.Term,
) -> T.Term:
    """Build a real-root-count specification term."""
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        polynomial,
        lower,
        upper,
        count,
    )


def certificate_matches_claim(
    certificate: RootCountCertificate,
    claim: RootCountClaim,
) -> bool:
    """Whether the certificate names exactly the claimed instance."""
    return (
        certificate.polynomial == claim.polynomial
        and certificate.lower == claim.lower
        and certificate.upper == claim.upper
        and certificate.count == claim.count
    )


def parse_root_count(
    vocabulary: RootCountVocabulary,
    term: T.Term,
) -> RootCountClaim | None:
    """Recognize this predicate's application, or return None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 4:
        return None
    polynomial, lower, upper, count = term.arguments
    return RootCountClaim(polynomial, lower, upper, count)


__all__ = [
    "RootCountCertificate",
    "RootCountClaim",
    "RootCountVocabulary",
    "certificate_matches_claim",
    "has_root_count",
    "parse_root_count",
]
