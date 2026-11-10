"""The `HasRootIsolation(p, intervals)` real-root-isolation specification.

The predicate states that the finite set of open rational intervals names every
distinct real root of the squarefree univariate polynomial `p`, exactly one root
per interval.  An interval is a structural language value `Interval(lo, hi)`;
it is not a mathematical function and carries no root by itself.  The
certificate carries the polynomial, the rational coverage bound and the Sturm
chain.  The interval set itself is the result candidate, so it is not repeated
inside the certificate.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import OperatorSignature
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class RootIsolationVocabulary:
    """The predicate and interval symbols one world uses for isolation claims."""

    symbol: SymbolId
    name: str
    interval_symbol: SymbolId
    interval_name: str = "Interval"

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a root-isolation predicate needs a name")
        if not self.interval_name:
            raise ValueError("a root-isolation interval needs a name")

    @property
    def signature(self) -> OperatorSignature:
        """`(polynomial, set-of-intervals) -> proposition`."""
        return OperatorSignature(
            (S.REAL, S.SetSort(S.IntervalSort())),
            S.PROPOSITION,
        )

    @property
    def interval_signature(self) -> OperatorSignature:
        """`(lower, upper) -> interval`; language data, not a function value."""
        return OperatorSignature(
            (S.REAL, S.REAL),
            S.IntervalSort(),
        )

    def interval(self, lower: T.Term, upper: T.Term) -> T.Term:
        """Build one `Interval(lower, upper)` term in this vocabulary."""
        if not isinstance(lower, T.Term) or not isinstance(upper, T.Term):
            raise TypeError("an interval needs term endpoints")
        return T.app(
            T.symbol(self.interval_symbol, self.interval_name),
            lower,
            upper,
        )


@dataclass(frozen=True, slots=True)
class RootIsolationClaim:
    """The parts of one `HasRootIsolation` application."""

    polynomial: T.Term
    intervals: T.Term

    def __post_init__(self) -> None:
        if not isinstance(self.polynomial, T.Term):
            raise TypeError("a root-isolation claim needs a polynomial term")
        if not isinstance(self.intervals, T.Term):
            raise TypeError("a root-isolation claim needs an interval-set term")


@dataclass(frozen=True, slots=True)
class RootIsolationCertificate:
    """The polynomial, rational coverage bound and supplied Sturm chain."""

    polynomial: T.Term
    bound: T.Term
    chain: tuple[T.Term, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.polynomial, T.Term):
            raise TypeError(
                "a root-isolation certificate needs a polynomial term"
            )
        if not isinstance(self.bound, T.Term):
            raise TypeError("a root-isolation certificate needs a bound term")
        chain = tuple(self.chain)
        if not chain:
            raise ValueError("a root-isolation certificate needs a Sturm chain")
        if any(not isinstance(item, T.Term) for item in chain):
            raise TypeError("a Sturm chain carries terms")
        object.__setattr__(self, "chain", chain)


def has_root_isolation(
    vocabulary: RootIsolationVocabulary,
    polynomial: T.Term,
    intervals: T.Term,
) -> T.Term:
    """Build a real-root-isolation specification term."""
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        polynomial,
        intervals,
    )


def certificate_matches_claim(
    certificate: RootIsolationCertificate,
    claim: RootIsolationClaim,
) -> bool:
    """Whether the certificate names exactly the claimed polynomial.

    The interval set is the candidate, not a certificate field; the checker
    compares it directly with the claim.
    """
    return certificate.polynomial == claim.polynomial


def parse_root_isolation(
    vocabulary: RootIsolationVocabulary,
    term: T.Term,
) -> RootIsolationClaim | None:
    """Recognize this predicate's application, or return None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 2:
        return None
    polynomial, intervals = term.arguments
    return RootIsolationClaim(polynomial, intervals)


__all__ = [
    "RootIsolationCertificate",
    "RootIsolationClaim",
    "RootIsolationVocabulary",
    "certificate_matches_claim",
    "has_root_isolation",
    "parse_root_isolation",
]
