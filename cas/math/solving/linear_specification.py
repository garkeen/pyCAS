"""The `HasSolutionSet` and `HasSolutionSubset` specifications.

The predicates describe a finite set result for one polynomial equation in one
variable.  `HasSolutionSubset` states soundness only: every member is a root.
`HasSolutionSet` states soundness and completeness for the declared fragment.
The checker decides both; the operation that proposes the set is separate.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.problems import Coverage
from cas.language.signatures import OperatorSignature
from cas.syntax import term as T


class SolutionSetKind(StrEnum):
    """Which solution-set claim a specification states."""

    SOUND = "HasSolutionSubset"
    COMPLETE = "HasSolutionSet"


@dataclass(frozen=True, slots=True)
class SolutionSetVocabulary:
    """The two predicate symbols one world uses for solution sets."""

    complete_symbol: SymbolId
    complete_name: str
    sound_symbol: SymbolId
    sound_name: str

    def __post_init__(self) -> None:
        if not self.complete_name or not self.sound_name:
            raise ValueError("a solution-set predicate needs a name")
        if self.complete_symbol == self.sound_symbol:
            raise ValueError("the two solution-set predicates must differ")

    @property
    def signature(self) -> OperatorSignature:
        """`(source, variable, set) -> proposition`."""
        return OperatorSignature(
            (S.REAL, S.REAL, S.SetSort(S.REAL)),
            S.PROPOSITION,
        )


@dataclass(frozen=True, slots=True)
class SolutionSetClaim:
    """The parts of one solution-set application."""

    kind: SolutionSetKind
    source: T.Term
    variable: T.SymbolRef
    set_term: T.Term

    def __post_init__(self) -> None:
        if not isinstance(self.kind, SolutionSetKind):
            raise TypeError("a solution-set claim needs a kind")
        if not isinstance(self.source, T.Term):
            raise TypeError("a solution-set claim needs a source term")
        if not isinstance(self.variable, T.SymbolRef):
            raise TypeError("a solution-set claim needs a variable symbol")
        if not isinstance(self.set_term, T.Term):
            raise TypeError("a solution-set claim needs a set term")


@dataclass(frozen=True, slots=True)
class LinearSolutionCertificate:
    """The exact source, variable, set and coverage behind one claim."""

    source: T.Term
    variable: SymbolId
    set_term: T.Term
    coverage: Coverage

    def __post_init__(self) -> None:
        if not isinstance(self.source, T.Term):
            raise TypeError("a solution certificate needs a source term")
        if isinstance(self.variable, bool) or not isinstance(
            self.variable, int
        ):
            raise TypeError("a solution certificate needs a variable id")
        if not isinstance(self.set_term, T.Term):
            raise TypeError("a solution certificate needs a set term")
        if not isinstance(self.coverage, Coverage):
            raise TypeError("a solution certificate needs a coverage value")


def has_solution_set(
    vocabulary: SolutionSetVocabulary,
    source: T.Term,
    variable: T.Term,
    set_term: T.Term,
) -> T.Term:
    """Build a complete-solution-set specification term."""
    return T.app(
        T.symbol(vocabulary.complete_symbol, vocabulary.complete_name),
        source,
        variable,
        set_term,
    )


def has_solution_subset(
    vocabulary: SolutionSetVocabulary,
    source: T.Term,
    variable: T.Term,
    set_term: T.Term,
) -> T.Term:
    """Build a sound-solution-subset specification term."""
    return T.app(
        T.symbol(vocabulary.sound_symbol, vocabulary.sound_name),
        source,
        variable,
        set_term,
    )


def certificate_matches_claim(
    certificate: LinearSolutionCertificate,
    claim: SolutionSetClaim,
) -> bool:
    """Whether the certificate names exactly the claimed instance."""
    expected = (
        Coverage.COMPLETE_SET
        if claim.kind is SolutionSetKind.COMPLETE
        else Coverage.SOUND_SET
    )
    return (
        certificate.source == claim.source
        and certificate.variable == claim.variable.symbol_id
        and certificate.set_term == claim.set_term
        and certificate.coverage is expected
    )


def parse_solution_set(
    vocabulary: SolutionSetVocabulary,
    term: T.Term,
) -> SolutionSetClaim | None:
    """Recognize one of this vocabulary's applications, or return None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    symbol = term.operator.symbol_id
    if symbol == vocabulary.complete_symbol:
        kind = SolutionSetKind.COMPLETE
    elif symbol == vocabulary.sound_symbol:
        kind = SolutionSetKind.SOUND
    else:
        return None
    if len(term.arguments) != 3:
        return None
    source, variable, set_term = term.arguments
    if not isinstance(variable, T.SymbolRef):
        return None
    return SolutionSetClaim(kind, source, variable, set_term)


__all__ = [
    "LinearSolutionCertificate",
    "SolutionSetClaim",
    "SolutionSetKind",
    "SolutionSetVocabulary",
    "certificate_matches_claim",
    "has_solution_set",
    "has_solution_subset",
    "parse_solution_set",
]
