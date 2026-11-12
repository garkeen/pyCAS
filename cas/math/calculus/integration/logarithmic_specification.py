"""The `HasRationalLogAntiderivative` specification and canonical log terms.

The predicate states that on region `U`, for the variable `x`,

    source = D(polynomial_part) + sum(coef_i * D(arg_i)/arg_i)

and that `result` is the visible antiderivative expression assembled from the
same polynomial part and logarithm terms.  The mathematical identity, the
squarefree/coprime conditions on the arguments and the domain of the logarithm
branches are re-proved by the independent checker in the next slice; this
module only publishes the language-level claim shape, the certificate shape and
the canonical encoding of the finite logarithm-term set.

Canonical encoding
------------------

A logarithm term is either

    log(g)

for coefficient one, or

    Times(c, log(g))

for a nonzero rational literal ``c != 1``.  A top-level ``Times`` with
coefficient one, a zero or non-literal coefficient, a nested wrapper, a wrong
arity and a repeated coefficient are all malformed.  The term set is built with
`set_term`, so members are deduplicated and ordered by the stable structural
term order; `parse_rational_log_terms` accepts only that exact canonical order.
`rational_log_antiderivative_term` is the single visible-result constructor: it
flattens one top-level ``Plus`` of the polynomial part, omits a literal zero
polynomial part, appends the canonical log members in their set order and never
performs a second algebraic normalization.

The predicate symbol and the logarithm function symbol are supplied data, not
hardcoded names.  This slice publishes no checker, operation, bootstrap,
workflow or REPL entry and does not claim that I0 is complete.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.sets import set_members, set_term
from cas.language.signatures import (
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.syntax import term as T

LogTermEntry = tuple[Fraction, T.Term]


@dataclass(frozen=True, slots=True)
class RationalLogVocabulary:
    """The predicate and logarithm symbols one world uses for this claim."""

    symbol: SymbolId
    name: str
    log_symbol: SymbolId
    log_name: str

    def __post_init__(self) -> None:
        if isinstance(self.symbol, bool) or not isinstance(self.symbol, int):
            raise TypeError(
                "a rational-log predicate needs a SymbolId"
            )
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("a rational-log predicate needs a name")
        if isinstance(self.log_symbol, bool) or not isinstance(
            self.log_symbol, int
        ):
            raise TypeError("a rational-log predicate needs a log SymbolId")
        if not isinstance(self.log_name, str) or not self.log_name:
            raise ValueError("a rational-log predicate needs a log name")
        if self.symbol == self.log_symbol:
            raise ValueError(
                "the predicate and logarithm symbols must be distinct"
            )

    @property
    def signature(self) -> OperatorSignature:
        """`(region, source, x, v, log-terms, result) -> proposition`."""
        return OperatorSignature(
            (
                S.PROPOSITION,
                S.REAL,
                S.REAL,
                S.REAL,
                S.SetSort(S.REAL),
                S.REAL,
            ),
            S.PROPOSITION,
        )

    @property
    def log_function(self) -> T.SymbolRef:
        """The term-level symbol of the declared logarithm function."""
        return T.symbol(self.log_symbol, self.log_name)


@dataclass(frozen=True, slots=True)
class RationalLogAntiderivativeClaim:
    """The six arguments of one `HasRationalLogAntiderivative` application."""

    region: T.Term
    source: T.Term
    variable: T.SymbolRef
    polynomial_part: T.Term
    log_terms: T.Term
    result: T.Term

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (
                self.region,
                self.source,
                self.polynomial_part,
                self.log_terms,
                self.result,
            )
        ):
            raise TypeError(
                "a rational-log claim needs term arguments"
            )
        if not isinstance(self.variable, T.SymbolRef):
            raise TypeError(
                "a rational-log claim needs a variable symbol"
            )


@dataclass(frozen=True, slots=True)
class RationalLogAntiderivativeCertificate:
    """The same six fields as the claim, with the variable as a `SymbolId`.

    The certificate repeats the claimed instance so that it cannot silently
    describe another source, region, polynomial part, logarithm-term set or
    result.  The identity itself is checked independently in the next slice.
    """

    region: T.Term
    source: T.Term
    variable: SymbolId
    polynomial_part: T.Term
    log_terms: T.Term
    result: T.Term

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (
                self.region,
                self.source,
                self.polynomial_part,
                self.log_terms,
                self.result,
            )
        ):
            raise TypeError(
                "a rational-log certificate carries terms"
            )
        if isinstance(self.variable, bool) or not isinstance(
            self.variable, int
        ):
            raise TypeError(
                "a rational-log certificate needs a variable id"
            )


def has_rational_log_antiderivative(
    vocabulary: RationalLogVocabulary,
    region: T.Term,
    source: T.Term,
    variable: T.SymbolRef,
    polynomial_part: T.Term,
    log_terms: T.Term,
    result: T.Term,
) -> T.Term:
    """Build a rational-log antiderivative specification term."""
    if not all(
        isinstance(item, T.Term)
        for item in (
            region,
            source,
            polynomial_part,
            log_terms,
            result,
        )
    ):
        raise TypeError(
            "a rational-log specification needs terms"
        )
    if not isinstance(variable, T.SymbolRef):
        raise TypeError(
            "a rational-log specification needs a variable symbol"
        )
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        region,
        source,
        variable,
        polynomial_part,
        log_terms,
        result,
    )


def parse_rational_log_antiderivative(
    vocabulary: RationalLogVocabulary,
    term: T.Term,
) -> RationalLogAntiderivativeClaim | None:
    """Recognize this predicate's application, or return None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 6:
        return None
    region, source, variable, polynomial_part, log_terms, result = (
        term.arguments
    )
    if not isinstance(variable, T.SymbolRef):
        return None
    return RationalLogAntiderivativeClaim(
        region,
        source,
        variable,
        polynomial_part,
        log_terms,
        result,
    )


def certificate_matches_claim(
    certificate: RationalLogAntiderivativeCertificate,
    claim: RationalLogAntiderivativeClaim,
) -> bool:
    """Whether the certificate names exactly the claimed instance."""
    return (
        certificate.region == claim.region
        and certificate.source == claim.source
        and certificate.variable == claim.variable.symbol_id
        and certificate.polynomial_part == claim.polynomial_part
        and certificate.log_terms == claim.log_terms
        and certificate.result == claim.result
    )


def _rational_literal(term: T.Term) -> Fraction | None:
    """The exact value of an `IntLit`/`RatLit`, or None for another term."""
    if isinstance(term, T.IntLit):
        return Fraction(term.value)
    if isinstance(term, T.RatLit):
        return term.value
    return None


def _head_of(
    signature: LanguageSignature,
    term: T.Term,
) -> StructuralHead | None:
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    return signature.head_of(term.operator.symbol_id)


def _set_arguments(
    signature: LanguageSignature,
    term: T.Term,
) -> tuple[T.Term, ...] | None:
    """The raw arguments of a `Set` application, or None."""
    if _head_of(signature, term) is not StructuralHead.SET:
        return None
    assert isinstance(term, T.Apply)
    return tuple(term.arguments)


def _log_argument(
    log_symbol: T.SymbolRef,
    term: T.Term,
) -> T.Term | None:
    """The `g` of a bare `log(g)` application, or None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    if term.operator.symbol_id != log_symbol.symbol_id:
        return None
    if len(term.arguments) != 1:
        return None
    return term.arguments[0]


def _parse_log_member(
    signature: LanguageSignature,
    log_symbol: T.SymbolRef,
    member: T.Term,
) -> LogTermEntry | None:
    """Parse one canonical log-term member, or None when malformed."""
    argument = _log_argument(log_symbol, member)
    if argument is not None:
        return Fraction(1), argument
    if _head_of(signature, member) is not StructuralHead.TIMES:
        return None
    assert isinstance(member, T.Apply)
    if len(member.arguments) != 2:
        return None
    coefficient_term, wrapped = member.arguments
    coefficient = _rational_literal(coefficient_term)
    if coefficient is None or coefficient == 0 or coefficient == 1:
        return None
    argument = _log_argument(log_symbol, wrapped)
    if argument is None:
        return None
    return coefficient, argument


def rational_log_term(
    signature: LanguageSignature,
    log_symbol: T.SymbolRef,
    coefficient: Fraction,
    argument_term: T.Term,
) -> T.Term:
    """Build one canonical log-term member for `coefficient * log(arg)`.

    Coefficient one is the bare `log(arg)`; every other nonzero rational is a
    two-argument ``Times(coefficient, log(arg))``.  Zero and one coefficients,
    non-rational coefficients and non-term arguments are refused.
    """
    if not isinstance(log_symbol, T.SymbolRef):
        raise TypeError("a log term needs a log function symbol")
    if not isinstance(coefficient, Fraction):
        raise TypeError("a log term needs a Fraction coefficient")
    if coefficient == 0:
        raise ValueError("a log term coefficient must be nonzero")
    if not isinstance(argument_term, T.Term):
        raise TypeError("a log term needs a term argument")
    logged = T.app(log_symbol, argument_term)
    if coefficient == 1:
        return logged
    return T.app(
        signature.head_term(StructuralHead.TIMES),
        T.number(coefficient),
        logged,
    )


def rational_log_term_set(
    signature: LanguageSignature,
    log_symbol: T.SymbolRef,
    entries: tuple[LogTermEntry, ...],
) -> T.Term:
    """Build the canonical log-term set for `(coefficient, argument)` entries.

    Coefficients are nonzero and distinct; a duplicate coefficient is an
    encoding error, not a second term.  The members are built only through
    `rational_log_term` and collected by `set_term`, which fixes the stable
    structural order.
    """
    if not isinstance(entries, tuple):
        raise TypeError("a log-term set needs a tuple of entries")
    checked: list[LogTermEntry] = []
    seen: set[Fraction] = set()
    for entry in entries:
        if not isinstance(entry, tuple) or len(entry) != 2:
            raise TypeError(
                "a log-term entry must be a (coefficient, argument) pair"
            )
        coefficient, argument = entry
        if not isinstance(coefficient, Fraction):
            raise TypeError("a log-term coefficient must be a Fraction")
        if coefficient == 0:
            raise ValueError("a log-term coefficient must be nonzero")
        if not isinstance(argument, T.Term):
            raise TypeError("a log-term argument must be a term")
        if coefficient in seen:
            raise ValueError(
                "a log-term coefficient appears more than once"
            )
        seen.add(coefficient)
        checked.append((coefficient, argument))
    members = tuple(
        rational_log_term(signature, log_symbol, coefficient, argument)
        for coefficient, argument in checked
    )
    return set_term(signature, members)


def parse_rational_log_terms(
    signature: LanguageSignature,
    log_symbol: T.SymbolRef,
    terms: T.Term,
) -> tuple[LogTermEntry, ...] | None:
    """Parse exactly the canonical log-term set, or return None.

    The term must be a `Set` application whose raw members are already in the
    canonical structural order.  Bare `log(g)` members decode to coefficient
    one; ``Times(c, log(g))`` decodes only for a nonzero rational literal
    ``c != 1`` and exactly two arguments.  A zero or non-literal coefficient, a
    nested wrapper, a wrong arity, a repeated coefficient and a non-canonical
    member order are all malformed.
    """
    if not isinstance(log_symbol, T.SymbolRef):
        raise TypeError("a log-term parser needs a log function symbol")
    raw = _set_arguments(signature, terms)
    if raw is None:
        return None
    canonical = set_members(terms, signature)
    if canonical is None or raw != canonical:
        return None
    entries: list[LogTermEntry] = []
    seen: set[Fraction] = set()
    for member in canonical:
        parsed = _parse_log_member(signature, log_symbol, member)
        if parsed is None:
            return None
        coefficient, argument = parsed
        if coefficient in seen:
            return None
        seen.add(coefficient)
        entries.append((coefficient, argument))
    return tuple(entries)


def rational_log_antiderivative_term(
    signature: LanguageSignature,
    polynomial_part: T.Term,
    log_terms: T.Term,
) -> T.Term:
    """Build the single visible antiderivative expression.

    With no log terms the polynomial part is returned unchanged.  A literal
    zero polynomial part is omitted when log terms exist; a top-level ``Plus``
    of the polynomial part is flattened once; the canonical log members keep
    their set order.  A non-`Set` or non-canonical-order ``log_terms`` is
    refused rather than silently reordered or normalized; member encoding is
    validated separately by `parse_rational_log_terms`, which needs the log
    symbol.
    """
    if not isinstance(polynomial_part, T.Term):
        raise TypeError("an antiderivative result needs a polynomial-part term")
    if not isinstance(log_terms, T.Term):
        raise TypeError("an antiderivative result needs a log-term set")
    raw = _set_arguments(signature, log_terms)
    if raw is None:
        raise ValueError("the log terms must be a Set application")
    canonical = set_members(log_terms, signature)
    if canonical is None or raw != canonical:
        raise ValueError("the log terms must be in canonical set order")
    if not canonical:
        return polynomial_part
    value = _rational_literal(polynomial_part)
    if value is not None and value == 0:
        parts: tuple[T.Term, ...] = ()
    elif _head_of(signature, polynomial_part) is StructuralHead.PLUS:
        assert isinstance(polynomial_part, T.Apply)
        parts = tuple(polynomial_part.arguments)
    else:
        parts = (polynomial_part,)
    combined = parts + canonical
    if len(combined) == 1:
        return combined[0]
    return T.app(
        signature.head_term(StructuralHead.PLUS), *combined
    )


__all__ = [
    "LogTermEntry",
    "RationalLogAntiderivativeCertificate",
    "RationalLogAntiderivativeClaim",
    "RationalLogVocabulary",
    "certificate_matches_claim",
    "has_rational_log_antiderivative",
    "parse_rational_log_antiderivative",
    "parse_rational_log_terms",
    "rational_log_antiderivative_term",
    "rational_log_term",
    "rational_log_term_set",
]
