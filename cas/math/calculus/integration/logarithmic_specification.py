"""The `HasRationalLogAntiderivative` specification and canonical log terms.

The predicate states that on region `U`, for the variable `x`,

    source = D(polynomial_part) + sum(coef_i * D(arg_i)/arg_i)

and that `result` is the visible antiderivative expression assembled from the
same polynomial part and logarithm terms.  `polynomial_part` is the
non-logarithmic rational part (the Hermite `v` plus any polynomial
antiderivative); despite the historical name it need not itself be a
polynomial.  The mathematical identity, the squarefree/coprime conditions on
the arguments and the domain of the logarithm branches are re-proved by the
independent checker in the next slice; this module only publishes the
language-level claim shape, the certificate shape and the canonical encoding of
the finite logarithm-term set.

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
hardcoded names.  `LogFunctionSemantics` ties the checker and operation to the
declared real-logarithm law: its domain and derivative factor are instantiated
from the admitted `FunctionSymbol` of an `ElementaryLibrary`, never rebuilt by
hand.  The completion slice of I0 (algebraic residues, RootSum, real branches
and the Risch tower) remains open.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from cas.foundation.ids import SymbolId
from cas.kernel.trust import BasisRef
from cas.language import sorts as S
from cas.language.declarations import (
    DOMAIN_ARGUMENT,
    Compare,
    LawExpr,
    Name,
    Num,
    Power,
    numeric_value,
)
from cas.language.sets import set_members, set_term
from cas.language.signatures import (
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.math.elementary.declarations import (
    ElementaryLibrary,
    FunctionSymbol,
)
from cas.syntax import term as T

LogTermEntry = tuple[Fraction, T.Term]


def _is_positive_argument_condition(expression: LawExpr | None) -> bool:
    """Whether the declaration is exactly ``u > 0``."""
    return (
        isinstance(expression, Compare)
        and expression.operator == ">"
        and isinstance(expression.left, Name)
        and expression.left.name == DOMAIN_ARGUMENT
        and isinstance(expression.right, Num)
        and expression.right.value == 0
    )


def _is_inverse_argument_body(expression: LawExpr) -> bool:
    """Whether the derivative body is exactly ``u^(-1)``.

    The declaration parser represents the exponent as ``Negate(Num(1))``; the
    exact numeric value is the authority, so both that canonical form and a
    direct ``Num(-1)`` are accepted.
    """
    return (
        isinstance(expression, Power)
        and isinstance(expression.base, Name)
        and expression.base.name == DOMAIN_ARGUMENT
        and numeric_value(expression.exponent) == -1
    )


@dataclass(frozen=True, slots=True)
class LogFunctionSemantics:
    """The declared real-logarithm law consumed by the rational-integration slice.

    The record is a structural view of one admitted `FunctionSymbol`, not a
    second declaration source.  It accepts exactly the declaration fragment

        log : Real -> Real on u > 0
        derivative log(u) = u^(-1) on u > 0

    so the rational-logarithmic fragment cannot attach itself to a different
    ``log`` symbol or a different derivative law.  `domain` and
    `derivative_factor` instantiate the declaration through
    `ElementaryLibrary.instantiate`; the trusted basis, when present, is the
    library's `BasisRef`.
    """

    library: ElementaryLibrary
    function: FunctionSymbol

    def __post_init__(self) -> None:
        if not isinstance(self.library, ElementaryLibrary):
            raise TypeError(
                "logarithm semantics need an elementary library"
            )
        if not isinstance(self.function, FunctionSymbol):
            raise TypeError(
                "logarithm semantics need the declared function symbol"
            )
        if self.library.function_for(self.function.symbol) != self.function:
            raise ValueError(
                "the logarithm function is not the library's admitted function"
            )
        if self.function.arguments != (S.REAL,):
            raise ValueError(
                "the logarithm declaration must take exactly one Real argument"
            )
        if self.function.result is not S.REAL:
            raise ValueError(
                "the logarithm declaration must return Real"
            )
        if not _is_positive_argument_condition(self.function.domain):
            raise ValueError(
                "the logarithm domain must be exactly `u > 0`"
            )
        law = self.function.law
        if law is None:
            raise ValueError(
                "the logarithm declaration needs a derivative law"
            )
        if law.argument != DOMAIN_ARGUMENT:
            raise ValueError(
                "the logarithm derivative law must use the domain argument "
                f"{DOMAIN_ARGUMENT!r}"
            )
        if not _is_positive_argument_condition(law.condition):
            raise ValueError(
                "the logarithm derivative law condition must be exactly "
                "`u > 0`"
            )
        if not _is_inverse_argument_body(law.body):
            raise ValueError(
                "the logarithm derivative law body must be exactly `u^(-1)`"
            )

    @property
    def symbol(self) -> SymbolId:
        """The declared logarithm symbol."""
        return self.function.symbol

    @property
    def name(self) -> str:
        """The declared logarithm name."""
        return self.function.name

    @property
    def basis(self) -> BasisRef | None:
        """The library's trusted basis, or None when the library has none."""
        return self.library.basis

    def domain(
        self, argument: T.Term, signature: LanguageSignature
    ) -> T.Term:
        """Instantiate the declared ``u > 0`` domain at `argument`."""
        if not isinstance(argument, T.Term):
            raise TypeError("a logarithm domain needs an argument term")
        if not isinstance(signature, LanguageSignature):
            raise TypeError("a logarithm domain needs a language signature")
        assert self.function.domain is not None
        return self.library.instantiate(
            self.function.domain,
            DOMAIN_ARGUMENT,
            argument,
            signature,
        )

    def derivative_factor(
        self, argument: T.Term, signature: LanguageSignature
    ) -> T.Term:
        """Instantiate the declared derivative body ``u^(-1)`` at `argument`."""
        if not isinstance(argument, T.Term):
            raise TypeError(
                "a logarithm derivative factor needs an argument term"
            )
        if not isinstance(signature, LanguageSignature):
            raise TypeError(
                "a logarithm derivative factor needs a language signature"
            )
        assert self.function.law is not None
        return self.library.instantiate(
            self.function.law.body,
            DOMAIN_ARGUMENT,
            argument,
            signature,
        )


@dataclass(frozen=True, slots=True)
class RationalLogVocabulary:
    """The predicate and logarithm symbols one world uses for this claim.

    `semantics` is optional only because `_start` creates the vocabulary before
    the elementary declaration library is built.  Checker and operation
    construction require it; it must name the same function as `log_symbol`.
    """

    symbol: SymbolId
    name: str
    log_symbol: SymbolId
    log_name: str
    semantics: LogFunctionSemantics | None = None

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
        if self.semantics is not None:
            if not isinstance(self.semantics, LogFunctionSemantics):
                raise TypeError(
                    "a rational-log vocabulary needs log-function semantics"
                )
            if self.semantics.function.symbol != self.log_symbol:
                raise ValueError(
                    "the logarithm semantics does not name the vocabulary's "
                    "log symbol"
                )
            if self.semantics.function.name != self.log_name:
                raise ValueError(
                    "the logarithm semantics does not name the vocabulary's "
                    "log name"
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


def require_log_semantics(
    vocabulary: RationalLogVocabulary,
) -> LogFunctionSemantics:
    """The vocabulary's declared logarithm semantics, or a precise refusal.

    Checker and operation construction require the data-backed declaration; a
    bare symbol pair is not enough to claim the real-logarithmic fragment.
    """
    if not isinstance(vocabulary, RationalLogVocabulary):
        raise TypeError(
            "a rational-log vocabulary is required for logarithm semantics"
        )
    semantics = vocabulary.semantics
    if semantics is None:
        raise ValueError(
            "the rational-log vocabulary has no declared logarithm semantics"
        )
    if semantics.function.symbol != vocabulary.log_symbol:
        raise ValueError(
            "the declared logarithm semantics does not name the vocabulary's "
            "log symbol"
        )
    if semantics.function.name != vocabulary.log_name:
        raise ValueError(
            "the declared logarithm semantics does not name the vocabulary's "
            "log name"
        )
    return semantics


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
    "LogFunctionSemantics",
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
    "require_log_semantics",
]
