"""The `HasFactorization(source, variable, unit, factors)` specification.

The predicate states that the polynomial `source` in the request's univariate
ring factors as

    source == unit * product(factor**multiplicity)

over ``Q[x]``, where `unit` is a nonzero rational literal, every factor is a
monic nonconstant polynomial and every multiplicity is a positive integer.
The factor argument is a finite set of *encoded* factors: a bare polynomial term
has multiplicity one, and a top-level ``Power(f, m)`` with an integer ``m >= 2``
is the multiplicity wrapper for ``f``.  A top-level ``Power`` is therefore never
a polynomial factor itself; ``x**2`` in the factor set means "``x`` with
multiplicity two".  This encoding is the single contract shared by the future
operation and the independent checker, and `factorization_product_term` is the
single constructor for the visible product a candidate must equal.

The certificate carries the source, the claimed unit and factor set, the radical
(the product of the distinct factors) and a Hensel irreducibility witness.  The
witness is certificate data, not an algebra search: it records a prime, a
precision and the lifted modular factors.  The independent checker re-proves the
witness from the low-level integer and modular primitives and enumerates the
recombination candidates itself.

This module publishes only the language-level claim shape and the encoded
factor-set contract.  The low-level search lives in
``cas.algebra.factorization``; the independent checker is
``cas.math.algebra.factorization_checker``.  No operation, bootstrap, workflow
or REPL entry is part of this slice, and the slice does not claim that ``A2`` is
complete.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.sets import set_members, set_term
from cas.language.signatures import (
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.syntax import term as T

FactorEntry: TypeAlias = tuple[T.Term, int]


@dataclass(frozen=True, slots=True)
class FactorizationVocabulary:
    """The predicate symbol one world uses for factorization claims."""

    symbol: SymbolId
    name: str

    def __post_init__(self) -> None:
        if isinstance(self.symbol, bool) or not isinstance(self.symbol, int):
            raise TypeError("a factorization predicate needs a SymbolId")
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("a factorization predicate needs a name")

    @property
    def signature(self) -> OperatorSignature:
        """`(source, variable, unit, factor-set) -> proposition`."""
        return OperatorSignature(
            (S.REAL, S.REAL, S.REAL, S.SetSort(S.REAL)),
            S.PROPOSITION,
        )


@dataclass(frozen=True, slots=True)
class FactorizationClaim:
    """The four arguments of one `HasFactorization` application."""

    source: T.Term
    variable: T.SymbolRef
    unit: T.Term
    factors: T.Term

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (self.source, self.unit, self.factors)
        ):
            raise TypeError("a factorization claim needs term arguments")
        if not isinstance(self.variable, T.SymbolRef):
            raise TypeError("a factorization claim needs a variable symbol")


@dataclass(frozen=True, slots=True)
class HenselIrreducibilityWitness:
    """A lifted modular factorization as certificate data.

    ``prime`` and ``precision`` are structurally positive integers and
    ``lifted`` is a nonempty tuple of polynomial terms.  The record validates
    only that structure: it does not claim that ``prime`` is prime, that the
    congruence holds, or that the lifted factors are irreducible.  Those facts
    belong to the independent checker, which re-proves them from the candidate
    radical.
    """

    prime: int
    precision: int
    lifted: tuple[T.Term, ...]

    def __post_init__(self) -> None:
        if isinstance(self.prime, bool) or not isinstance(self.prime, int):
            raise TypeError("a Hensel witness prime must be an integer")
        if self.prime < 1:
            raise ValueError("a Hensel witness prime must be positive")
        if isinstance(self.precision, bool) or not isinstance(
            self.precision, int
        ):
            raise TypeError("a Hensel witness precision must be an integer")
        if self.precision < 1:
            raise ValueError("a Hensel witness precision must be positive")
        lifted = tuple(self.lifted)
        if not lifted:
            raise ValueError("a Hensel witness needs at least one factor")
        if any(not isinstance(item, T.Term) for item in lifted):
            raise TypeError("a Hensel witness carries polynomial terms")
        object.__setattr__(self, "lifted", lifted)


@dataclass(frozen=True, slots=True)
class FactorizationCertificate:
    """The source, encoded factors, radical and irreducibility witness.

    The certificate repeats the claimed source, variable, unit and factor set so
    that it cannot silently describe another instance.  ``radical`` must be the
    canonical product of the distinct factor bases.  The checker requires
    ``irreducibility`` exactly when a claimed base has degree at least two.
    """

    source: T.Term
    variable: SymbolId
    unit: T.Term
    factors: T.Term
    radical: T.Term
    irreducibility: HenselIrreducibilityWitness | None = None

    def __post_init__(self) -> None:
        if not all(
            isinstance(item, T.Term)
            for item in (
                self.source,
                self.unit,
                self.factors,
                self.radical,
            )
        ):
            raise TypeError("a factorization certificate carries terms")
        if isinstance(self.variable, bool) or not isinstance(
            self.variable, int
        ):
            raise TypeError("a factorization certificate needs a variable id")
        if self.irreducibility is not None and not isinstance(
            self.irreducibility, HenselIrreducibilityWitness
        ):
            raise TypeError(
                "a factorization certificate irreducibility field must be a "
                "Hensel witness or None"
            )


def has_factorization(
    vocabulary: FactorizationVocabulary,
    source: T.Term,
    variable: T.Term,
    unit: T.Term,
    factors: T.Term,
) -> T.Term:
    """Build a factorization specification term."""
    if not all(
        isinstance(item, T.Term)
        for item in (source, variable, unit, factors)
    ):
        raise TypeError("a factorization specification needs terms")
    return T.app(
        T.symbol(vocabulary.symbol, vocabulary.name),
        source,
        variable,
        unit,
        factors,
    )


def parse_factorization(
    vocabulary: FactorizationVocabulary,
    term: T.Term,
) -> FactorizationClaim | None:
    """Recognize this predicate's application, or return None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    if term.operator.symbol_id != vocabulary.symbol:
        return None
    if len(term.arguments) != 4:
        return None
    source, variable, unit, factors = term.arguments
    if not isinstance(variable, T.SymbolRef):
        return None
    return FactorizationClaim(source, variable, unit, factors)


def certificate_matches_claim(
    certificate: FactorizationCertificate,
    claim: FactorizationClaim,
) -> bool:
    """Whether the certificate names exactly the claimed instance.

    ``radical`` and ``irreducibility`` are certificate data and have no claim
    counterpart; the checker validates them separately.
    """
    return (
        certificate.source == claim.source
        and certificate.variable == claim.variable.symbol_id
        and certificate.unit == claim.unit
        and certificate.factors == claim.factors
    )


def rational_literal(term: T.Term) -> Fraction | None:
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


def _checked_entries(
    signature: LanguageSignature,
    entries: tuple[FactorEntry, ...],
) -> tuple[FactorEntry, ...]:
    """Validate the factor entries and reject duplicate or ambiguous bases.

    This is the single entry validation shared by the set, product and radical
    builders.  A multiplicity is a positive integer; ``True`` is not accepted
    as one.  Duplicate bases are an encoding error, not a second factor.  A
    base that is itself a top-level ``Power`` cannot be represented: the
    encoding reserves that position for the multiplicity wrapper and parsing
    would read it back as a different entry.
    """
    checked: list[FactorEntry] = []
    seen: set[T.Term] = set()
    for entry in entries:
        if not isinstance(entry, tuple) or len(entry) != 2:
            raise TypeError(
                "a factorization entry must be a (factor, multiplicity) pair"
            )
        factor, multiplicity = entry
        if not isinstance(factor, T.Term):
            raise TypeError("a factorization factor must be a term")
        if _head_of(signature, factor) is StructuralHead.POWER:
            raise ValueError(
                "a factor base cannot be a top-level Power multiplicity "
                "wrapper"
            )
        if isinstance(multiplicity, bool) or not isinstance(
            multiplicity, int
        ):
            raise TypeError("a factorization multiplicity must be an integer")
        if multiplicity < 1:
            raise ValueError("a factorization multiplicity must be positive")
        if factor in seen:
            raise ValueError("a factorization factor appears more than once")
        seen.add(factor)
        checked.append((factor, multiplicity))
    return tuple(checked)


def _set_arguments(
    signature: LanguageSignature,
    term: T.Term,
) -> tuple[T.Term, ...] | None:
    """The raw arguments of a `Set` application, or None."""
    if _head_of(signature, term) is not StructuralHead.SET:
        return None
    assert isinstance(term, T.Apply)
    return tuple(term.arguments)


def factorization_factor_set(
    signature: LanguageSignature,
    entries: tuple[FactorEntry, ...],
) -> T.Term:
    """Build the canonical encoded factor set for `entries`.

    A multiplicity of one is a bare base; every higher multiplicity is a
    top-level ``Power(base, multiplicity)`` wrapper.  The result is built with
    `set_term`, so members are deduplicated and ordered structurally.
    """
    checked = _checked_entries(signature, entries)
    members: list[T.Term] = []
    power: T.SymbolRef | None = None
    for factor, multiplicity in checked:
        if multiplicity == 1:
            members.append(factor)
            continue
        if power is None:
            power = signature.head_term(StructuralHead.POWER)
        members.append(T.app(power, factor, T.number(multiplicity)))
    return set_term(signature, tuple(members))


def _parse_factor_member(
    signature: LanguageSignature,
    member: T.Term,
) -> FactorEntry | None:
    """Parse one encoded factor member, or None when the wrapper is malformed."""
    if _head_of(signature, member) is not StructuralHead.POWER:
        return member, 1
    assert isinstance(member, T.Apply)
    if len(member.arguments) != 2:
        return None
    factor, exponent = member.arguments
    if not isinstance(exponent, T.IntLit):
        return None
    if exponent.value < 2:
        return None
    if _head_of(signature, factor) is StructuralHead.POWER:
        return None
    return factor, exponent.value


def parse_factor_entries(
    signature: LanguageSignature,
    factors: T.Term,
) -> tuple[FactorEntry, ...] | None:
    """Parse exactly the canonical encoded factor set, or return None.

    The term must be a `Set` application whose raw members are already in the
    canonical deduplicated structural order.  A top-level ``Power(f, m)`` must
    have an integer ``m >= 2``; ``Power(f, 1)``, a non-integer or non-positive
    exponent, a wrong arity and a bare ``Power`` misuse are all malformed.  A
    bare member has multiplicity one.  Duplicate bases are malformed.
    """
    raw = _set_arguments(signature, factors)
    if raw is None:
        return None
    canonical = set_members(factors, signature)
    if canonical is None or raw != canonical:
        return None
    entries: list[FactorEntry] = []
    seen: set[T.Term] = set()
    for member in canonical:
        parsed = _parse_factor_member(signature, member)
        if parsed is None:
            return None
        factor, multiplicity = parsed
        if factor in seen:
            return None
        seen.add(factor)
        entries.append((factor, multiplicity))
    return tuple(entries)


def factorization_product_term(
    signature: LanguageSignature,
    unit: T.Term,
    factors: T.Term,
) -> T.Term | None:
    """Build the visible product of the claimed unit and factor set.

    The unit must be a nonzero rational literal.  With no factors the product is
    the unit itself (including ``1``).  With factors, the unit ``1`` is omitted
    unless there are no factors; a single factor with unit ``1`` stays a bare
    factor; every other case is a ``Times`` application.  A multiplicity of one
    renders a bare base and ``m >= 2`` renders ``Power(base, m)``.  The function
    returns None for a malformed unit or factor set instead of inventing a
    second normalization.
    """
    unit_value = rational_literal(unit)
    if unit_value is None or unit_value == 0:
        return None
    entries = parse_factor_entries(signature, factors)
    if entries is None:
        return None
    if not entries:
        return unit
    power: T.SymbolRef | None = None
    rendered: list[T.Term] = []
    for factor, multiplicity in entries:
        if multiplicity == 1:
            rendered.append(factor)
            continue
        if power is None:
            power = signature.head_term(StructuralHead.POWER)
        rendered.append(T.app(power, factor, T.number(multiplicity)))
    factor_terms = tuple(rendered)
    if len(factor_terms) == 1 and unit_value == 1:
        return factor_terms[0]
    times = signature.head_term(StructuralHead.TIMES)
    if unit_value == 1:
        return T.app(times, *factor_terms)
    return T.app(times, unit, *factor_terms)


def factorization_radical_term(
    signature: LanguageSignature,
    entries: tuple[FactorEntry, ...],
) -> T.Term:
    """Build the product of the distinct factor bases, without the unit.

    The empty factor set is the constant ``1``.  Multiplicities are ignored and
    duplicate bases are refused: the radical is a product of distinct bases.
    The bases are emitted in the stable structural term order, so the result
    does not depend on the order the entries were supplied in.
    """
    checked = _checked_entries(signature, entries)
    bases = tuple(sorted(factor for factor, _ in checked))
    if not bases:
        return T.number(1)
    if len(bases) == 1:
        return bases[0]
    times = signature.head_term(StructuralHead.TIMES)
    return T.app(times, *bases)


__all__ = [
    "FactorEntry",
    "FactorizationCertificate",
    "FactorizationClaim",
    "FactorizationVocabulary",
    "HenselIrreducibilityWitness",
    "certificate_matches_claim",
    "factorization_factor_set",
    "factorization_product_term",
    "factorization_radical_term",
    "has_factorization",
    "parse_factor_entries",
    "parse_factorization",
    "rational_literal",
]
