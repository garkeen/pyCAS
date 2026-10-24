"""Parameter specialization, localizations and coverage claims.

A parameter-family computation produces a candidate that is valid only where
the localizations and branch choices it made remain justified. That data is a
`GenericResult` (§8.4): the result, the region on which it holds, the cases the
computation excluded, the specification it satisfies, and the coverage it
claims.

`specialize` maps one exact parameter point. It is not a field homomorphism
from a rational-function field to its base field: a point specialization is
defined only when every parameter has an exact value, the point lies in the
validity region, and no excluded case applies. An unknown condition is not
treated as valid; the caller must recompute in the specialized setting instead.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from enum import StrEnum
from fractions import Fraction
from types import MappingProxyType
from typing import TypeAlias

from cas.foundation.ids import SymbolId
from cas.language.problems import ParameterMode
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics.request import AlgebraRequest
from cas.syntax import binding as B
from cas.syntax import term as T


class CoverageClaim(StrEnum):
    """What a generic answer is allowed to claim about parameter values."""

    SPECIFIED = "specified"
    GENERIC = "generic"
    PARTIAL = "partial"
    ALL_VALUES = "all_values"


@dataclass(frozen=True, slots=True)
class GenericResult:
    """One parameter-family answer with its validity and coverage data."""

    result: T.Term
    valid_on: Proposition
    excluded_cases: tuple[Proposition, ...]
    correctness_specification: Proposition
    coverage_claim: CoverageClaim

    def __post_init__(self) -> None:
        object.__setattr__(self, "excluded_cases", tuple(self.excluded_cases))
        for condition in (
            self.valid_on,
            self.correctness_specification,
            *self.excluded_cases,
        ):
            if not isinstance(condition, Proposition):
                raise TypeError("a generic result carries propositions")
        if self.coverage_claim is CoverageClaim.ALL_VALUES:
            if self.excluded_cases or self.valid_on.term != T.TRUE:
                raise ValueError(
                    "an all-values claim needs unconditional validity"
                )

    @property
    def is_unconditional(self) -> bool:
        return self.valid_on.term == T.TRUE and not self.excluded_cases

    @classmethod
    def assemble(
        cls,
        *,
        result: T.Term,
        valid_on: Proposition,
        excluded_cases: tuple[Proposition, ...],
        correctness_specification: Proposition,
        parameter_mode: ParameterMode,
    ) -> GenericResult:
        """Build the record while deriving the claim from the request mode."""
        unconditional = valid_on.term == T.TRUE and not excluded_cases
        if parameter_mode is ParameterMode.SPECIFIED_VALUES:
            claim = CoverageClaim.SPECIFIED
        elif parameter_mode is ParameterMode.GENERIC_PARAMETERS:
            claim = CoverageClaim.GENERIC
        elif unconditional:
            claim = CoverageClaim.ALL_VALUES
        else:
            claim = CoverageClaim.PARTIAL
        return cls(
            result,
            valid_on,
            tuple(excluded_cases),
            correctness_specification,
            claim,
        )


@dataclass(frozen=True, slots=True)
class Specialization:
    """An exact value for every parameter of one request."""

    values: Mapping[SymbolId, Fraction]

    def __post_init__(self) -> None:
        normalized: dict[SymbolId, Fraction] = {}
        for symbol_id, value in self.values.items():
            if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
                raise TypeError("a parameter value must be an exact rational")
            normalized[SymbolId(symbol_id)] = Fraction(value)
        if not normalized:
            raise ValueError("a specialization needs at least one value")
        object.__setattr__(self, "values", MappingProxyType(normalized))


class SpecializationOutcome:
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Applied(SpecializationOutcome):
    """The generic formula is valid at this point and was substituted."""

    result: T.Term
    specialization: Specialization


@dataclass(frozen=True, slots=True)
class OutsideValidity(SpecializationOutcome):
    """The point is outside the region where the generic result is stated."""

    detail: str
    valid_on: Proposition


@dataclass(frozen=True, slots=True)
class NeedsRecomputation(SpecializationOutcome):
    """The generic formula cannot be used here; the problem must be redone."""

    detail: str
    conditions: tuple[Proposition, ...]


@dataclass(frozen=True, slots=True)
class InvalidSpecialization(SpecializationOutcome):
    """The assignment does not match the request's parameters."""

    detail: str


SpecializationOutcomeType: TypeAlias = (
    Applied | OutsideValidity | NeedsRecomputation | InvalidSpecialization
)


def specialize(
    generic: GenericResult,
    request: AlgebraRequest,
    specialization: Specialization,
    signature: LanguageSignature,
) -> SpecializationOutcomeType:
    """Apply one exact point to a generic result, or explain why not."""
    values = specialization.values
    if set(values) != set(request.parameters):
        missing = tuple(sorted(set(request.parameters) - set(values)))
        extra = tuple(sorted(set(values) - set(request.parameters)))
        return InvalidSpecialization(
            "a specialization must assign exactly the request parameters; "
            f"missing={missing!r}, extra={extra!r}"
        )

    mapping = {
        symbol_id: T.number(value) for symbol_id, value in values.items()
    }
    valid = _truth(generic.valid_on, mapping, signature)
    if valid is None:
        return NeedsRecomputation(
            "the validity region cannot be decided at this point",
            (generic.valid_on,),
        )
    if not valid:
        return OutsideValidity(
            "the point lies outside the validity region", generic.valid_on
        )

    unresolved: list[Proposition] = []
    for case in generic.excluded_cases:
        truth = _truth(case, mapping, signature)
        if truth is None:
            unresolved.append(case)
        elif truth:
            return NeedsRecomputation(
                "the point lies in an excluded case; recompute in the "
                "specialized setting",
                (case,),
            )
    if unresolved:
        return NeedsRecomputation(
            "an excluded case cannot be decided at this point", tuple(unresolved)
        )

    return Applied(B.substitute_free(generic.result, mapping), specialization)


def _truth(
    proposition: Proposition,
    mapping: Mapping[SymbolId, T.Term],
    signature: LanguageSignature,
) -> bool | None:
    value = _evaluate(B.substitute_free(proposition.term, mapping), signature)
    return value if isinstance(value, bool) else None


def _evaluate(
    term: T.Term,
    signature: LanguageSignature,
) -> Fraction | bool | None:
    """Exact ground evaluation; None means the fragment cannot decide it."""
    if isinstance(term, T.IntLit):
        return Fraction(term.value)
    if isinstance(term, T.RatLit):
        return term.value
    if isinstance(term, T.BoolLit):
        return term.value
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    head = signature.head_of(term.operator.symbol_id)
    if head is None:
        return None
    if head in (StructuralHead.PLUS, StructuralHead.TIMES):
        return _arithmetic(head, term.arguments, signature)
    if head is StructuralHead.POWER:
        return _power(term.arguments, signature)
    if head in _COMPARISONS:
        return _comparison(head, term.arguments, signature)
    if head in (StructuralHead.AND, StructuralHead.OR):
        return _junction(head, term.arguments, signature)
    if head is StructuralHead.NOT:
        value = _evaluate(term.arguments[0], signature)
        return None if not isinstance(value, bool) else not value
    if head is StructuralHead.IMPLIES:
        left = _evaluate(term.arguments[0], signature)
        right = _evaluate(term.arguments[1], signature)
        return _implies(left, right)
    return None


_COMPARISONS = frozenset(
    {
        StructuralHead.EQ,
        StructuralHead.NE,
        StructuralHead.LT,
        StructuralHead.LE,
        StructuralHead.GT,
        StructuralHead.GE,
    }
)


def _arithmetic(
    head: StructuralHead,
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> Fraction | None:
    values: list[Fraction] = []
    for argument in arguments:
        value = _evaluate(argument, signature)
        if not isinstance(value, Fraction):
            return None
        values.append(value)
    if not values:
        return None
    if head is StructuralHead.PLUS:
        return sum(values, Fraction(0))
    product = Fraction(1)
    for value in values:
        product *= value
    return product


def _power(
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> Fraction | None:
    if len(arguments) != 2:
        return None
    base = _evaluate(arguments[0], signature)
    exponent = arguments[1]
    if not isinstance(base, Fraction) or not isinstance(exponent, T.IntLit):
        return None
    if exponent.value < 0 and base == 0:
        return None
    return base**exponent.value


def _comparison(
    head: StructuralHead,
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> bool | None:
    if len(arguments) != 2:
        return None
    left = _evaluate(arguments[0], signature)
    right = _evaluate(arguments[1], signature)
    if not isinstance(left, Fraction) or not isinstance(right, Fraction):
        return None
    if head is StructuralHead.EQ:
        return left == right
    if head is StructuralHead.NE:
        return left != right
    if head is StructuralHead.LT:
        return left < right
    if head is StructuralHead.LE:
        return left <= right
    if head is StructuralHead.GT:
        return left > right
    return left >= right


def _junction(
    head: StructuralHead,
    arguments: tuple[T.Term, ...],
    signature: LanguageSignature,
) -> bool | None:
    unknown = False
    for argument in arguments:
        value = _evaluate(argument, signature)
        if not isinstance(value, bool):
            unknown = True
            continue
        if head is StructuralHead.AND and not value:
            return False
        if head is StructuralHead.OR and value:
            return True
    if unknown:
        return None
    return head is StructuralHead.AND


def _implies(left: Fraction | bool | None, right: Fraction | bool | None) -> bool | None:
    if left is False or right is True:
        return True
    if left is True and right is False:
        return False
    return None


__all__ = [
    "Applied",
    "CoverageClaim",
    "GenericResult",
    "InvalidSpecialization",
    "NeedsRecomputation",
    "OutsideValidity",
    "Specialization",
    "SpecializationOutcome",
    "SpecializationOutcomeType",
    "specialize",
]
