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
from cas.language.signatures import LanguageSignature
from cas.semantics.conditions import condition_truth
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
        return cls(
            result,
            valid_on,
            tuple(excluded_cases),
            correctness_specification,
            coverage_claim(parameter_mode, valid_on, excluded_cases),
        )


def coverage_claim(
    parameter_mode: ParameterMode,
    valid_on: Proposition,
    excluded_cases: tuple[Proposition, ...],
) -> CoverageClaim:
    """The strongest claim justified by the request mode and validity data."""
    unconditional = valid_on.term == T.TRUE and not excluded_cases
    if parameter_mode is ParameterMode.SPECIFIED_VALUES:
        return CoverageClaim.SPECIFIED
    if parameter_mode is ParameterMode.GENERIC_PARAMETERS:
        return CoverageClaim.GENERIC
    if unconditional:
        return CoverageClaim.ALL_VALUES
    return CoverageClaim.PARTIAL


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
    return condition_truth(
        B.substitute_free(proposition.term, mapping), signature
    )


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
    "coverage_claim",
    "specialize",
]
