"""Parameter specialization, localizations and coverage claims.

A parameter-family computation produces a candidate that is valid only where
the localizations and branch choices it made remain justified. That data is a
`GenericResult` (§8.4): the result, the region on which it holds, the cases the
computation excluded, the specification it satisfies, and the coverage it
claims.  `valid_on` and `excluded_cases` are `RegionSpec` payloads (§10.3), not
bare propositions.

`specialize` maps one exact parameter point. It is not a field homomorphism
from a rational-function field to its base field: a point specialization is
defined only when every parameter has an exact value, the point lies in the
validity region, and no excluded case applies.  A validity or exclusion
condition is evaluated only where its definedness premises hold.  A false
premise means the condition is undefined at the point: the point is outside a
validity region, and an excluded case does not apply.  An undecidable premise
forces recomputation.  An unknown condition is not treated as valid; the
caller must recompute in the specialized setting instead.
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
from cas.semantics.regions import RegionSpec
from cas.semantics.request import AlgebraRequest
from cas.syntax import binding as B
from cas.syntax import term as T


class CoverageClaim(StrEnum):
    """What a generic answer is allowed to claim about parameter values."""

    SPECIFIED = "specified"
    GENERIC = "generic"
    PARTIAL = "partial"
    ALL_VALUES = "all_values"


def is_unconditional(
    valid_on: RegionSpec,
    excluded_cases: tuple[RegionSpec, ...],
) -> bool:
    """Whether the answer is stated without any validity restriction.

    A data record has no prover, so only the canonical `true` region is
    accepted. A logically equivalent but structurally different region is
    conservatively not promoted to an all-values claim.
    """
    return valid_on.condition.term == T.TRUE and not excluded_cases


def validate_coverage_claim(
    coverage: CoverageClaim | None,
    valid_on: RegionSpec | None,
    excluded_cases: tuple[RegionSpec, ...],
) -> None:
    """The single admission rule for coverage data."""
    if coverage is not None and not isinstance(coverage, CoverageClaim):
        raise TypeError("coverage must be a CoverageClaim")
    if valid_on is not None and not isinstance(valid_on, RegionSpec):
        raise TypeError("a validity region must be a RegionSpec")
    if any(not isinstance(case, RegionSpec) for case in excluded_cases):
        raise TypeError("excluded cases must be RegionSpec values")
    if coverage is None:
        if valid_on is not None or excluded_cases:
            raise ValueError(
                "validity data requires a coverage claim"
            )
        return
    if valid_on is None:
        raise ValueError(
            "a coverage claim needs the region on which it is claimed"
        )
    if coverage is CoverageClaim.ALL_VALUES and not is_unconditional(
        valid_on, excluded_cases
    ):
        raise ValueError(
            "an all-values claim needs unconditional validity"
        )


@dataclass(frozen=True, slots=True)
class GenericResult:
    """One parameter-family answer with its validity and coverage data.

    `valid_on` and `excluded_cases` are `RegionSpec` payloads: the same
    `Region` description of §10.3 that §8.4 requires, not bare propositions.
    `correctness_specification` remains a proposition because it states the
    relation the result must satisfy, not a region on which it is claimed.
    """

    result: T.Term
    valid_on: RegionSpec
    excluded_cases: tuple[RegionSpec, ...]
    correctness_specification: Proposition
    coverage_claim: CoverageClaim

    def __post_init__(self) -> None:
        if not isinstance(self.result, T.Term):
            raise TypeError("a generic result must be a term")
        object.__setattr__(self, "excluded_cases", tuple(self.excluded_cases))
        if not isinstance(self.correctness_specification, Proposition):
            raise TypeError(
                "a generic result needs a correctness proposition"
            )
        if not isinstance(self.coverage_claim, CoverageClaim):
            raise TypeError("a generic result needs a coverage claim")
        validate_coverage_claim(
            self.coverage_claim, self.valid_on, self.excluded_cases
        )

    @property
    def is_unconditional(self) -> bool:
        return is_unconditional(self.valid_on, self.excluded_cases)

    @classmethod
    def assemble(
        cls,
        *,
        result: T.Term,
        valid_on: RegionSpec,
        excluded_cases: tuple[RegionSpec, ...],
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
    valid_on: RegionSpec,
    excluded_cases: tuple[RegionSpec, ...],
) -> CoverageClaim:
    """The strongest claim justified by the request mode and validity data."""
    if parameter_mode is ParameterMode.SPECIFIED_VALUES:
        return CoverageClaim.SPECIFIED
    if parameter_mode is ParameterMode.GENERIC_PARAMETERS:
        return CoverageClaim.GENERIC
    if is_unconditional(valid_on, excluded_cases):
        return CoverageClaim.ALL_VALUES
    return CoverageClaim.PARTIAL


def exact_values(
    values: Mapping[SymbolId, Fraction],
) -> Mapping[SymbolId, Fraction]:
    """Normalize an exact rational assignment, rejecting non-rational values."""
    normalized: dict[SymbolId, Fraction] = {}
    for symbol_id, value in values.items():
        if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
            raise TypeError("an exact rational value is required")
        normalized[SymbolId(symbol_id)] = Fraction(value)
    return MappingProxyType(normalized)


@dataclass(frozen=True, slots=True)
class Specialization:
    """An exact value for every parameter of one request."""

    values: Mapping[SymbolId, Fraction]

    def __post_init__(self) -> None:
        normalized = exact_values(self.values)
        if not normalized:
            raise ValueError("a specialization needs at least one value")
        object.__setattr__(self, "values", normalized)


@dataclass(frozen=True, slots=True)
class Applied:
    """The generic formula is valid at this point and was substituted."""

    result: T.Term
    specialization: Specialization


@dataclass(frozen=True, slots=True)
class OutsideValidity:
    """The point is outside the region where the generic result is stated."""

    detail: str
    valid_on: RegionSpec

    def __post_init__(self) -> None:
        if not isinstance(self.valid_on, RegionSpec):
            raise TypeError("an outside-validity outcome needs a RegionSpec")


@dataclass(frozen=True, slots=True)
class NeedsRecomputation:
    """The generic formula cannot be used here; the problem must be redone."""

    detail: str
    conditions: tuple[RegionSpec, ...]

    def __post_init__(self) -> None:
        conditions = tuple(self.conditions)
        if any(not isinstance(case, RegionSpec) for case in conditions):
            raise TypeError(
                "recomputation conditions must be RegionSpec values"
            )
        object.__setattr__(self, "conditions", conditions)


@dataclass(frozen=True, slots=True)
class InvalidSpecialization:
    """The assignment does not match the request's parameters."""

    detail: str


SpecializationOutcome: TypeAlias = (
    Applied | OutsideValidity | NeedsRecomputation | InvalidSpecialization
)


def specialize(
    generic: GenericResult,
    request: AlgebraRequest,
    specialization: Specialization,
    signature: LanguageSignature,
) -> SpecializationOutcome:
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
    valid = _truth(generic.valid_on.condition, mapping, signature)
    if valid is None:
        return NeedsRecomputation(
            "the validity region cannot be decided at this point",
            (generic.valid_on,),
        )
    if not valid:
        return OutsideValidity(
            "the point lies outside the validity region", generic.valid_on
        )

    unresolved: list[RegionSpec] = []
    for case in generic.excluded_cases:
        truth = _truth(case.condition, mapping, signature)
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
    """Truth of `proposition` at the point, respecting its definedness.

    A proposition is only evaluated where its definedness premises hold.  The
    premises are evaluated first, recursively, because a premise can itself be
    a partial expression.  A false premise means the proposition is undefined
    at the point, so it is reported as `False`: the point is outside a validity
    region and an excluded case does not apply.  An undecidable premise returns
    `None`, which the caller must treat as "cannot decide" rather than valid.
    The main condition is evaluated only after every premise is proved true.
    """
    premises = _premises_truth(proposition, mapping, signature)
    if premises is not True:
        return premises
    return condition_truth(
        B.substitute_free(proposition.term, mapping), signature
    )


def _premises_truth(
    proposition: Proposition,
    mapping: Mapping[SymbolId, T.Term],
    signature: LanguageSignature,
) -> bool | None:
    """Whether every definedness premise of `proposition` holds at the point."""
    undecided = False
    for premise in proposition.definedness:
        truth = _truth(premise, mapping, signature)
        if truth is False:
            return False
        if truth is None:
            undecided = True
    return None if undecided else True


__all__ = [
    "Applied",
    "CoverageClaim",
    "GenericResult",
    "InvalidSpecialization",
    "NeedsRecomputation",
    "OutsideValidity",
    "Specialization",
    "SpecializationOutcome",
    "coverage_claim",
    "exact_values",
    "is_unconditional",
    "specialize",
    "validate_coverage_claim",
]
