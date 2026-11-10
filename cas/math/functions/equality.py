"""The `EqualOn` and `SamePartialFunction` specifications.

Both predicates are data: the symbols are issued by assembly and the checker
interprets their applications.  A certificate carries the two explicit
`FunctionValue` objects and the representation indices used in the claim, so
the checker never has to guess which function a bare representation term
belongs to.

`EqualOn(U, f, g)` requires both functions to be defined and equal on `U`.
`SamePartialFunction(f, g)` additionally requires the complete intrinsic
domains and representation sets to agree.  The checker proves only the exact
fragments it can decide; everything else is `Unverified`.

An extension certificate may also carry a `CoversCertificate` proving that the
new function value's intrinsic domain is covered by its representation
regions.  That claim is independent of the `EqualOn` agreement on the old
domain and is re-verified by the checker.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.functions import FunctionValue
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature, OperatorSignature
from cas.semantics.regions import (
    CoversCertificate,
    RegionSpec,
    certify_covers,
    coordinate_symbols,
)
from cas.syntax import term as T


class FunctionEqualityKind(StrEnum):
    """Which partial-function relation a specification states."""

    EQUAL_ON = "EqualOn"
    SAME_PARTIAL_FUNCTION = "SamePartialFunction"


@dataclass(frozen=True, slots=True)
class FunctionEqualityVocabulary:
    """The two predicate symbols one world uses for function relations."""

    equal_on_symbol: SymbolId
    equal_on_name: str
    same_symbol: SymbolId
    same_name: str

    def __post_init__(self) -> None:
        if not self.equal_on_name or not self.same_name:
            raise ValueError("a function-equality predicate needs a name")
        if self.equal_on_symbol == self.same_symbol:
            raise ValueError("the two function-equality predicates must differ")

    @property
    def equal_on_signature(self) -> OperatorSignature:
        """`(region, left, right) -> proposition`."""
        return OperatorSignature(
            (S.PROPOSITION, S.REAL, S.REAL),
            S.PROPOSITION,
        )

    @property
    def same_signature(self) -> OperatorSignature:
        """`(left, right) -> proposition`."""
        return OperatorSignature((S.REAL, S.REAL), S.PROPOSITION)


@dataclass(frozen=True, slots=True)
class FunctionEqualityClaim:
    """The parts of one function-equality application."""

    kind: FunctionEqualityKind
    region: T.Term | None
    left: T.Term
    right: T.Term

    def __post_init__(self) -> None:
        if not isinstance(self.kind, FunctionEqualityKind):
            raise TypeError("a function-equality claim needs a kind")
        if self.kind is FunctionEqualityKind.EQUAL_ON:
            if self.region is None:
                raise ValueError("EqualOn needs a region")
        elif self.region is not None:
            raise ValueError("SamePartialFunction has no region argument")
        if not isinstance(self.left, T.Term) or not isinstance(
            self.right, T.Term
        ):
            raise TypeError("a function-equality claim needs two terms")


@dataclass(frozen=True, slots=True)
class FunctionEqualityCertificate:
    """The exact function values and representations behind one claim.

    An extension certificate may additionally carry `coverage`: the proof that
    the right (new) function value's intrinsic domain is covered by its
    representation regions.  The `EqualOn` specification itself only proves
    agreement on the old domain; the coverage claim is a separate
    representational claim and the checker re-verifies it.  Ordinary
    `EqualOn`/`SamePartialFunction` certificates leave `coverage` empty.
    """

    region: T.Term | None
    left: FunctionValue
    right: FunctionValue
    left_index: int
    right_index: int
    coverage: CoversCertificate | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.left, FunctionValue):
            raise TypeError("a function-equality certificate needs a left value")
        if not isinstance(self.right, FunctionValue):
            raise TypeError(
                "a function-equality certificate needs a right value"
            )
        if self.left_index < 0 or self.left_index >= len(
            self.left.representations
        ):
            raise ValueError("the left representation index is out of range")
        if self.right_index < 0 or self.right_index >= len(
            self.right.representations
        ):
            raise ValueError("the right representation index is out of range")
        if self.region is not None and not isinstance(self.region, T.Term):
            raise TypeError("a certificate region must be a term")
        if self.coverage is not None and not isinstance(
            self.coverage, CoversCertificate
        ):
            raise TypeError(
                "a function-equality coverage must be a CoversCertificate"
            )

    @property
    def left_representation(self) -> T.Term:
        return self.left.representations[self.left_index].term

    @property
    def right_representation(self) -> T.Term:
        return self.right.representations[self.right_index].term


def function_region(
    value: FunctionValue,
    proposition: Proposition,
) -> RegionSpec:
    """The region of one function domain proposition, with fixed coordinates.

    The coordinate tuple is the sorted union of every function parameter
    symbol and every free variable of the proposition.  The operation and the
    checker call this helper, so they build the identical region rather than
    two coordinate conventions.

    Binding sorts are recorded only for coordinates that are function
    parameters; those are the only symbols whose declaration sort this value
    owns.  If the condition mentions any free variable that is not a parameter,
    the whole sort tuple is omitted: inventing a sort for the extra coordinate
    would let dense-order coverage reasoning run over an unbound symbol.  An
    omitted tuple makes the region non-dense, so `certify_covers` refuses it.
    """
    if not isinstance(value, FunctionValue):
        raise TypeError("a function region needs a FunctionValue")
    if not isinstance(proposition, Proposition):
        raise TypeError("a function region needs a proposition")
    parameters = {
        parameter.symbol: parameter.sort
        for parameter in value.parameters
    }
    condition_symbols = coordinate_symbols(proposition.term)
    coordinates = tuple(
        sorted(set(parameters) | set(condition_symbols))
    )
    sorts: tuple[tuple[SymbolId, S.Sort], ...]
    if condition_symbols <= set(parameters):
        sorts = tuple(
            sorted(parameters.items(), key=lambda item: item[0])
        )
    else:
        sorts = ()
    return RegionSpec(coordinates, proposition, sorts)


def function_coverage_regions(
    value: FunctionValue,
) -> tuple[RegionSpec, tuple[RegionSpec, ...]]:
    """The intrinsic domain and every representation region of `value`.

    The pieces stay in representation order, so the certificate identifies the
    exact function value it covers.  The intrinsic domain is the covered
    region; a representation may be valid on a proper subregion.
    """
    if not isinstance(value, FunctionValue):
        raise TypeError("function coverage needs a FunctionValue")
    domain = function_region(value, value.intrinsic_domain)
    pieces = tuple(
        function_region(value, representation.valid_on)
        for representation in value.representations
    )
    return domain, pieces


def function_coverage_certificate(
    value: FunctionValue,
    signature: LanguageSignature,
) -> CoversCertificate | None:
    """Certify that `value`'s representations cover its intrinsic domain.

    This uses the same restricted `certify_covers` fragment as every other
    region claim.  `None` means the fragment cannot prove the cover; it is not
    a claim that the cover is false.
    """
    if not isinstance(value, FunctionValue):
        raise TypeError("function coverage needs a FunctionValue")
    if not isinstance(signature, LanguageSignature):
        raise TypeError(
            "function coverage is read in a LanguageSignature"
        )
    domain, pieces = function_coverage_regions(value)
    return certify_covers(domain, pieces, signature)


def coverage_matches_value(
    certificate: CoversCertificate,
    value: FunctionValue,
) -> bool:
    """Whether `certificate` is exactly the coverage claim for `value`.

    The checker calls this with the certificate's right function value.  A
    certificate for a different domain, a different representation order or a
    different validity region does not match, even when its `method` label
    looks plausible.
    """
    if not isinstance(certificate, CoversCertificate):
        raise TypeError("coverage matching needs a CoversCertificate")
    if not isinstance(value, FunctionValue):
        raise TypeError("coverage matching needs a FunctionValue")
    domain, pieces = function_coverage_regions(value)
    return certificate.region == domain and certificate.pieces == pieces


def equal_on(
    vocabulary: FunctionEqualityVocabulary,
    region: T.Term,
    left: T.Term,
    right: T.Term,
) -> T.Term:
    """Build an `EqualOn` specification term."""
    return T.app(
        T.symbol(vocabulary.equal_on_symbol, vocabulary.equal_on_name),
        region,
        left,
        right,
    )


def same_partial_function(
    vocabulary: FunctionEqualityVocabulary,
    left: T.Term,
    right: T.Term,
) -> T.Term:
    """Build a `SamePartialFunction` specification term."""
    return T.app(
        T.symbol(vocabulary.same_symbol, vocabulary.same_name),
        left,
        right,
    )


def certificate_matches_claim(
    certificate: FunctionEqualityCertificate,
    claim: FunctionEqualityClaim,
) -> bool:
    """Whether the certificate names exactly the claimed instance."""
    if claim.kind is FunctionEqualityKind.EQUAL_ON:
        if certificate.region != claim.region:
            return False
    elif certificate.region is not None:
        return False
    return (
        certificate.left_representation == claim.left
        and certificate.right_representation == claim.right
    )


def parse_function_equality(
    vocabulary: FunctionEqualityVocabulary,
    term: T.Term,
) -> FunctionEqualityClaim | None:
    """Recognize one of this vocabulary's applications, or return None."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    symbol = term.operator.symbol_id
    if symbol == vocabulary.equal_on_symbol:
        if len(term.arguments) != 3:
            return None
        region, left, right = term.arguments
        return FunctionEqualityClaim(
            FunctionEqualityKind.EQUAL_ON, region, left, right
        )
    if symbol == vocabulary.same_symbol:
        if len(term.arguments) != 2:
            return None
        left, right = term.arguments
        return FunctionEqualityClaim(
            FunctionEqualityKind.SAME_PARTIAL_FUNCTION, None, left, right
        )
    return None


__all__ = [
    "FunctionEqualityCertificate",
    "FunctionEqualityClaim",
    "FunctionEqualityKind",
    "FunctionEqualityVocabulary",
    "certificate_matches_claim",
    "coverage_matches_value",
    "equal_on",
    "function_coverage_certificate",
    "function_coverage_regions",
    "function_region",
    "parse_function_equality",
    "same_partial_function",
]
