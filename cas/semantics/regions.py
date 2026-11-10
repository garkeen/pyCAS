"""Region specifications and the certificates that establish their properties.

A region is a proposition formula together with the ordered coordinates its
free variables are read in.  `RegionSpec` is the description; a
`RegionCertificate` records a proved nonemptiness, inclusion or cover.  The
certificate's `method` is only a human-readable label: verification always
re-checks the mathematical claim in the restricted condition logic, so a
forged or mismatched certificate is rejected even when its label looks valid.

The restricted fragment is the one implemented in `cas.semantics.conditions`:
ground truth, conjunctions of one-atom linear comparisons and interval
inclusion.  Opaque, nonlinear, multi-atom, disjunctive and non-normalizable
negated conditions are undecided, never treated as true or nonempty.  That
fragment reasons about intervals in a dense linear order, so a certificate is
issued or accepted only when every participating region records rational or
real binding sorts.  An integer, complex, unknown or missing sort is not dense:
the same interval may be empty over the integers (`0 < y < 1`), and a
certificate over it would be unsound.  This is the region slice of
`cas_v5_arch.md` §10.3 and the `Covers` specification of §12.2; it does not
claim a general semialgebraic or discrete region algebra.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.meaning import MeaningKey
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics.conditions import (
    condition_satisfiable,
    implies,
    is_subregion,
    premises_proved,
)
from cas.syntax import term as T
from cas.syntax.binding import variable_symbols


def coordinate_symbols(term: T.Term) -> frozenset[SymbolId]:
    """The free variables of `term`, excluding operator-position symbols.

    This is the coordinate vocabulary of a region condition.  Language heads
    and declared function symbols occur in operator position and are not
    coordinates; the remaining free symbols are the variables a region is read
    over.  A scalar variable cannot be an operator, so no real coordinate is
    lost.  The traversal lives in `syntax.binding` so the language-level problem
    region check and the region algebra share one definition.
    """
    return variable_symbols(term)


def region_from_proposition(proposition: Proposition) -> RegionSpec:
    """The region described by an existing proposition-valued payload.

    Proposal fields such as `MathematicalProposal.valid_on` are propositions.
    This bridge turns one into the `RegionSpec` used by `GenericResult`
    (§8.4/§10.3) without introducing a second region type.  The coordinates are
    the sorted free variables of the condition, so the same proposition always
    yields the same deterministic coordinate tuple.  The proposition payload
    carries no binding sorts, so the resulting region has no `sorts` and is not
    admissible for dense-order certificate reasoning; callers that own the
    symbol declarations must supply a sorted `RegionSpec` explicitly.
    """
    if not isinstance(proposition, Proposition):
        raise TypeError("a region needs a proposition condition")
    coordinates = tuple(sorted(coordinate_symbols(proposition.term)))
    return RegionSpec(coordinates, proposition)


@dataclass(frozen=True, slots=True)
class RegionSpec:
    """A condition formula with the ordered coordinates it is read in.

    The coordinate order is part of the region's coordinate system and is kept
    exactly as given.  Every free variable of `condition` must be one of the
    coordinates; extra coordinates are allowed because a region may be stated
    over a larger coordinate space than the variables it mentions.

    `sorts` is the binding part of the region description.  When present it
    binds every coordinate to its declared sort, in canonical `SymbolId` order.
    A region without complete binding sorts is not admissible for the
    dense-order certificate fragment: the interval reasoning in
    `cas.semantics.conditions` assumes rational or real coordinates, so an
    integer, complex or unknown sort must not inherit that reasoning.  An empty
    coordinate set is vacuously dense because no ordered variable is involved.
    """

    coordinates: tuple[SymbolId, ...]
    condition: Proposition
    sorts: tuple[tuple[SymbolId, S.Sort], ...] = ()

    def __post_init__(self) -> None:
        coordinates = tuple(self.coordinates)
        if any(
            isinstance(item, bool) or not isinstance(item, int)
            for item in coordinates
        ):
            raise TypeError("region coordinates must be SymbolId integers")
        if len(set(coordinates)) != len(coordinates):
            raise ValueError("region coordinates must be distinct")
        if not isinstance(self.condition, Proposition):
            raise TypeError("a region needs a proposition condition")
        unknown = coordinate_symbols(self.condition.term) - set(coordinates)
        if unknown:
            rendered = ", ".join(str(item) for item in sorted(unknown))
            raise ValueError(
                "the region condition has free variables outside its "
                f"coordinates: {rendered}"
            )
        sorts = tuple(self.sorts)
        for entry in sorts:
            if not isinstance(entry, tuple) or len(entry) != 2:
                raise TypeError(
                    "region sorts must be (SymbolId, Sort) pairs"
                )
            symbol_id, sort = entry
            if isinstance(symbol_id, bool) or not isinstance(
                symbol_id, int
            ):
                raise TypeError(
                    "region sort symbols must be SymbolId integers"
                )
            if not isinstance(sort, S.Sort):
                raise TypeError("region sort entries must carry a Sort")
        sort_symbols = tuple(symbol_id for symbol_id, _ in sorts)
        if len(set(sort_symbols)) != len(sort_symbols):
            raise ValueError("region sort symbols must be distinct")
        if sorts and set(sort_symbols) != set(coordinates):
            raise ValueError(
                "region sorts must cover exactly the region coordinates"
            )
        object.__setattr__(self, "coordinates", coordinates)
        object.__setattr__(
            self,
            "sorts",
            tuple(sorted(sorts, key=lambda item: item[0])),
        )

    @property
    def meaning(self) -> MeaningKey:
        """The meaning environment the condition was read in."""
        return self.condition.meaning

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        """The binding sort of one coordinate, or None when it is unrecorded."""
        if isinstance(symbol_id, bool) or not isinstance(symbol_id, int):
            raise TypeError("a region sort query needs a SymbolId")
        for identifier, sort in self.sorts:
            if identifier == symbol_id:
                return sort
        return None

    @property
    def is_dense(self) -> bool:
        """Whether every coordinate has a rational or real binding sort.

        The certificate fragment in `cas.semantics.conditions` uses interval
        reasoning over a dense linear order.  Only rational and real
        coordinates justify that reading; an empty coordinate set is vacuously
        dense because no ordered variable is involved.  Missing, integer,
        complex and unknown sorts are not dense.
        """
        if not self.coordinates:
            return True
        if not self.sorts:
            return False
        return all(
            sort in (S.RATIONAL, S.REAL) for _, sort in self.sorts
        )


def _require_method(method: str) -> None:
    if not isinstance(method, str):
        raise TypeError("a region certificate needs a method string")
    if not method:
        raise ValueError("a region certificate method cannot be empty")


@dataclass(frozen=True, slots=True)
class NonemptyCertificate:
    """A proved nonempty region."""

    region: RegionSpec
    method: str

    def __post_init__(self) -> None:
        if not isinstance(self.region, RegionSpec):
            raise TypeError("a nonempty certificate needs a region")
        _require_method(self.method)


@dataclass(frozen=True, slots=True)
class SubregionCertificate:
    """A proved inclusion `subregion` inside `region`."""

    subregion: RegionSpec
    region: RegionSpec
    method: str

    def __post_init__(self) -> None:
        if not isinstance(self.subregion, RegionSpec) or not isinstance(
            self.region, RegionSpec
        ):
            raise TypeError("a subregion certificate needs two regions")
        _require_method(self.method)
        if self.subregion.meaning != self.region.meaning:
            raise ValueError(
                "a subregion certificate needs one meaning environment"
            )


@dataclass(frozen=True, slots=True)
class CoversCertificate:
    """A proved cover of `region` by `pieces`."""

    region: RegionSpec
    pieces: tuple[RegionSpec, ...]
    method: str

    def __post_init__(self) -> None:
        if not isinstance(self.region, RegionSpec):
            raise TypeError("a covers certificate needs a region")
        pieces = tuple(self.pieces)
        if any(not isinstance(piece, RegionSpec) for piece in pieces):
            raise TypeError("a covers certificate needs region pieces")
        if not pieces:
            raise ValueError("a covers certificate needs at least one piece")
        _require_method(self.method)
        if any(piece.meaning != self.region.meaning for piece in pieces):
            raise ValueError(
                "a covers certificate needs one meaning environment"
            )
        object.__setattr__(self, "pieces", pieces)


RegionCertificate: TypeAlias = (
    NonemptyCertificate | SubregionCertificate | CoversCertificate
)


def _require_signature(signature: LanguageSignature) -> None:
    if not isinstance(signature, LanguageSignature):
        raise TypeError(
            "region certificates are read in a LanguageSignature"
        )


def premises_proved_from(
    assumption: Proposition,
    owner: Proposition,
    signature: LanguageSignature,
) -> bool | None:
    """Whether every definedness premise of `owner` follows from `assumption`.

    Definedness premises are conditions under which `owner` is defined, not
    assumptions that make it true.  A region certificate may use a partial
    condition only when the region's own condition proves its premises;
    otherwise the condition does not describe a total region.  The restricted
    implication fragment is conservative: `None` is never treated as proved.
    """
    if not isinstance(assumption, Proposition) or not isinstance(
        owner, Proposition
    ):
        raise TypeError(
            "definedness premises are compared between propositions"
        )
    _require_signature(signature)
    return premises_proved(
        assumption.term,
        tuple(premise.term for premise in owner.definedness),
        signature,
    )


def proved_subregion(
    subregion: Proposition,
    region: Proposition,
    signature: LanguageSignature,
    *,
    same_meaning: bool = True,
) -> bool | None:
    """Whether `subregion` is a total region provably inside `region`.

    The subregion's own definedness premises and the region's definedness
    premises must both follow from the subregion condition.  A condition with
    an open premise does not describe a region on which the proposition is
    defined, so it is never admitted as a certificate participant.  `True`
    means every premise and the term-level inclusion are proved; `False` and
    `None` are never read as proved.

    `same_meaning` is the default certificate rule: both propositions must be
    read in the same meaning environment.  A caller that has independently
    established both propositions are readable in one world may pass `False`
    and still get the same premise and inclusion checks.  That is used by the
    function-equality checker, whose claim region is read in the request frame
    while a function domain may be read in a visible ancestor frame; the shared
    symbol identities of one world carry the mathematical meaning.
    """
    if not isinstance(subregion, Proposition) or not isinstance(
        region, Proposition
    ):
        raise TypeError("a subregion claim compares propositions")
    _require_signature(signature)
    if same_meaning and subregion.meaning != region.meaning:
        return None
    own = premises_proved_from(subregion, subregion, signature)
    if own is not True:
        return own
    goal = premises_proved_from(subregion, region, signature)
    if goal is not True:
        return goal
    return is_subregion(subregion.term, region.term, signature)


def _disjunction(
    pieces: tuple[RegionSpec, ...],
    signature: LanguageSignature,
) -> T.Term | None:
    """The disjunction of the piece conditions, or None without an Or head."""
    if not pieces:
        return None
    if len(pieces) == 1:
        return pieces[0].condition.term
    or_symbol = signature.symbol_of(StructuralHead.OR)
    if or_symbol is None:
        return None
    return T.app(
        T.symbol(or_symbol, StructuralHead.OR.value),
        *(piece.condition.term for piece in pieces),
    )


def certify_nonempty(
    region: RegionSpec,
    signature: LanguageSignature,
) -> NonemptyCertificate | None:
    """Certify `region` nonempty, or return None when the fragment cannot.

    A condition with an unproved definedness premise does not describe a total
    region; the certificate is refused rather than ignoring the premise.  The
    interval fragment assumes a dense linear order, so a region without
    rational or real binding sorts is refused before satisfiability is read.
    """
    if not isinstance(region, RegionSpec):
        raise TypeError("nonemptiness needs a region")
    _require_signature(signature)
    if not region.is_dense:
        return None
    if premises_proved_from(
        region.condition, region.condition, signature
    ) is not True:
        return None
    if condition_satisfiable(region.condition.term, signature) is not True:
        return None
    return NonemptyCertificate(
        region, "restricted condition satisfiability"
    )


def certify_subregion(
    subregion: RegionSpec,
    region: RegionSpec,
    signature: LanguageSignature,
) -> SubregionCertificate | None:
    """Certify `subregion` inside `region`, or return None when unproved.

    Both the subregion's own definedness premises and the region's premises
    must be proved from the subregion condition; otherwise the certificate is
    refused.  The inclusion uses the same dense-order interval fragment, so a
    non-dense participant is refused.
    """
    if not isinstance(subregion, RegionSpec) or not isinstance(
        region, RegionSpec
    ):
        raise TypeError("a subregion claim needs two regions")
    _require_signature(signature)
    if not subregion.is_dense or not region.is_dense:
        return None
    if subregion.meaning != region.meaning:
        return None
    if proved_subregion(
        subregion.condition, region.condition, signature
    ) is not True:
        return None
    return SubregionCertificate(subregion, region, "restricted implication")


def certify_covers(
    region: RegionSpec,
    pieces: tuple[RegionSpec, ...],
    signature: LanguageSignature,
) -> CoversCertificate | None:
    """Certify that `pieces` cover `region`, or return None when unproved.

    The covered region's own premises must follow from its condition, and every
    piece's premises must follow from the region condition.  This strict-Or
    reading keeps the piece disjunction defined throughout the covered region;
    a piece with an open premise is not admitted.  The disjunction implication
    uses the dense-order fragment, so every participant must be dense.
    """
    if not isinstance(region, RegionSpec):
        raise TypeError("a cover needs a region")
    pieces = tuple(pieces)
    if any(not isinstance(piece, RegionSpec) for piece in pieces):
        raise TypeError("a cover needs region pieces")
    _require_signature(signature)
    if not pieces:
        return None
    if not region.is_dense or any(not piece.is_dense for piece in pieces):
        return None
    if any(piece.meaning != region.meaning for piece in pieces):
        return None
    if premises_proved_from(
        region.condition, region.condition, signature
    ) is not True:
        return None
    if any(
        premises_proved_from(
            region.condition, piece.condition, signature
        )
        is not True
        for piece in pieces
    ):
        return None
    disjunction = _disjunction(pieces, signature)
    if disjunction is None:
        return None
    if implies(
        region.condition.term, disjunction, signature
    ) is not True:
        return None
    return CoversCertificate(
        region, pieces, "restricted implication of the disjunction"
    )


def verify_region_certificate(
    certificate: RegionCertificate,
    signature: LanguageSignature,
) -> bool:
    """Re-check a region certificate in `signature`.

    The method label is deliberately ignored.  A certificate whose regions do
    not support its claim is rejected even if it was constructed with a
    plausible label or bypassed its constructor.  The interval fragment is
    sound only for dense coordinates, so a forged certificate over an integer,
    complex or sort-less region is rejected rather than re-checked with the
    dense-order reading.
    """
    _require_signature(signature)
    if isinstance(certificate, NonemptyCertificate):
        if not certificate.region.is_dense:
            return False
        if premises_proved_from(
            certificate.region.condition,
            certificate.region.condition,
            signature,
        ) is not True:
            return False
        return (
            condition_satisfiable(
                certificate.region.condition.term, signature
            )
            is True
        )
    if isinstance(certificate, SubregionCertificate):
        if not certificate.subregion.is_dense or not certificate.region.is_dense:
            return False
        return (
            proved_subregion(
                certificate.subregion.condition,
                certificate.region.condition,
                signature,
            )
            is True
        )
    if isinstance(certificate, CoversCertificate):
        if not certificate.pieces:
            return False
        if not certificate.region.is_dense or any(
            not piece.is_dense for piece in certificate.pieces
        ):
            return False
        if any(
            piece.meaning != certificate.region.meaning
            for piece in certificate.pieces
        ):
            return False
        if premises_proved_from(
            certificate.region.condition,
            certificate.region.condition,
            signature,
        ) is not True:
            return False
        if any(
            premises_proved_from(
                certificate.region.condition,
                piece.condition,
                signature,
            )
            is not True
            for piece in certificate.pieces
        ):
            return False
        disjunction = _disjunction(certificate.pieces, signature)
        if disjunction is None:
            return False
        return (
            implies(
                certificate.region.condition.term,
                disjunction,
                signature,
            )
            is True
        )
    raise TypeError("verification needs a region certificate")


__all__ = [
    "CoversCertificate",
    "NonemptyCertificate",
    "RegionCertificate",
    "RegionSpec",
    "SubregionCertificate",
    "certify_covers",
    "certify_nonempty",
    "certify_subregion",
    "coordinate_symbols",
    "premises_proved_from",
    "proved_subregion",
    "region_from_proposition",
    "verify_region_certificate",
]
