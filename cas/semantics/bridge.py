"""Conversions between syntax terms and parent elements.

``to_view`` and ``render`` are the only conversion entry points.  A typed
source is admitted into an explicit parent under one ``AlgebraRequest``, and a
member is rendered back through the view's symbol bindings.  Both directions
report a closed ``ViewRefused``/``RenderRefused`` with the missing capability
instead of collapsing every reason into the same absence; the former
``None``-returning helpers have been removed.  The univariate polynomial
bridge, the multivariate polynomial bridge and the rational-function bridge
implement the same protocol, but only the last has real holes: its view
carries the denominator-nonzero proposition on which the fraction-field
representation equals the source.

An ``AlgebraView`` pairs the typed source, the target parent, the element and
the symbol bindings that interpret the source's free symbols as a target,
generator or parameter generator.  It also records the source's intrinsic
domain and the region on which the representation equals the source when the
bridge is not total on its fragment.  The two are independent: a source may be
total while the chosen representation is valid only on a proper subregion, so
a ``valid_on`` does not require a ``source_domain``.  It is the value
mathematical operations and checkers consume.  The view also carries a
`ConversionWitness`: the structural facts the conversion establishes, not just
its kind.  The witness records whether the conversion preserves definedness;
only such a witness can support a view's explicit region claim.  Rendering back
to terms uses those bindings and never invents a global name.  The payload and
admission contract follow `cas_v5_arch.md` §7.8, §32.4 and §32.6.

The polynomial bridge is total on its fragment: every accepted source is
defined wherever the polynomial expression is evaluated, so its views leave
``source_domain`` and ``valid_on`` as ``None``.  The rational bridge computes
the product of the source's inverse denominators, so cancelling a factor in
the fraction field does not erase a hole in the source expression.  The
multivariate polynomial bridge binds the ring's generators in declared order
to source symbols with ``Role.GENERATOR``; it refuses a target, a parameter
ring or a generator order that differs from the ring.  The registered
``groebner_basis`` operation and bootstrap assembly consume this generator
mode view.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from enum import StrEnum
from fractions import Fraction
from types import MappingProxyType
from typing import Generic, Protocol, TypeAlias, TypeVar, cast

from cas.algebra.parents import Parent
from cas.algebra.polynomial import Polynomial, PolynomialRing
from cas.algebra.protocols import RationalEmbedding
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.foundation.ids import FrameId, SymbolId, WorldId
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.problems import Role
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.language.typing import FreeSymbol, TypedExpr, TypedExprFailure
from cas.semantics import elaborate
from cas.semantics.definedness import (
    Definedness,
    DefinednessExactness,
    _issue_definedness,
)
from cas.semantics.frames import FrameStore
from cas.semantics.regions import (
    RegionSpec,
    certify_subregion,
    coordinate_symbols,
    premises_proved_from,
    proved_subregion,
)
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.syntax import term as T

E = TypeVar("E")
V = TypeVar("V")

_VIEW_SEAL = object()

_ROLE_ORDER = {
    Role.TARGET: 0,
    Role.GENERATOR: 1,
    Role.PARAMETER: 2,
}


class ConversionKind(StrEnum):
    """The mathematical relation a view's conversion establishes.

    `REPRESENTATION_ISOMORPHISM` is a bijective structure-preserving change of
    representation, so equality transfers in both directions.  `EMBEDDING` is
    injective and structure-preserving, so target equality still implies source
    equality.  A general `HOMOMORPHISM` need not be injective: source equality
    implies target equality, but target equality does not transfer back to the
    source.  The current polynomial and rational bridges issue only
    `REPRESENTATION_ISOMORPHISM`; `typed_view` refuses to read a target
    equality as a source equality through a witness that is not injective or
    does not preserve equality.
    """

    REPRESENTATION_ISOMORPHISM = "representation_isomorphism"
    EMBEDDING = "embedding"
    HOMOMORPHISM = "homomorphism"


@dataclass(frozen=True, slots=True)
class ConversionWitness:
    """The structural properties a view's conversion actually establishes.

    The kind alone is a label; the witness records the facts consumers may
    rely on.  A representation isomorphism and an embedding are injective,
    preserve equality in both directions, preserve nonzero values and preserve
    definedness.  A general homomorphism may fail any of these; without
    injectivity and equality preservation it cannot transfer a target equality
    back to the source.

    ``preserves_definedness`` states whether the conversion preserves the
    source expression's definedness at all.  A conversion that does not
    preserve definedness cannot transfer a source-domain or
    representation-region claim back to the source; the
    `AlgebraView.source_domain`/`valid_on` are the explicit region payload,
    and this flag is the witness's statement that the conversion preserves
    definedness.  A total view carries no such region claim, so a
    homomorphism that does not preserve definedness can still transfer
    equality when it is injective and equality-preserving.
    """

    kind: ConversionKind
    injective: bool
    preserves_equality: bool
    preserves_nonzero: bool
    preserves_definedness: bool

    def __post_init__(self) -> None:
        if not isinstance(self.kind, ConversionKind):
            raise TypeError("a conversion witness needs a ConversionKind")
        for name in (
            "injective",
            "preserves_equality",
            "preserves_nonzero",
            "preserves_definedness",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(
                    f"a conversion witness needs a boolean {name} flag"
                )
        if self.kind is not ConversionKind.HOMOMORPHISM:
            if not (
                self.injective
                and self.preserves_equality
                and self.preserves_nonzero
                and self.preserves_definedness
            ):
                raise ValueError(
                    f"a {self.kind.value} witness must be injective, "
                    "preserve equality, preserve nonzero and preserve "
                    "definedness"
                )

    @classmethod
    def representation_isomorphism(cls) -> ConversionWitness:
        """The witness the polynomial and rational bridges establish."""
        return cls(
            ConversionKind.REPRESENTATION_ISOMORPHISM,
            injective=True,
            preserves_equality=True,
            preserves_nonzero=True,
            preserves_definedness=True,
        )


def _interpretation_witness_refusal(
    interpretation: Interpretation, witness: ConversionWitness
) -> str | None:
    """The detail when an interpretation contradicts its witness kind.

    An ``EMBEDDED`` view claims that the value is the image of the source
    under an injective structure-preserving map.  Only an embedding or a
    representation isomorphism establishes that claim; a general homomorphism
    is not injective, so it cannot witness that the value is *the* embedded
    image rather than one homomorphic image.

    A ``PARAMETER_FAMILY`` view claims that the value is the formal
    parameter-family representation itself.  Only a representation
    isomorphism establishes that claim; an embedding or homomorphism is a
    strictly weaker relation and would let a coarser representation be
    presented as the family.

    A ``FORMAL`` view claims only a value in the parent, so all three kinds
    remain admissible and the witness flags alone govern what may be
    transferred.  This rule is independent of the region/definedness rule in
    `_region_definedness_refusal`; a view must satisfy both.
    """
    if interpretation is Interpretation.EMBEDDED:
        if witness.kind not in (
            ConversionKind.EMBEDDING,
            ConversionKind.REPRESENTATION_ISOMORPHISM,
        ):
            return (
                "an embedded interpretation needs an embedding or "
                "representation-isomorphism witness, not a homomorphism"
            )
        return None
    if interpretation is Interpretation.PARAMETER_FAMILY:
        if witness.kind is not ConversionKind.REPRESENTATION_ISOMORPHISM:
            return (
                "a parameter-family interpretation needs a "
                "representation-isomorphism witness"
            )
        return None
    return None


def _region_binding_refusal(
    source: object,
    source_domain: Proposition | None,
    valid_on: Proposition | None,
    region_bindings: object,
) -> str | None:
    """The detail when the region binding view cannot read the regions.

    A region's coordinates are the free variables of its condition.  The
    source binding view is the default coordinate vocabulary, but a region may
    be read in a descendant frame and mention an extra declared symbol.  The
    view therefore records an explicit `region_bindings` tuple that must cover
    the source's free symbols and every present region's free variables.  The
    tuple is the binding authority for the `RegionSpec` sorts; missing entries
    are refused instead of being guessed from names or syntax.

    An explicit entry may not override the sort of a symbol the source binds.
    The source binding view is the authority for its own free symbols, so a
    region binding with a different sort is refused; otherwise `definedness`
    could build a dense `RegionSpec` over a disguised non-dense source
    coordinate.  Extra child-frame coordinates that the source does not bind
    keep the bridge's declared sort: this rule only protects known source
    symbols and does not infer sorts for the extras.
    """
    if not isinstance(source, TypedExpr):
        return None
    if not isinstance(region_bindings, tuple):
        return "the view region bindings must be a tuple of FreeSymbol values"
    for item in region_bindings:
        if not isinstance(item, FreeSymbol):
            return "the view region bindings must be FreeSymbol values"
    identifiers = tuple(item.symbol_id for item in region_bindings)
    if len(set(identifiers)) != len(identifiers):
        return "the view cannot bind one region coordinate twice"
    source_sorts = {
        item.symbol_id: item.sort for item in source.bindings.symbols
    }
    for item in region_bindings:
        expected = source_sorts.get(item.symbol_id)
        if expected is not None and item.sort != expected:
            return (
                "the view region bindings give symbol "
                f"{item.symbol_id} sort {item.sort!r}, but the source binds "
                f"it as {expected!r}"
            )
    bound = set(identifiers)
    missing_source = {
        item.symbol_id for item in source.bindings.symbols
    } - bound
    if missing_source:
        rendered = ", ".join(
            str(item) for item in sorted(missing_source)
        )
        return (
            "the view region bindings do not cover every source free symbol: "
            f"{rendered}"
        )
    for name, region in (
        ("source domain", source_domain),
        ("validity region", valid_on),
    ):
        if region is None:
            continue
        missing = coordinate_symbols(region.term) - bound
        if missing:
            rendered = ", ".join(str(item) for item in sorted(missing))
            return (
                f"the view region bindings do not cover every {name} "
                f"coordinate: {rendered}"
            )
    return None


def _region_definedness_refusal(
    witness: ConversionWitness,
    source_domain: Proposition | None,
    valid_on: Proposition | None,
) -> str | None:
    """The detail when a view's explicit regions need a preserving witness.

    A source domain or validity region is a claim about the source expression.
    A conversion that does not preserve definedness cannot transfer that claim
    back to the source, so a region-bearing view must record a witness that
    preserves definedness.  A total view (both regions absent) makes no such
    claim and is not covered by this rule.
    """
    if source_domain is None and valid_on is None:
        return None
    if witness.preserves_definedness:
        return None
    return (
        "the conversion witness does not preserve definedness, so the view's "
        "source domain or validity region cannot be transferred back to the "
        "source"
    )


@dataclass(frozen=True, slots=True)
class SymbolBinding:
    """One source symbol interpreted as a target, generator or parameter."""

    symbol: SymbolId
    role: Role
    index: int

    def __post_init__(self) -> None:
        if isinstance(self.symbol, bool) or not isinstance(self.symbol, int):
            raise TypeError("a symbol binding needs a SymbolId")
        if not isinstance(self.role, Role):
            raise TypeError("a symbol binding needs a Role")
        if isinstance(self.index, bool) or not isinstance(self.index, int):
            raise TypeError("a symbol binding needs an integer index")
        if self.index < 0:
            raise ValueError("a symbol binding index must be nonnegative")


_VIEW_FIELDS = frozenset(
    {
        "source",
        "parent",
        "value",
        "symbols",
        "interpretation",
        "witness",
        "signature",
        "source_domain",
        "valid_on",
        "region_bindings",
    }
)


def _require_view_seal(value: object) -> None:
    """Refuse a view whose factory did not set the module seal."""
    try:
        seal = object.__getattribute__(value, "_seal")
    except AttributeError:
        seal = None
    if seal is not _VIEW_SEAL:
        raise ValueError("an algebra view is issued only by _issue_view")


@dataclass(frozen=True, slots=True)
class AlgebraView(Generic[E]):
    """A typed source expression paired with its effective parent element.

    The view is issued only by the bridge through ``_issue_view``.  It fixes
    the source, the parent that owns the element, the element itself, the
    target/generator/parameter symbol bindings, the interpretation, the
    conversion witness and the language signature its regions are read in.  The
    binding tuple is canonical by role and index: the target first, then the
    generators, then the parameters in index order.  A view binds either
    exactly one target at index 0 or a nonempty generator tuple with indices
    0..n-1; a generator view binds no parameters and no target.  The signature
    is the language of the region propositions, not a second world identity.

    ``source_domain`` is the source expression's intrinsic domain when the
    bridge cannot establish that it is total.  ``valid_on`` is the region on
    which the representation equals the source.  ``None`` means "total on the
    bridge's declared fragment"; a bridge with real holes must carry the
    proposition instead of a tautological region.  The two regions are
    independent: a total source (``source_domain`` is None) may have a
    representation that is valid only on a proper subregion (``valid_on`` is
    not None).  When both are present, ``valid_on`` must be provably a
    subregion of ``source_domain`` and both must be read in the same meaning
    environment; every present region must be read in the source's meaning
    world.  A region may be read in a descendant frame of that world.  The
    polynomial bridge is total on its fragment and always leaves both fields
    ``None``.

    The interpretation and the bindings must agree: a `PARAMETER_FAMILY` view
    binds at least one parameter, and every other interpretation binds none.
    The interpretation and the witness kind must also agree: an `EMBEDDED`
    view admits an embedding or representation-isomorphism witness but not a
    homomorphism, and a `PARAMETER_FAMILY` view admits only a
    representation-isomorphism witness.  A `FORMAL` view admits all three
    kinds; its witness flags alone govern what may be transferred.  The
    polynomial and rational bridges issue a representation-isomorphism
    witness; a view whose witness is not injective or does not preserve
    equality cannot transfer target equality back to the source, so
    `typed_view` refuses it.

    A view with an explicit ``source_domain`` or ``valid_on`` must record a
    witness that preserves definedness: otherwise the region claim cannot be
    transferred back to the source.  A total view (both regions absent) makes
    no region claim, so a homomorphism that does not preserve definedness is
    still admissible when it is injective and equality-preserving; admission
    then applies only the equality-transfer checks and invents no definedness
    claim.

    ``region_bindings`` is the binding view the region propositions are read
    over.  It defaults to the source's binding view, but a region read in a
    descendant frame may mention an extra declared symbol, in which case the
    issuer passes a larger explicit tuple.  It must be a tuple of distinct
    `FreeSymbol` values that covers every source free symbol and every free
    variable of each present region, and an entry for a source free symbol must
    carry that symbol's source sort; an explicit entry cannot disguise a
    non-dense source coordinate as dense.  `definedness` builds its `RegionSpec`
    coordinates and binding sorts from this tuple, not from the source binding
    view alone.
    """

    source: TypedExpr
    parent: Parent[E]
    value: E
    symbols: tuple[SymbolBinding, ...]
    interpretation: Interpretation
    witness: ConversionWitness
    signature: LanguageSignature
    source_domain: Proposition | None
    valid_on: Proposition | None
    region_bindings: tuple[FreeSymbol, ...] = ()
    _seal: object | None = field(
        init=False, default=None, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if self._seal is not _VIEW_SEAL:
            raise ValueError("an algebra view is issued only by _issue_view")
        if not isinstance(self.source, TypedExpr):
            raise TypeError("an algebra view needs a typed source expression")
        if not isinstance(self.parent, Parent):
            raise TypeError("an algebra view needs a parent")
        if not isinstance(self.interpretation, Interpretation):
            raise TypeError("an algebra view needs an interpretation")
        if not isinstance(self.witness, ConversionWitness):
            raise TypeError("an algebra view needs a conversion witness")
        consistency = _interpretation_witness_refusal(
            self.interpretation, self.witness
        )
        if consistency is not None:
            raise ValueError(consistency)
        if not isinstance(self.signature, LanguageSignature):
            raise TypeError("an algebra view needs a language signature")
        if self.source_domain is not None and not isinstance(
            self.source_domain, Proposition
        ):
            raise TypeError(
                "an algebra view source domain must be a proposition or None"
            )
        if self.valid_on is not None and not isinstance(
            self.valid_on, Proposition
        ):
            raise TypeError(
                "an algebra view validity region must be a proposition or None"
            )
        binding_refusal = _region_binding_refusal(
            self.source,
            self.source_domain,
            self.valid_on,
            self.region_bindings,
        )
        if binding_refusal is not None:
            raise ValueError(binding_refusal)
        refusal = _region_definedness_refusal(
            self.witness, self.source_domain, self.valid_on
        )
        if refusal is not None:
            raise ValueError(refusal)
        if (
            self.source_domain is not None
            and self.source_domain.meaning.world != self.source.meaning.world
        ):
            raise ValueError(
                "the algebra view source domain was read in another meaning "
                "world"
            )
        if (
            self.valid_on is not None
            and self.valid_on.meaning.world != self.source.meaning.world
        ):
            raise ValueError(
                "the algebra view validity region was read in another meaning "
                "world"
            )
        if (
            self.source_domain is not None
            and self.valid_on is not None
            and self.source_domain.meaning != self.valid_on.meaning
        ):
            raise ValueError(
                "the algebra view regions were read in different meaning "
                "environments"
            )
        symbols = tuple(self.symbols)
        if any(not isinstance(item, SymbolBinding) for item in symbols):
            raise TypeError("an algebra view holds symbol bindings")
        if len({item.symbol for item in symbols}) != len(symbols):
            raise ValueError("an algebra view cannot bind one symbol twice")
        targets = tuple(item for item in symbols if item.role is Role.TARGET)
        generators = tuple(
            item for item in symbols if item.role is Role.GENERATOR
        )
        if targets:
            if len(targets) != 1 or targets[0].index != 0:
                raise ValueError(
                    "an algebra view needs exactly one target binding at "
                    "index 0"
                )
            if generators:
                raise ValueError(
                    "an algebra view cannot bind both a target and generators"
                )
        else:
            if not generators:
                raise ValueError(
                    "an algebra view needs a target binding or generator "
                    "bindings"
                )
            if tuple(sorted(item.index for item in generators)) != tuple(
                range(len(generators))
            ):
                raise ValueError(
                    "generator bindings need the indices 0..n-1 without gaps"
                )
        parameters = tuple(
            item for item in symbols if item.role is Role.PARAMETER
        )
        if tuple(sorted(item.index for item in parameters)) != tuple(
            range(len(parameters))
        ):
            raise ValueError(
                "parameter bindings need the indices 0..n-1 without gaps"
            )
        if generators and parameters:
            raise ValueError("a generator view cannot bind parameters")
        if self.interpretation is Interpretation.PARAMETER_FAMILY:
            if not parameters:
                raise ValueError(
                    "a parameter-family view needs at least one parameter binding"
                )
        elif parameters:
            raise ValueError(
                "a non-parameter-family view cannot bind parameters"
            )
        canonical = tuple(
            sorted(
                symbols,
                key=lambda item: (_ROLE_ORDER[item.role], item.index),
            )
        )
        if canonical != symbols:
            object.__setattr__(self, "symbols", canonical)
        if not S.is_scalar(self.source.sort):
            raise ValueError("an algebra view needs a scalar source")
        if not self.parent.contains(self.value):
            raise ValueError("the value is not a member of the view's parent")
        bound = {item.symbol for item in symbols}
        free = {item.symbol_id for item in self.source.bindings.symbols}
        if not free <= bound:
            raise ValueError(
                "the algebra view does not bind every free symbol of the source"
            )

    def __getattribute__(self, name: str) -> object:
        if name in _VIEW_FIELDS:
            _require_view_seal(self)
        return object.__getattribute__(self, name)

    @property
    def conversion(self) -> ConversionKind:
        """The conversion kind recorded by the witness."""
        return self.witness.kind

    @property
    def definedness(self) -> Definedness:
        """The source's domain and representation region as one record.

        The record is built from the view's existing ``source_domain`` and
        ``valid_on`` propositions; it is not a second region authority.  A view
        with both regions absent is total on the bridge's fragment; equal
        regions are exact.  A total source with a partial representation is
        sufficient without a region certificate: the bridge's
        ``ConversionWitness`` is the evidence.  A strict validity region under
        a nontrivial domain must be a proved subregion, so the record carries
        the `SubregionCertificate` produced by the same restricted logic that
        admitted the view.  Every region's own definedness premises must be
        proved from its condition; an open premise raises `ValueError` instead
        of being ignored.  Any present region is paired with a conversion
        witness that preserves definedness, so the witness can support the
        region claim.  The `RegionSpec` coordinates and binding sorts come from
        ``region_bindings``, so a region read over extra child-frame coordinates
        keeps those coordinates instead of being squeezed into the source
        binding view.  A strict subregion whose coordinates are not dense
        rational/real raises `ValueError` rather than downgrading to a
        certificate-less record.
        """
        coordinates = tuple(
            item.symbol_id for item in self.region_bindings
        )
        sorts = tuple(
            (item.symbol_id, item.sort) for item in self.region_bindings
        )
        if self.source_domain is None:
            if self.valid_on is None:
                return _issue_definedness(
                    self.source, None, None, DefinednessExactness.TOTAL
                )
            if premises_proved_from(
                self.valid_on, self.valid_on, self.signature
            ) is not True:
                raise ValueError(
                    "the view validity region does not prove its definedness "
                    "premises"
                )
            return _issue_definedness(
                self.source,
                None,
                RegionSpec(coordinates, self.valid_on, sorts),
                DefinednessExactness.SUFFICIENT,
            )
        if premises_proved_from(
            self.source_domain, self.source_domain, self.signature
        ) is not True:
            raise ValueError(
                "the view source domain does not prove its definedness "
                "premises"
            )
        domain = RegionSpec(coordinates, self.source_domain, sorts)
        if self.valid_on is None or self.valid_on == self.source_domain:
            valid_on = None if self.valid_on is None else domain
            return _issue_definedness(
                self.source,
                domain,
                valid_on,
                DefinednessExactness.EXACT,
            )
        valid_on = RegionSpec(coordinates, self.valid_on, sorts)
        if not valid_on.is_dense or not domain.is_dense:
            raise ValueError(
                "the view validity region is a strict subregion, but its "
                "binding sorts are not dense rational/real coordinates, so no "
                "dense-order subregion certificate can be issued"
            )
        certificate = certify_subregion(
            valid_on, domain, self.signature
        )
        if certificate is None:
            raise ValueError(
                "the view validity region is not provably inside its source "
                "domain"
            )
        return _issue_definedness(
            self.source,
            domain,
            valid_on,
            DefinednessExactness.SUFFICIENT,
            certificate,
        )

    def generators_for(self, role: Role) -> tuple[SymbolId, ...]:
        """The generator symbols bound to `role`, in index order."""
        if not isinstance(role, Role):
            raise TypeError("a generator query needs a Role")
        return tuple(
            item.symbol for item in self.symbols if item.role is role
        )

    def symbol_for(self, role: Role, index: int) -> SymbolId | None:
        """The symbol bound to `(role, index)`, or None when it is unbound."""
        if not isinstance(role, Role):
            raise TypeError("a symbol query needs a Role")
        if isinstance(index, bool) or not isinstance(index, int):
            raise TypeError("a symbol query needs an integer index")
        for item in self.symbols:
            if item.role is role and item.index == index:
                return item.symbol
        return None


def _build_view(
    source: TypedExpr,
    parent: Parent[E],
    value: E,
    symbols: tuple[SymbolBinding, ...],
    interpretation: Interpretation,
    witness: ConversionWitness,
    source_domain: Proposition | None,
    valid_on: Proposition | None,
    *,
    signature: LanguageSignature,
    region_bindings: tuple[FreeSymbol, ...] | None = None,
) -> AlgebraView[E]:
    """Construct one algebra view after setting the module seal.

    ``region_bindings`` defaults to the source binding view.  An explicit
    tuple is needed only when a region read in a descendant frame mentions an
    extra declared symbol; the constructor validates that the tuple covers the
    source and every present region.
    """
    view = cast(AlgebraView[E], object.__new__(AlgebraView))
    if region_bindings is None:
        region_bindings = (
            source.bindings.symbols
            if isinstance(source, TypedExpr)
            else ()
        )
    object.__setattr__(view, "source", source)
    object.__setattr__(view, "parent", parent)
    object.__setattr__(view, "value", value)
    object.__setattr__(view, "symbols", symbols)
    object.__setattr__(view, "interpretation", interpretation)
    object.__setattr__(view, "witness", witness)
    object.__setattr__(view, "signature", signature)
    object.__setattr__(view, "source_domain", source_domain)
    object.__setattr__(view, "valid_on", valid_on)
    object.__setattr__(view, "region_bindings", region_bindings)
    object.__setattr__(view, "_seal", _VIEW_SEAL)
    view.__post_init__()
    return view


def _issue_view(
    source: TypedExpr,
    parent: Parent[E],
    value: E,
    symbols: tuple[SymbolBinding, ...],
    interpretation: Interpretation,
    witness: ConversionWitness,
    source_domain: Proposition | None,
    valid_on: Proposition | None,
    *,
    signature: LanguageSignature,
    region_bindings: tuple[FreeSymbol, ...] | None = None,
) -> AlgebraView[E] | ViewRefused:
    """Issue the only constructible algebra view, or refuse its region.

    ``source_domain`` and ``valid_on`` must be propositions or ``None``.  A
    total source may have a representation that is valid only on a proper
    subregion, so ``valid_on`` does not require a ``source_domain``.  Every
    present region must be read in the source's meaning world, and when both
    are present they must share one meaning environment; a region may be read
    in a descendant frame of the source's world.  Each region's own definedness
    premises must follow from its condition, and when both are present the
    restricted condition logic must prove that ``valid_on`` is a subregion of
    ``source_domain`` including the source domain's premises; an unprovable
    premise or inclusion is refused instead of being assumed.  A view that
    carries either region also needs a witness that preserves definedness;
    otherwise the region cannot be transferred back to the source and the
    factory refuses it with ``conversion_witness``.  The interpretation and
    the witness kind must agree: an ``EMBEDDED`` view refuses a homomorphism
    witness, and a ``PARAMETER_FAMILY`` view refuses an embedding or
    homomorphism witness; the factory refuses those contradictions with
    ``interpretation_witness`` before building.  ``signature`` is the
    language the two region propositions were read in.  ``region_bindings``
    defaults to the source binding view; an explicit tuple is required when a
    region read in a descendant frame mentions an extra declared symbol.  A
    tuple that does not cover the source or a present region's free variables,
    or that gives a source free symbol a different sort than the source binding
    view, is refused with ``region_bindings`` before the view is built.
    """
    if not isinstance(witness, ConversionWitness):
        raise TypeError("an algebra view needs a conversion witness")
    consistency = _interpretation_witness_refusal(interpretation, witness)
    if consistency is not None:
        return ViewRefused(
            Reason.FRAGMENT,
            consistency,
            frozenset({"interpretation_witness"}),
        )
    if not isinstance(signature, LanguageSignature):
        raise TypeError("an algebra view needs a language signature")
    if source_domain is not None and not isinstance(
        source_domain, Proposition
    ):
        return ViewRefused(
            Reason.FRAGMENT,
            "the view source domain is not a proposition",
            frozenset({"source_domain"}),
        )
    if valid_on is not None and not isinstance(valid_on, Proposition):
        return ViewRefused(
            Reason.FRAGMENT,
            "the view validity region is not a proposition",
            frozenset({"valid_on"}),
        )
    if region_bindings is None:
        region_bindings = (
            source.bindings.symbols
            if isinstance(source, TypedExpr)
            else ()
        )
    binding_refusal = _region_binding_refusal(
        source, source_domain, valid_on, region_bindings
    )
    if binding_refusal is not None:
        return ViewRefused(
            Reason.FRAGMENT,
            binding_refusal,
            frozenset({"region_bindings"}),
        )
    refusal = _region_definedness_refusal(witness, source_domain, valid_on)
    if refusal is not None:
        return ViewRefused(
            Reason.FRAGMENT, refusal, frozenset({"conversion_witness"})
        )
    if isinstance(source, TypedExpr):
        for name, region in (
            ("source domain", source_domain),
            ("validity region", valid_on),
        ):
            if (
                region is not None
                and region.meaning.world != source.meaning.world
            ):
                return ViewRefused(
                    Reason.FRAGMENT,
                    f"the view {name} was read in another meaning world",
                    frozenset({"region_world"}),
                )
    if (
        source_domain is not None
        and valid_on is not None
        and source_domain.meaning != valid_on.meaning
    ):
        return ViewRefused(
            Reason.FRAGMENT,
            "the view regions were read in different meaning environments",
            frozenset({"region_meaning"}),
        )
    if source_domain is not None and valid_on is not None:
        contained = proved_subregion(valid_on, source_domain, signature)
        if contained is not True:
            return ViewRefused(
                Reason.GUARDED,
                "the view validity region is not provably inside the source "
                "domain",
                frozenset({"region_coverage"}),
                (valid_on, source_domain),
            )
    else:
        region = source_domain if source_domain is not None else valid_on
        if (
            region is not None
            and premises_proved_from(region, region, signature) is not True
        ):
            return ViewRefused(
                Reason.GUARDED,
                "the view region does not prove its definedness premises",
                frozenset({"region_definedness"}),
                (region,),
            )
    return _build_view(
        source,
        parent,
        value,
        symbols,
        interpretation,
        witness,
        source_domain,
        valid_on,
        signature=signature,
        region_bindings=region_bindings,
    )


@dataclass(frozen=True, slots=True)
class ViewBuilt(Generic[E]):
    """A view was built."""

    view: AlgebraView[E]

    def __post_init__(self) -> None:
        if not isinstance(self.view, AlgebraView):
            raise TypeError("a built view needs an algebra view")


@dataclass(frozen=True, slots=True)
class ViewRefused:
    """A view was refused with the capability it needs."""

    reason: Reason
    detail: str
    missing: frozenset[str] = frozenset()
    conditions: tuple[Proposition, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("a view refusal needs a Reason")
        if not isinstance(self.detail, str):
            raise TypeError("a view refusal detail must be a string")
        if not self.detail:
            raise ValueError("a view refusal needs a detail")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError("view-refusal capabilities must be non-empty strings")
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError("view-refusal conditions must be propositions")
        object.__setattr__(self, "missing", missing)
        object.__setattr__(self, "conditions", conditions)


AlgebraViewOutcome: TypeAlias = ViewBuilt[E] | ViewRefused


@dataclass(frozen=True, slots=True)
class Rendered:
    """A view element was rendered back to a term."""

    term: T.Term

    def __post_init__(self) -> None:
        if not isinstance(self.term, T.Term):
            raise TypeError("a rendered result needs a term")


@dataclass(frozen=True, slots=True)
class RenderRefused:
    """An element cannot be rendered in this language."""

    reason: Reason
    detail: str
    missing: frozenset[str] = frozenset()

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("a render refusal needs a Reason")
        if not isinstance(self.detail, str):
            raise TypeError("a render refusal detail must be a string")
        if not self.detail:
            raise ValueError("a render refusal needs a detail")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError(
                "render-refusal capabilities must be non-empty strings"
            )
        object.__setattr__(self, "missing", missing)


RenderOutcome: TypeAlias = Rendered | RenderRefused


class AlgebraBridge(Protocol[V]):
    """An explicit conversion between terms and one parent's elements."""

    def to_view(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> AlgebraViewOutcome[V]:
        """Admit a typed source under a request, or name the missing capability."""

    def render(
        self, view: AlgebraView[V], value: V
    ) -> RenderOutcome:
        """Render `value` using the view's symbol bindings."""


class PolynomialBridge(AlgebraBridge[Polynomial[E]], Protocol[E]):
    """An explicit conversion between terms and one polynomial parent."""

    @property
    def ring(self) -> PolynomialRing[E]:
        """The polynomial ring this bridge interprets."""


def _admit_view_relation(
    view: AlgebraView[E], request: AlgebraRequest
) -> ViewRefused | None:
    """Check that a view may transfer target claims back to the source.

    The view's interpretation must be the request's interpretation.  A view
    that carries an explicit source domain or validity region is admitted only
    when its witness preserves definedness; without that fact the region claim
    cannot be transferred back to the source.  A total view makes no region
    claim, so a homomorphism that does not preserve definedness is still
    admissible when it is injective and equality-preserving; the admission then
    applies only the equality-transfer checks and invents no definedness claim.

    Equality transfers back only when the conversion witness records an
    injective, equality-preserving conversion.  A general homomorphism may be
    non-injective or may identify source expressions that are not equal;
    reading a target equality as a source equality through such a witness
    would invent an inverse the conversion does not have.
    """
    if view.interpretation is not request.interpretation:
        return ViewRefused(
            Reason.FRAGMENT,
            "the view interpretation does not match the request",
            frozenset({"interpretation_mismatch"}),
        )
    witness = view.witness
    # The view constructor already enforces this invariant; the admission
    # boundary re-establishes it independently because it is the point where a
    # target claim is trusted for transfer back to the source.
    refusal = _region_definedness_refusal(
        witness, view.source_domain, view.valid_on
    )
    if refusal is not None:
        return ViewRefused(
            Reason.FRAGMENT, refusal, frozenset({"conversion_witness"})
        )
    if not witness.injective or not witness.preserves_equality:
        return ViewRefused(
            Reason.FRAGMENT,
            "the conversion witness cannot transfer target equality back to "
            "the source",
            frozenset({"conversion_witness"}),
        )
    return None


def typed_view(
    bridge: AlgebraBridge[V],
    term: T.Term,
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    request: AlgebraRequest,
) -> AlgebraView[V] | ViewRefused | TypedExprFailure:
    """Elaborate `term` in `frame`, then admit it through `bridge`.

    This is the checker-facing admission path: the term is independently typed
    and expanded in the frame the claim was read in, then converted under the
    fixed algebra request.  A typing failure and a bridge refusal remain
    distinct closed outcomes so a checker can report the missing capability
    instead of turning it into a mathematical refutation.  A built view is
    admitted only when its interpretation matches the request and its
    conversion can transfer target claims back to the source: a region-bearing
    view needs a witness that preserves definedness, and equality transfer
    needs an injective, equality-preserving witness.
    """
    typed = elaborate.typed(term, frames, frame, signature)
    if not isinstance(typed, TypedExpr):
        return typed
    outcome = bridge.to_view(typed, request)
    if isinstance(outcome, ViewRefused):
        return outcome
    refusal = _admit_view_relation(outcome.view, request)
    if refusal is not None:
        return refusal
    return outcome.view


@dataclass(frozen=True, slots=True)
class SimplePolynomialBridge(Generic[E]):
    """The bridge for a ring whose coefficients are base literals."""

    ring: PolynomialRing[E]
    parent: Parent[Polynomial[E]]
    world: WorldId
    signature: LanguageSignature
    name_of: Callable[[SymbolId], str]
    render_coefficient: Callable[[E], T.Term]

    def __post_init__(self) -> None:
        if not isinstance(self.parent, Parent):
            raise TypeError("a polynomial bridge needs a parent")
        if self.parent.ring is not self.ring:
            raise ValueError("the parent does not own the bridge's ring")
        if isinstance(self.world, bool) or not isinstance(self.world, int):
            raise TypeError("a polynomial bridge needs a WorldId")

    def to_view(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> AlgebraViewOutcome[Polynomial[E]]:
        if not isinstance(source, TypedExpr):
            raise TypeError("an algebra view needs a typed source expression")
        if not isinstance(request, AlgebraRequest):
            raise TypeError("an algebra view needs an algebra request")
        if request.roles.target is None:
            return _view_refused(
                "target_role",
                "the simple bridge needs a target role",
            )
        refusal = _admit_source(source, self.world)
        if refusal is not None:
            return refusal
        refusal = _admit_request_world(source, request)
        if refusal is not None:
            return refusal
        if self.ring.generators != (request.target,):
            return _view_refused(
                "target_role",
                "the simple bridge needs the request target to be its only "
                "generator",
            )
        if request.parameters or request.parameter_ring is not None:
            return _view_refused(
                "parameter_ring",
                "the simple bridge has no parameter structure",
            )
        if request.interpretation not in (
            Interpretation.FORMAL,
            Interpretation.EMBEDDED,
        ):
            return _view_refused(
                "parameter_family_interpretation",
                "the simple bridge does not interpret a parameter family",
            )
        if request.coefficient.ring is not self.ring.coefficients:
            return _view_refused(
                "coefficient_parent",
                "the request coefficients are not the bridge's coefficients",
            )
        symbols = (SymbolBinding(request.target, Role.TARGET, 0),)
        refusal = _admit_bindings(source, symbols)
        if refusal is not None:
            return refusal
        converted = _convert_in_ring(self.ring, source.term, self.signature)
        if isinstance(converted, ViewRefused):
            return converted
        view = _issue_view(
            source,
            self.parent,
            converted,
            symbols,
            request.interpretation,
            ConversionWitness.representation_isomorphism(),
            None,
            None,
            signature=self.signature,
            region_bindings=source.bindings.symbols,
        )
        if isinstance(view, ViewRefused):
            return view
        return ViewBuilt(view)

    def render(
        self, view: AlgebraView[Polynomial[E]], value: Polynomial[E]
    ) -> RenderOutcome:
        if not isinstance(view, AlgebraView):
            raise TypeError("rendering needs an algebra view")
        if view.parent is not self.parent:
            raise ValueError("the view belongs to another parent")
        if not self.parent.contains(value):
            raise ValueError("the polynomial belongs to another ring")
        return _render_polynomial(
            self.ring,
            value,
            self.signature,
            self.name_of,
            self.render_coefficient,
            view.generators_for(Role.TARGET),
        )


@dataclass(frozen=True, slots=True)
class MultivariatePolynomialBridge(Generic[E]):
    """The bridge for ``K[x_1, ..., x_n]`` under a generator-mode request.

    The source's free symbols are mapped onto ``ring.generators`` in the ring's
    declared order.  The request's `variables` must be exactly that tuple, and
    each source free symbol that is a ring generator must carry the sort the
    request records for it; neither the role nor the sort is inferred from
    names or from the order the symbols happen to appear in the source
    expression.  The conversion is the same structural polynomial conversion as
    the univariate bridge and is total on its fragment, so a view carries
    neither ``source_domain`` nor ``valid_on``.

    A generator view has no single target and no formal parameters in this
    slice: the differentiation/integration/solve consumers are target-mode, so
    this bridge refuses those requests instead of choosing a generator as the
    target.  The bridge issues a representation-isomorphism witness, matching
    the univariate polynomial bridge.
    """

    ring: PolynomialRing[E]
    parent: Parent[Polynomial[E]]
    world: WorldId
    signature: LanguageSignature
    name_of: Callable[[SymbolId], str]
    render_coefficient: Callable[[E], T.Term]

    def __post_init__(self) -> None:
        if not isinstance(self.parent, Parent):
            raise TypeError("a polynomial bridge needs a parent")
        if self.parent.ring is not self.ring:
            raise ValueError("the parent does not own the bridge's ring")
        if isinstance(self.world, bool) or not isinstance(self.world, int):
            raise TypeError("a polynomial bridge needs a WorldId")

    def to_view(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> AlgebraViewOutcome[Polynomial[E]]:
        if not isinstance(source, TypedExpr):
            raise TypeError("an algebra view needs a typed source expression")
        if not isinstance(request, AlgebraRequest):
            raise TypeError("an algebra view needs an algebra request")
        refusal = _admit_source(source, self.world)
        if refusal is not None:
            return refusal
        refusal = _admit_request_world(source, request)
        if refusal is not None:
            return refusal
        if request.roles.target is not None:
            return _view_refused(
                "target_role",
                "the multivariate bridge has no target role; it binds the "
                "ordered generator tuple",
            )
        if request.roles.parameters or request.parameter_ring is not None:
            return _view_refused(
                "parameter_ring",
                "the multivariate bridge has no parameter structure",
            )
        if request.roles.variables != self.ring.generators:
            return _view_refused(
                "generator_roles",
                "the request generator roles are not the ring's generators in "
                "ring order",
            )
        if len(request.roles.variable_sorts) != len(self.ring.generators):
            return _view_refused(
                "variable_sort",
                "the request does not declare one sort per ring generator",
            )
        if request.interpretation not in (
            Interpretation.FORMAL,
            Interpretation.EMBEDDED,
        ):
            return _view_refused(
                "parameter_family_interpretation",
                "the multivariate bridge does not interpret a parameter "
                "family",
            )
        if request.coefficient.ring is not self.ring.coefficients:
            return _view_refused(
                "coefficient_parent",
                "the request coefficients are not the bridge's coefficients",
            )
        symbols = tuple(
            SymbolBinding(symbol_id, Role.GENERATOR, index)
            for index, symbol_id in enumerate(self.ring.generators)
        )
        refusal = _admit_bindings(source, symbols)
        if refusal is not None:
            return refusal
        generator_index = {
            symbol_id: index
            for index, symbol_id in enumerate(self.ring.generators)
        }
        for free in source.bindings.symbols:
            index = generator_index.get(free.symbol_id)
            if index is None:
                continue
            expected = request.roles.variable_sorts[index]
            if free.sort != expected:
                return _view_refused(
                    "variable_sort",
                    f"the source binds generator {free.symbol_id} as "
                    f"{free.sort!r}, but the request declares {expected!r}",
                )
        converted = _convert_in_ring(self.ring, source.term, self.signature)
        if isinstance(converted, ViewRefused):
            return converted
        view = _issue_view(
            source,
            self.parent,
            converted,
            symbols,
            request.interpretation,
            ConversionWitness.representation_isomorphism(),
            None,
            None,
            signature=self.signature,
            region_bindings=source.bindings.symbols,
        )
        if isinstance(view, ViewRefused):
            return view
        return ViewBuilt(view)

    def render(
        self, view: AlgebraView[Polynomial[E]], value: Polynomial[E]
    ) -> RenderOutcome:
        if not isinstance(view, AlgebraView):
            raise TypeError("rendering needs an algebra view")
        if view.parent is not self.parent:
            raise ValueError("the view belongs to another parent")
        if not self.parent.contains(value):
            raise ValueError("the polynomial belongs to another ring")
        generators = view.generators_for(Role.GENERATOR)
        if generators != self.ring.generators:
            raise ValueError(
                "the view does not bind the bridge's generators in ring order"
            )
        return _render_polynomial(
            self.ring,
            value,
            self.signature,
            self.name_of,
            self.render_coefficient,
            generators,
        )


@dataclass(frozen=True, slots=True)
class ParameterPolynomialBridge(Generic[E]):
    """A bridge for `K[parameters][target]`.

    Parameter symbols become constants of the target ring (elements of the
    coefficient ring), while target symbols become target generators. The two
    maps are explicit and disjoint; no symbol is guessed to be a coefficient or
    a variable from its name or position.
    """

    ring: PolynomialRing[Polynomial[E]]
    target_parent: Parent[Polynomial[Polynomial[E]]]
    coefficient_ring: PolynomialRing[E]
    coefficient_parent: Parent[Polynomial[E]]
    world: WorldId
    parameters: Mapping[SymbolId, int]
    signature: LanguageSignature
    name_of: Callable[[SymbolId], str]
    embed_rational: Callable[[Fraction], Polynomial[E]]
    render_base: Callable[[E], T.Term]

    def __post_init__(self) -> None:
        if not isinstance(self.target_parent, Parent):
            raise TypeError("a parameter bridge needs a target parent")
        if not isinstance(self.coefficient_parent, Parent):
            raise TypeError("a parameter bridge needs a coefficient parent")
        if self.target_parent.ring is not self.ring:
            raise ValueError("the target parent does not own the bridge's ring")
        if self.coefficient_parent.ring is not self.coefficient_ring:
            raise ValueError(
                "the coefficient parent does not own the coefficient ring"
            )
        if isinstance(self.world, bool) or not isinstance(self.world, int):
            raise TypeError("a parameter bridge needs a WorldId")
        parameters = MappingProxyType(dict(self.parameters))
        object.__setattr__(self, "parameters", parameters)
        if set(parameters) & set(self.ring.generators):
            raise ValueError("a symbol cannot be both a target and a parameter")
        if set(parameters) != set(self.coefficient_ring.generators):
            raise ValueError(
                "the parameter map must cover exactly the coefficient "
                "generators"
            )
        for index in parameters.values():
            if not 0 <= index < len(self.coefficient_ring.generators):
                raise ValueError("a parameter index is outside the coefficient ring")
        for symbol_id, index in parameters.items():
            if self.coefficient_ring.generators[index] != symbol_id:
                raise ValueError(
                    "a parameter index does not name its coefficient generator"
                )

    def _convert_term(
        self, term: T.Term
    ) -> Polynomial[Polynomial[E]] | ViewRefused:
        target = self.ring
        coefficient_ring = self.coefficient_ring
        target_indices = {
            symbol_id: index
            for index, symbol_id in enumerate(target.generators)
        }
        parameters = dict(self.parameters)

        def resolve(
            symbol_id: SymbolId,
        ) -> Polynomial[Polynomial[E]] | None:
            index = target_indices.get(symbol_id)
            if index is not None:
                return target.generator(index)
            parameter = parameters.get(symbol_id)
            if parameter is not None:
                return target.constant(
                    coefficient_ring.generator(parameter)
                )
            return None

        def embed(value: Fraction) -> Polynomial[Polynomial[E]] | None:
            return target.constant(self.embed_rational(value))

        return _convert_polynomial(
            target,
            term,
            self.signature,
            resolve,
            embed,
            target.is_nonzero_constant,
        )

    def to_view(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> AlgebraViewOutcome[Polynomial[Polynomial[E]]]:
        if not isinstance(source, TypedExpr):
            raise TypeError("an algebra view needs a typed source expression")
        if not isinstance(request, AlgebraRequest):
            raise TypeError("an algebra view needs an algebra request")
        if request.roles.target is None:
            return _view_refused(
                "target_role",
                "the parameter bridge needs a target role",
            )
        refusal = _admit_source(source, self.world)
        if refusal is not None:
            return refusal
        refusal = _admit_request_world(source, request)
        if refusal is not None:
            return refusal
        if self.ring.generators != (request.target,):
            return _view_refused(
                "target_role",
                "the parameter bridge needs the request target to be its only "
                "generator",
            )
        if request.parameter_ring is None:
            return _view_refused(
                "parameter_ring",
                "the parameter bridge needs a parameter structure",
            )
        if request.parameters != self.coefficient_ring.generators:
            return _view_refused(
                "parameter_ring",
                "the request parameters are not the coefficient generators",
            )
        if request.parameter_ring.ring is not self.coefficient_ring:
            return _view_refused(
                "parameter_ring",
                "the request parameter ring is not the coefficient ring",
            )
        if request.parameter_ring.spec != self.coefficient_parent.spec:
            return _view_refused(
                "parameter_ring",
                "the request parameter ring does not extend the coefficient "
                "parent",
            )
        if request.interpretation is not Interpretation.PARAMETER_FAMILY:
            return _view_refused(
                "parameter_family_interpretation",
                "the parameter bridge needs the parameter-family "
                "interpretation",
            )
        if request.coefficient.ring is not self.coefficient_ring.coefficients:
            return _view_refused(
                "coefficient_parent",
                "the request coefficients are not the bridge's coefficients",
            )
        if any(
            self.parameters.get(symbol_id) != index
            for index, symbol_id in enumerate(request.parameters)
        ):
            return _view_refused(
                "parameter_ring",
                "the parameter map does not match the request parameters",
            )
        symbols = (
            SymbolBinding(request.target, Role.TARGET, 0),
            *(
                SymbolBinding(symbol_id, Role.PARAMETER, index)
                for index, symbol_id in enumerate(request.parameters)
            ),
        )
        refusal = _admit_bindings(source, symbols)
        if refusal is not None:
            return refusal
        converted = self._convert_term(source.term)
        if isinstance(converted, ViewRefused):
            return converted
        view = _issue_view(
            source,
            self.target_parent,
            converted,
            symbols,
            request.interpretation,
            ConversionWitness.representation_isomorphism(),
            None,
            None,
            signature=self.signature,
            region_bindings=source.bindings.symbols,
        )
        if isinstance(view, ViewRefused):
            return view
        return ViewBuilt(view)

    def render(
        self,
        view: AlgebraView[Polynomial[Polynomial[E]]],
        value: Polynomial[Polynomial[E]],
    ) -> RenderOutcome:
        if not isinstance(view, AlgebraView):
            raise TypeError("rendering needs an algebra view")
        if view.parent is not self.target_parent:
            raise ValueError("the view belongs to another parent")
        if not self.target_parent.contains(value):
            raise ValueError("the polynomial belongs to another ring")
        heads = _structural_heads(self.signature)
        if heads is None:
            return RenderRefused(
                Reason.FRAGMENT,
                "the language has no structural heads for polynomials",
                frozenset({"structural_heads"}),
            )
        plus, times, power = heads
        parameter_symbols = view.generators_for(Role.PARAMETER)

        def render_coefficient(coefficient: Polynomial[E]) -> T.Term | None:
            return _render_terms(
                self.coefficient_ring,
                coefficient,
                plus,
                times,
                power,
                self.name_of,
                self.render_base,
                parameter_symbols,
            )

        rendered = _render_terms(
            self.ring,
            value,
            plus,
            times,
            power,
            self.name_of,
            render_coefficient,
            view.generators_for(Role.TARGET),
        )
        if rendered is None:
            return RenderRefused(
                Reason.FRAGMENT,
                "a coefficient cannot be rendered in this language",
                frozenset({"coefficient_rendering"}),
            )
        return Rendered(rendered)


@dataclass(frozen=True, slots=True)
class RationalFunctionBridge(Generic[E]):
    """The bridge for a univariate rational-function field ``K(x)``.

    The conversion is the formal fraction-field representation of literals,
    generators, sums, products and integer powers.  A negative power is an
    explicit inverse and introduces the source condition that its base is
    nonzero; the bridge keeps every such condition, including factors that the
    fraction field cancels.  The resulting ``source_domain``/``valid_on`` is a
    single ``Ne(denominator, 0)`` proposition rendered through the view's
    symbol bindings and elaborated in the source frame.  A source with no
    inverse denominators is total and leaves both regions ``None``.

    The formal fraction field is a representation isomorphism on that region.
    Outside the accepted term fragment the bridge returns a structured
    ``ViewRefused``; it never invents an implicit division or a domain
    condition.  The conversion rules follow `cas_v5_arch.md` §7.8 and §32.6.
    """

    field: RationalFunctionField[E]
    parent: Parent[RationalFunction[E]]
    world: WorldId
    signature: LanguageSignature
    frames: FrameStore
    name_of: Callable[[SymbolId], str]
    render_coefficient: Callable[[E], T.Term]

    def __post_init__(self) -> None:
        if not isinstance(self.field, RationalFunctionField):
            raise TypeError(
                "a rational bridge needs a rational-function field"
            )
        if not isinstance(self.parent, Parent):
            raise TypeError("a rational bridge needs a parent")
        if self.parent.ring is not self.field:
            raise ValueError("the parent does not own the bridge's field")
        if isinstance(self.world, bool) or not isinstance(self.world, int):
            raise TypeError("a rational bridge needs a WorldId")
        if not isinstance(self.frames, FrameStore):
            raise TypeError("a rational bridge needs a frame store")
        if self.frames.world.id != self.world:
            raise ValueError(
                "the bridge frame store is in another meaning world"
            )
        if self.frames.world.language is not self.signature:
            raise ValueError(
                "the bridge signature is not the frame store language"
            )

    def to_view(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> AlgebraViewOutcome[RationalFunction[E]]:
        if not isinstance(source, TypedExpr):
            raise TypeError("an algebra view needs a typed source expression")
        if not isinstance(request, AlgebraRequest):
            raise TypeError("an algebra view needs an algebra request")
        if request.roles.target is None:
            return _view_refused(
                "target_role",
                "the rational bridge needs a target role",
            )
        refusal = _admit_source(source, self.world)
        if refusal is not None:
            return refusal
        refusal = _admit_request_world(source, request)
        if refusal is not None:
            return refusal
        try:
            self.frames.get(source.meaning.frame)
        except KeyError:
            return _view_refused(
                "source_frame",
                "the source frame is not in the bridge's frame store",
            )
        if self.field.generators != (request.target,):
            return _view_refused(
                "target_role",
                "the rational bridge needs the request target to be its only "
                "generator",
            )
        if request.parameters or request.parameter_ring is not None:
            return _view_refused(
                "parameter_ring",
                "the rational bridge has no parameter structure",
            )
        if request.interpretation not in (
            Interpretation.FORMAL,
            Interpretation.EMBEDDED,
        ):
            return _view_refused(
                "parameter_family_interpretation",
                "the rational bridge does not interpret a parameter family",
            )
        if request.coefficient.ring is not self.field.coefficients:
            return _view_refused(
                "coefficient_parent",
                "the request coefficients are not the bridge's coefficients",
            )
        symbols = (SymbolBinding(request.target, Role.TARGET, 0),)
        refusal = _admit_bindings(source, symbols)
        if refusal is not None:
            return refusal
        converted = _convert_rational(self.field, source.term, self.signature)
        if isinstance(converted, ViewRefused):
            return converted
        polynomials = self.field.polynomials
        if polynomials.is_one(converted.denominator):
            source_domain = None
            valid_on = None
        else:
            rendered = _render_polynomial(
                polynomials,
                converted.denominator,
                self.signature,
                self.name_of,
                self.render_coefficient,
                (request.target,),
            )
            if isinstance(rendered, RenderRefused):
                return ViewRefused(
                    rendered.reason,
                    "the source denominator cannot be rendered: "
                    + rendered.detail,
                    rendered.missing,
                )
            ne_symbol = self.signature.symbol_of(StructuralHead.NE)
            if ne_symbol is None:
                return _view_refused(
                    "definedness_region",
                    "the language has no inequality head for the denominator "
                    "condition",
                )
            condition = T.app(
                T.symbol(ne_symbol, StructuralHead.NE.value),
                rendered.term,
                T.number(0),
            )
            issued = elaborate.proposition(
                condition,
                self.frames,
                source.meaning.frame,
                self.signature,
            )
            if not isinstance(issued, Proposition):
                return _view_refused(
                    "definedness_region",
                    "the denominator condition is not a proposition: "
                    + issued.detail,
                )
            source_domain = issued
            valid_on = issued
        view = _issue_view(
            source,
            self.parent,
            converted.value,
            symbols,
            request.interpretation,
            ConversionWitness.representation_isomorphism(),
            source_domain,
            valid_on,
            signature=self.signature,
            region_bindings=source.bindings.symbols,
        )
        if isinstance(view, ViewRefused):
            return view
        return ViewBuilt(view)

    def render(
        self,
        view: AlgebraView[RationalFunction[E]],
        value: RationalFunction[E],
    ) -> RenderOutcome:
        if not isinstance(view, AlgebraView):
            raise TypeError("rendering needs an algebra view")
        if view.parent is not self.parent:
            raise ValueError("the view belongs to another parent")
        if not self.parent.contains(value):
            raise ValueError("the rational function belongs to another field")
        return _render_rational(
            self.field,
            value,
            self.signature,
            self.name_of,
            self.render_coefficient,
            view.generators_for(Role.TARGET),
        )


def _view_refused(missing: str, detail: str) -> ViewRefused:
    """One fragment refusal with its capability key."""
    return ViewRefused(Reason.FRAGMENT, detail, frozenset({missing}))


def _admit_source(source: TypedExpr, world: WorldId) -> ViewRefused | None:
    """Check the source sort and meaning world shared by all bridges."""
    if not S.is_scalar(source.sort):
        return _view_refused(
            "scalar_source",
            "the source does not have a scalar sort",
        )
    if source.meaning.world != world:
        return _view_refused(
            "world_identity",
            "the source was read in another meaning world",
        )
    return None


def _admit_request_world(
    source: TypedExpr, request: AlgebraRequest
) -> ViewRefused | None:
    """Refuse a request whose role symbols belong to another meaning world.

    `VariableRoles` fixes target and parameter `SymbolId` values together with
    the world whose namespace defines them.  A bare integer id is not a global
    identity: two assemblies may issue the same integer for different symbols.
    The bridge therefore compares the request's role world with the typed
    source's meaning world before any role or generator check.  A request with
    no bound world is refused as well; an `AlgebraRequest` already rejects that
    state, so the check is the bridge's independent boundary.
    """
    world = request.roles.world
    if world is None:
        return _view_refused(
            "request_world",
            "the algebra request does not fix a meaning world for its roles",
        )
    if world != source.meaning.world:
        return _view_refused(
            "request_world",
            "the algebra request roles belong to another meaning world",
        )
    return None


def _admit_bindings(
    source: TypedExpr, symbols: tuple[SymbolBinding, ...]
) -> ViewRefused | None:
    """Refuse a source whose free symbols are not scalar bound generators."""
    non_scalar = tuple(
        item
        for item in source.bindings.symbols
        if not S.is_scalar(item.sort)
    )
    if non_scalar:
        rendered = ", ".join(
            f"{item.symbol_id} ({item.sort!r})" for item in non_scalar
        )
        return _view_refused(
            "scalar_symbol",
            f"free symbols must have scalar sorts: {rendered}",
        )
    bound = {item.symbol for item in symbols}
    missing = tuple(
        item.symbol_id
        for item in source.bindings.symbols
        if item.symbol_id not in bound
    )
    if missing:
        rendered = ", ".join(str(symbol_id) for symbol_id in missing)
        return _view_refused(
            "symbol_mapping",
            f"free symbols have no generator binding: {rendered}",
        )
    return None


def _structural_heads(
    signature: LanguageSignature,
) -> tuple[T.SymbolRef, T.SymbolRef, T.SymbolRef] | None:
    """The plus, times and power symbols, or None when the language lacks one."""
    plus_id = signature.symbol_of(StructuralHead.PLUS)
    times_id = signature.symbol_of(StructuralHead.TIMES)
    power_id = signature.symbol_of(StructuralHead.POWER)
    if plus_id is None or times_id is None or power_id is None:
        return None
    return (
        T.symbol(plus_id, "Plus"),
        T.symbol(times_id, "Times"),
        T.symbol(power_id, "Power"),
    )


def _render_terms(
    ring: PolynomialRing[E],
    value: Polynomial[E],
    plus: T.SymbolRef,
    times: T.SymbolRef,
    power: T.SymbolRef,
    name_of: Callable[[SymbolId], str],
    render_coefficient: Callable[[E], T.Term | None],
    generator_symbols: tuple[SymbolId, ...],
) -> T.Term | None:
    """Render one polynomial using an explicit generator-symbol alignment."""
    if len(generator_symbols) != len(ring.generators):
        raise ValueError("the view does not map every generator")
    coefficients = ring.coefficients
    if not value.terms:
        return render_coefficient(coefficients.zero())
    rendered: list[T.Term] = []
    for exponents, coefficient in value.terms:
        factors: list[T.Term] = []
        if not coefficients.is_one(coefficient):
            rendered_coefficient = render_coefficient(coefficient)
            if rendered_coefficient is None:
                return None
            factors.append(rendered_coefficient)
        for index, exponent in enumerate(exponents):
            if exponent == 0:
                continue
            generator_id = generator_symbols[index]
            generator = T.symbol(generator_id, name_of(generator_id))
            if exponent == 1:
                factors.append(generator)
            else:
                factors.append(T.app(power, generator, T.number(exponent)))
        if not factors:
            rendered_one = render_coefficient(coefficients.one())
            if rendered_one is None:
                return None
            factors.append(rendered_one)
        rendered.append(
            factors[0] if len(factors) == 1 else T.app(times, *factors)
        )
    return rendered[0] if len(rendered) == 1 else T.app(plus, *rendered)


def _render_polynomial(
    ring: PolynomialRing[E],
    value: Polynomial[E],
    signature: LanguageSignature,
    name_of: Callable[[SymbolId], str],
    render_coefficient: Callable[[E], T.Term | None],
    generator_symbols: tuple[SymbolId, ...],
) -> RenderOutcome:
    """Render a polynomial member through a view's generator symbols."""
    if not ring.contains(value):
        raise ValueError("the polynomial belongs to another ring")
    heads = _structural_heads(signature)
    if heads is None:
        return RenderRefused(
            Reason.FRAGMENT,
            "the language has no structural heads for polynomials",
            frozenset({"structural_heads"}),
        )
    plus, times, power = heads
    rendered = _render_terms(
        ring,
        value,
        plus,
        times,
        power,
        name_of,
        render_coefficient,
        generator_symbols,
    )
    if rendered is None:
        return RenderRefused(
            Reason.FRAGMENT,
            "a coefficient cannot be rendered in this language",
            frozenset({"coefficient_rendering"}),
        )
    return Rendered(rendered)


def _convert_in_ring(
    ring: PolynomialRing[E],
    term: T.Term,
    signature: LanguageSignature,
) -> Polynomial[E] | ViewRefused:
    """Convert a term in `ring`, embedding rational literals when possible."""
    coefficients = ring.coefficients
    indices = {
        symbol_id: index for index, symbol_id in enumerate(ring.generators)
    }

    def resolve(symbol_id: SymbolId) -> Polynomial[E] | None:
        index = indices.get(symbol_id)
        return None if index is None else ring.generator(index)

    def embed(value: Fraction) -> Polynomial[E] | None:
        if value.denominator == 1:
            return ring.constant(
                coefficients.mul_int(coefficients.one(), value.numerator)
            )
        if not isinstance(coefficients, RationalEmbedding):
            return None
        embedding = cast(RationalEmbedding[E], coefficients)
        return ring.constant(
            embedding.of_rational(value.numerator, value.denominator)
        )

    return _convert_polynomial(
        ring,
        term,
        signature,
        resolve,
        embed,
        ring.is_nonzero_constant,
    )


def _convert_polynomial(
    ring: PolynomialRing[E],
    term: T.Term,
    signature: LanguageSignature,
    resolve: Callable[[SymbolId], Polynomial[E] | None],
    embed: Callable[[Fraction], Polynomial[E] | None],
    nonzero_constant: Callable[[Polynomial[E]], bool],
) -> Polynomial[E] | ViewRefused:
    """The shared structural conversion used by both bridges.

    Every refusal names the capability it lacks.  In particular a zero power is
    never projected onto the ring's `a^0 = 1` unless the base is a globally
    nonzero constant; a formal parameter is not globally nonzero.
    """

    def convert(current: T.Term) -> Polynomial[E] | ViewRefused:
        if isinstance(current, T.IntLit):
            embedded = embed(Fraction(current.value))
            if embedded is None:
                return _view_refused(
                    "rational_embedding",
                    "the coefficient structure cannot embed a rational literal",
                )
            return embedded
        if isinstance(current, T.RatLit):
            embedded = embed(current.value)
            if embedded is None:
                return _view_refused(
                    "rational_embedding",
                    "the coefficient structure cannot embed a rational literal",
                )
            return embedded
        if isinstance(current, T.SymbolRef):
            resolved = resolve(current.symbol_id)
            if resolved is None:
                return _view_refused(
                    "symbol_mapping",
                    f"symbol {current.symbol_id} has no generator binding",
                )
            return resolved
        if not isinstance(current, T.Apply) or not isinstance(
            current.operator, T.SymbolRef
        ):
            return _view_refused(
                "polynomial_representation",
                "the source is outside the polynomial representation",
            )
        head = signature.head_of(current.operator.symbol_id)
        if head is StructuralHead.PLUS:
            total = ring.zero()
            for argument in current.arguments:
                converted = convert(argument)
                if isinstance(converted, ViewRefused):
                    return converted
                total = ring.add(total, converted)
            return total
        if head is StructuralHead.TIMES:
            product = ring.one()
            for argument in current.arguments:
                converted = convert(argument)
                if isinstance(converted, ViewRefused):
                    return converted
                product = ring.mul(product, converted)
            return product
        if head is StructuralHead.POWER:
            if len(current.arguments) != 2:
                return _view_refused(
                    "polynomial_representation",
                    "Power needs exactly two arguments",
                )
            base_term, exponent_term = current.arguments
            if not isinstance(exponent_term, T.IntLit):
                return _view_refused(
                    "integer_exponent",
                    "the polynomial fragment needs an integer exponent",
                )
            if exponent_term.value < 0:
                return _view_refused(
                    "nonnegative_power",
                    "the polynomial fragment needs a nonnegative exponent",
                )
            base = convert(base_term)
            if isinstance(base, ViewRefused):
                return base
            if exponent_term.value == 0:
                # The ring defines a^0 = 1 for every member, including zero.
                # The source expression does not: Power(f, 0) is defined only
                # where f is defined and nonzero.  Project it only when the
                # base is a globally nonzero constant, so no definedness
                # condition can be erased.
                if not nonzero_constant(base):
                    return _view_refused(
                        "defined_zero_power",
                        "a zero power needs a globally nonzero constant base",
                    )
                return ring.one()
            return ring.pow(base, exponent_term.value)
        return _view_refused(
            "polynomial_representation",
            "the source is outside the polynomial representation",
        )

    return convert(term)


@dataclass(frozen=True, slots=True)
class _RationalConversion(Generic[E]):
    """A converted rational function and the source's denominator factors.

    `denominator` is the product of the inverse bases and their nested
    denominators.  It is `one` exactly when the source has no hole, so the
    bridge can issue ``None`` for a total view instead of a tautological
    proposition.
    """

    value: RationalFunction[E]
    denominator: Polynomial[E]


def _source_denominator(
    polynomials: PolynomialRing[E],
    current: Polynomial[E],
    factor: Polynomial[E],
) -> Polynomial[E]:
    """Add one source hole, dropping a globally nonzero constant factor."""
    if polynomials.is_nonzero_constant(factor):
        return current
    return polynomials.mul(current, factor)


def _convert_rational(
    field: RationalFunctionField[E],
    term: T.Term,
    signature: LanguageSignature,
) -> _RationalConversion[E] | ViewRefused:
    """Convert a term into `K(x)`, accepting negative integer powers.

    The accepted fragment is literals, the polynomial ring's generators, sums,
    products and integer powers.  A negative power is an explicit inverse; its
    base contributes a nonzero condition, and any hole inside the base remains
    even when the fraction field cancels the factor.  Terms outside the
    fragment return a structured refusal.

    Zero powers follow the same boundary as the polynomial bridge: `Power(f, 0)`
    is projected only when the converted base is a globally nonzero constant.
    A negative power of the zero rational function is outside the fragment and
    is refused instead of raising from the field inverse.
    """
    polynomials = field.polynomials
    coefficients = polynomials.coefficients
    indices = {
        symbol_id: index
        for index, symbol_id in enumerate(polynomials.generators)
    }

    def embed(value: Fraction) -> RationalFunction[E] | None:
        if value.denominator == 1:
            coefficient = coefficients.mul_int(
                coefficients.one(), value.numerator
            )
        elif isinstance(coefficients, RationalEmbedding):
            embedding = cast(RationalEmbedding[E], coefficients)
            coefficient = embedding.of_rational(
                value.numerator, value.denominator
            )
        else:
            return None
        return field.of_polynomial(polynomials.constant(coefficient))

    def contains_inverse(current: T.Term) -> bool:
        """Whether a term contains an explicit negative power.

        A zero power must not erase the hole introduced by an inverse.  Even
        when the formal rational function normalizes to a constant, the source
        expression may be undefined where the inverse's base vanishes.
        """
        if not isinstance(current, T.Apply) or not isinstance(
            current.operator, T.SymbolRef
        ):
            return False
        head = signature.head_of(current.operator.symbol_id)
        if (
            head is StructuralHead.POWER
            and len(current.arguments) == 2
            and isinstance(current.arguments[1], T.IntLit)
            and current.arguments[1].value < 0
        ):
            return True
        return any(
            contains_inverse(argument) for argument in current.arguments
        )

    def convert(
        current: T.Term,
    ) -> _RationalConversion[E] | ViewRefused:
        if isinstance(current, T.IntLit):
            embedded = embed(Fraction(current.value))
            if embedded is None:
                return _view_refused(
                    "rational_embedding",
                    "the coefficient structure cannot embed a rational literal",
                )
            return _RationalConversion(embedded, polynomials.one())
        if isinstance(current, T.RatLit):
            embedded = embed(current.value)
            if embedded is None:
                return _view_refused(
                    "rational_embedding",
                    "the coefficient structure cannot embed a rational literal",
                )
            return _RationalConversion(embedded, polynomials.one())
        if isinstance(current, T.SymbolRef):
            index = indices.get(current.symbol_id)
            if index is None:
                return _view_refused(
                    "symbol_mapping",
                    f"symbol {current.symbol_id} has no generator binding",
                )
            return _RationalConversion(
                field.of_polynomial(polynomials.generator(index)),
                polynomials.one(),
            )
        if not isinstance(current, T.Apply) or not isinstance(
            current.operator, T.SymbolRef
        ):
            return _view_refused(
                "rational_function_representation",
                "the source is outside the rational-function representation",
            )
        head = signature.head_of(current.operator.symbol_id)
        if head is StructuralHead.PLUS:
            total = field.zero()
            denominator = polynomials.one()
            for argument in current.arguments:
                converted = convert(argument)
                if isinstance(converted, ViewRefused):
                    return converted
                total = field.add(total, converted.value)
                denominator = polynomials.mul(
                    denominator, converted.denominator
                )
            return _RationalConversion(total, denominator)
        if head is StructuralHead.TIMES:
            product = field.one()
            denominator = polynomials.one()
            for argument in current.arguments:
                converted = convert(argument)
                if isinstance(converted, ViewRefused):
                    return converted
                product = field.mul(product, converted.value)
                denominator = polynomials.mul(
                    denominator, converted.denominator
                )
            return _RationalConversion(product, denominator)
        if head is StructuralHead.POWER:
            if len(current.arguments) != 2:
                return _view_refused(
                    "rational_function_representation",
                    "Power needs exactly two arguments",
                )
            base_term, exponent_term = current.arguments
            if not isinstance(exponent_term, T.IntLit):
                return _view_refused(
                    "integer_exponent",
                    "the rational fragment needs an integer exponent",
                )
            base = convert(base_term)
            if isinstance(base, ViewRefused):
                return base
            exponent = exponent_term.value
            if exponent == 0:
                if contains_inverse(base_term):
                    return _view_refused(
                        "defined_zero_power",
                        "a zero power cannot erase an inverse's hole",
                    )
                if polynomials.is_one(
                    base.value.denominator
                ) and polynomials.is_nonzero_constant(base.value.numerator):
                    return _RationalConversion(
                        field.one(), polynomials.one()
                    )
                return _view_refused(
                    "defined_zero_power",
                    "a zero power needs a globally nonzero constant base",
                )
            if exponent > 0:
                return _RationalConversion(
                    field.pow(base.value, exponent), base.denominator
                )
            if base.value.numerator.is_zero():
                return _view_refused(
                    "defined_negative_power",
                    "a negative power needs a nonzero rational base",
                )
            factor = polynomials.pow(base.value.numerator, -exponent)
            denominator = _source_denominator(
                polynomials, base.denominator, factor
            )
            return _RationalConversion(
                field.inv(field.pow(base.value, -exponent)),
                denominator,
            )
        return _view_refused(
            "rational_function_representation",
            "the source is outside the rational-function representation",
        )

    return convert(term)


def _render_rational(
    field: RationalFunctionField[E],
    value: RationalFunction[E],
    signature: LanguageSignature,
    name_of: Callable[[SymbolId], str],
    render_coefficient: Callable[[E], T.Term],
    generator_symbols: tuple[SymbolId, ...],
) -> RenderOutcome:
    """Render a rational function as `numerator * denominator^-1`."""
    polynomials = field.polynomials
    if not field.contains(value):
        raise ValueError("the rational function belongs to another field")

    def render_member(member: Polynomial[E]) -> T.Term | RenderRefused:
        outcome = _render_polynomial(
            polynomials,
            member,
            signature,
            name_of,
            render_coefficient,
            generator_symbols,
        )
        if isinstance(outcome, RenderRefused):
            return outcome
        return outcome.term

    numerator = render_member(value.numerator)
    if isinstance(numerator, RenderRefused):
        return numerator
    if polynomials.is_one(value.denominator):
        return Rendered(numerator)
    denominator = render_member(value.denominator)
    if isinstance(denominator, RenderRefused):
        return denominator
    power_id = signature.symbol_of(StructuralHead.POWER)
    times_id = signature.symbol_of(StructuralHead.TIMES)
    if power_id is None or times_id is None:
        return RenderRefused(
            Reason.FRAGMENT,
            "the language has no structural heads for rational functions",
            frozenset({"structural_heads"}),
        )
    power = T.symbol(power_id, StructuralHead.POWER.value)
    times = T.symbol(times_id, StructuralHead.TIMES.value)
    return Rendered(
        T.app(
            times,
            numerator,
            T.app(power, denominator, T.number(-1)),
        )
    )


__all__ = [
    "AlgebraBridge",
    "AlgebraView",
    "AlgebraViewOutcome",
    "ConversionKind",
    "ConversionWitness",
    "MultivariatePolynomialBridge",
    "ParameterPolynomialBridge",
    "PolynomialBridge",
    "RationalFunctionBridge",
    "RenderOutcome",
    "RenderRefused",
    "Rendered",
    "SimplePolynomialBridge",
    "SymbolBinding",
    "ViewBuilt",
    "ViewRefused",
    "typed_view",
]
