"""Parents: an effective structure together with its complete description.

A `ParentSpec` is the description, and structural equality is its identity. The
registry issues one stable `ParentId` per description, so two independently
written descriptions of the same structure resolve to the same parent, while two
different structures never share an id.

A name such as "Q" or "K[x]" is not an identity: the description, including the
base structure, generators and representation options, is.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Generic, TypeVar, cast

from cas.algebra.protocols import (
    Derivation,
    DescribedRing,
    Euclidean,
    Field,
    GeneratorRing,
    IntegerEmbedding,
    Ordered,
    Ring,
)
from cas.foundation.ids import IdIssuer, ParentId, SymbolId

E = TypeVar("E")


@dataclass(frozen=True, slots=True)
class ParentSpec:
    """A complete description of the admitted structure fragment.

    `options` records representation choices as `(name, value)` pairs. The
    constructor normalises them into name order, so two equal descriptions are
    always structurally equal regardless of how the caller built the pairs.

    Quotient relations, required structure proofs and algebraic root embeddings
    are not represented yet: no structure in this tree can be built with them,
    so a description cannot claim them.
    """

    kind: str
    base: ParentSpec | None = None
    generators: tuple[SymbolId, ...] = ()
    options: tuple[tuple[str, str], ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.kind, str) or not self.kind:
            raise ValueError("a parent description needs a kind")
        if self.base is not None and not isinstance(self.base, ParentSpec):
            raise TypeError("a parent description base must be a ParentSpec")
        generators = tuple(self.generators)
        if any(
            not isinstance(generator, int) or isinstance(generator, bool)
            for generator in generators
        ):
            raise TypeError("parent generators must be SymbolIds")
        if generators != self.generators:
            object.__setattr__(self, "generators", generators)
        options: list[tuple[str, str]] = []
        for option in self.options:
            if not isinstance(option, tuple) or len(option) != 2:
                raise TypeError(
                    "a parent option must be a (name, value) pair"
                )
            name, value = option
            if not isinstance(name, str) or not isinstance(value, str):
                raise TypeError("a parent option name and value must be strings")
            options.append((name, value))
        canonical = tuple(sorted(options))
        if len({name for name, _ in canonical}) != len(canonical):
            raise ValueError("parent option names must be unique")
        if canonical != self.options:
            object.__setattr__(self, "options", canonical)


@dataclass(frozen=True, slots=True, eq=False)
class Parent(Generic[E]):
    """A structure instance: stable id, description and arithmetic.

    `eq=False` is deliberate: a parent is a runtime object whose identity is its
    `ParentId`, not a value to be compared by the identity of its ring object.
    """

    id: ParentId
    spec: ParentSpec
    ring: Ring[E]

    @property
    def is_field(self) -> bool:
        return isinstance(self.ring, Field)

    @property
    def is_euclidean(self) -> bool:
        return isinstance(self.ring, Euclidean)

    @property
    def is_ordered(self) -> bool:
        return isinstance(self.ring, Ordered)

    @property
    def has_derivation(self) -> bool:
        return isinstance(self.ring, Derivation)

    @property
    def embeds_integers(self) -> bool:
        return isinstance(self.ring, IntegerEmbedding)

    def contains(self, value: object) -> bool:
        return self.ring.contains(value)

    def value(self, representation: E) -> AlgebraValue[E]:
        return AlgebraValue(self, representation)


@dataclass(frozen=True, slots=True)
class AlgebraValue(Generic[E]):
    """A representation paired with the parent that accepts it."""

    parent: Parent[E]
    representation: E

    def __post_init__(self) -> None:
        if not self.parent.contains(self.representation):
            raise ValueError(
                "the representation is not a member of the parent"
            )


class ParentRegistry:
    """Issues one stable id per complete description."""

    __slots__ = ("_ids", "_parents", "_issuer")

    def __init__(self) -> None:
        self._ids: dict[ParentSpec, ParentId] = {}
        # One declared erasure boundary: the registry stores parents of mixed
        # element types and hands each caller back its own type.
        self._parents: dict[ParentId, Parent[Any]] = {}
        self._issuer = IdIssuer()

    def intern(self, spec: ParentSpec, ring: Ring[E]) -> Parent[E]:
        """Return the parent for `spec`, creating it once.

        Registering the same description with a different structure is an
        assembly error, not a silent replacement.
        """
        existing = self._ids.get(spec)
        if existing is not None:
            known = self._parents[existing]
            if known.ring is not ring:
                raise ValueError(
                    f"parent {spec.kind!r} was registered with a different structure"
                )
            return cast(Parent[E], known)
        if not isinstance(ring, DescribedRing):
            raise ValueError(
                "a parent structure must describe its kind and representation"
            )
        if spec.kind != ring.parent_kind:
            raise ValueError(
                f"parent kind {spec.kind!r} does not match the structure "
                f"kind {ring.parent_kind!r}"
            )
        if (spec.base is not None) is not ring.parent_requires_base:
            raise ValueError(
                "the parent description disagrees with the structure about "
                "whether it has a base"
            )
        if isinstance(ring, GeneratorRing):
            if spec.generators != tuple(ring.generators):
                raise ValueError(
                    "the parent description's generators do not match the "
                    "structure"
                )
        elif spec.generators:
            raise ValueError(
                "a structure without declared generators cannot describe "
                "generators"
            )
        described = dict(ring.parent_options)
        declared = dict(spec.options)
        missing = sorted(set(described) - set(declared))
        if missing:
            raise ValueError(
                "the parent description omits representation options: "
                + ", ".join(missing)
            )
        unknown = sorted(set(declared) - set(described))
        if unknown:
            raise ValueError(
                "the parent description declares unknown representation "
                "options: " + ", ".join(unknown)
            )
        for name, value in described.items():
            if declared[name] != value:
                raise ValueError(
                    f"parent option {name!r} does not match the structure"
                )
        identifier = ParentId(self._issuer.issue())
        created = Parent(identifier, spec, ring)
        self._ids[spec] = identifier
        self._parents[identifier] = created
        return created

    def get(self, identifier: ParentId) -> Parent[Any]:
        return self._parents[identifier]

    @property
    def count(self) -> int:
        """How many distinct descriptions have been admitted."""
        return self._issuer.issued


__all__ = ["AlgebraValue", "Parent", "ParentRegistry", "ParentSpec"]
