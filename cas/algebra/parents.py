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
    IntegerEmbedding,
    Ordered,
    Ring,
)
from cas.foundation.ids import IdIssuer, ParentId, SymbolId

E = TypeVar("E")


@dataclass(frozen=True, slots=True)
class ParentSpec:
    """A complete description of a structure.

    `options` records representation choices as `(name, value)` pairs. The
    constructor normalises them into name order, so two equal descriptions are
    always structurally equal regardless of how the caller built the pairs.
    """

    kind: str
    base: ParentSpec | None = None
    generators: tuple[SymbolId, ...] = ()
    options: tuple[tuple[str, str], ...] = ()

    def __post_init__(self) -> None:
        if not self.kind:
            raise ValueError("a parent description needs a kind")
        canonical = tuple(sorted(self.options))
        names = [name for name, _ in canonical]
        if len(set(names)) != len(names):
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
        if isinstance(ring, DescribedRing):
            actual = dict(ring.parent_options)
            for name, value in spec.options:
                if actual.get(name) != value:
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
