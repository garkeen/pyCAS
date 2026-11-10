"""Trust records shared by the kernel and the checkers it admits.

A `BasisRef` names an admitted external basis; a `CertificateSchema` names the
certificate type a checker interprets and bounds its structural size. These are
not proofs. They record what the assembly admitted, so an inference can be
audited against the world and the dependency it used.

The budget walker is deliberately generic: certificates are immutable data
(literals, tuples, mappings and frozen dataclasses). An unmeasurable or cyclic
value is rejected rather than silently treated as small.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, fields, is_dataclass
from enum import Enum, StrEnum
from fractions import Fraction
from types import MappingProxyType

from cas.foundation.ids import WorldId

_LEAVES = (type(None), bool, int, float, str, bytes, Fraction)


class BasisKind(StrEnum):
    """What kind of trusted dependency a basis reference names."""

    STANDARD_LIBRARY = "standard_library"
    DECLARATION_FILE = "declaration_file"


@dataclass(frozen=True, slots=True)
class BasisRef:
    """An admitted trusted basis: kind, version, scope and content digest.

    A basis reference is created at assembly time from data the runtime admits
    explicitly. It is not a proof; it records which trusted dependency a checker
    used, so an inference can be audited against the world it was made in.
    """

    name: str
    kind: BasisKind
    version: str
    digest: str
    world: WorldId

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a basis reference needs a name")
        if not isinstance(self.kind, BasisKind):
            raise TypeError("a basis reference needs a BasisKind")
        if not self.version:
            raise ValueError("a basis reference needs a version")
        if not self.digest:
            raise ValueError("a basis reference needs a content digest")


@dataclass(frozen=True, slots=True)
class AxiomRef:
    """One admitted trusted dependency recorded for a verification context.

    The kernel derives it from the checker's admitted `BasisRef` so a receipt
    can name the trust it used without copying the registry lookup or the
    basis kind into the context.  It is not a proof: it records the admitted
    name, version, content digest and meaning world.
    """

    name: str
    version: str
    digest: str
    world: WorldId

    def __post_init__(self) -> None:
        for label, value in (
            ("name", self.name),
            ("version", self.version),
            ("digest", self.digest),
        ):
            if not isinstance(value, str) or not value:
                raise ValueError(f"an axiom reference needs a {label}")
        if isinstance(self.world, bool) or not isinstance(self.world, int):
            raise TypeError("an axiom reference needs a WorldId")

    @classmethod
    def from_basis(cls, basis: BasisRef) -> AxiomRef:
        """The context-visible axiom record of one admitted basis."""
        if not isinstance(basis, BasisRef):
            raise TypeError(
                "an axiom reference can only be derived from a BasisRef"
            )
        return cls(basis.name, basis.version, basis.digest, basis.world)


class BasisRegistry:
    """The bases one assembly admitted, keyed by name and kind.

    Registration is explicit and frozen at assembly time. A checker spec may
    name any `BasisRef`, but `validate_commit` only accepts it when this table
    holds the same name, kind, version, digest and world. Comparing the whole
    reference prevents a caller from reusing an admitted name with another
    version or content.
    """

    __slots__ = ("_bases",)

    def __init__(self, bases: tuple[BasisRef, ...] = ()) -> None:
        if not isinstance(bases, tuple):
            raise TypeError("a basis registry is built from a tuple of BasisRef")
        table: dict[tuple[str, BasisKind], BasisRef] = {}
        for basis in bases:
            if not isinstance(basis, BasisRef):
                raise TypeError(
                    "a basis registry holds BasisRef values, "
                    f"got {type(basis).__name__}"
                )
            key = (basis.name, basis.kind)
            if key in table:
                raise ValueError(
                    f"basis {basis.name!r} of kind {basis.kind} "
                    "is registered twice"
                )
            table[key] = basis
        self._bases = MappingProxyType(table)

    def get(self, name: str, kind: BasisKind) -> BasisRef | None:
        return self._bases.get((name, kind))

    def verify(self, basis: BasisRef) -> bool:
        """Whether this exact reference was admitted, field for field."""
        if not isinstance(basis, BasisRef):
            raise TypeError(
                "only a BasisRef can be verified against a basis registry"
            )
        known = self.get(basis.name, basis.kind)
        if known is None:
            return False
        return (
            known.name == basis.name
            and known.kind == basis.kind
            and known.version == basis.version
            and known.digest == basis.digest
            and known.world == basis.world
        )

    def __len__(self) -> int:
        return len(self._bases)


@dataclass(frozen=True, slots=True)
class CertificateSchema:
    """The certificate format a checker is admitted to interpret."""

    name: str
    version: str
    certificate_type: type
    max_nodes: int = 4096
    max_depth: int = 64

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a certificate schema needs a name")
        if not self.version:
            raise ValueError("a certificate schema needs a version")
        if not isinstance(self.certificate_type, type):
            raise TypeError("a certificate schema needs a certificate type")
        if self.max_nodes <= 0:
            raise ValueError("a certificate schema needs a positive node budget")
        if self.max_depth <= 0:
            raise ValueError("a certificate schema needs a positive depth budget")

    def accepts(self, certificate: object) -> bool:
        return isinstance(certificate, self.certificate_type)

    def within_budget(self, certificate: object) -> bool:
        """Whether the certificate is measurable and within this schema."""
        return (
            certificate_limits(
                certificate,
                max_nodes=self.max_nodes,
                max_depth=self.max_depth,
            )
            is not None
        )


def _slot_names(value_type: type) -> tuple[str, ...]:
    """Declared slot names, so immutable value objects are measurable."""
    names: list[str] = []
    for base in value_type.__mro__:
        declared = base.__dict__.get("__slots__", ())
        if isinstance(declared, str):
            declared = (declared,)
        for name in declared:
            if name not in names:
                names.append(name)
    return tuple(names)


def certificate_limits(
    value: object,
    *,
    max_nodes: int,
    max_depth: int,
) -> tuple[int, int] | None:
    """Return `(nodes, depth)`, or `None` when the budget is exceeded.

    Unknown objects are unmeasurable and therefore refused; a schema may only
    admit certificates built from exact data and frozen dataclasses.
    """

    def measure(current: object, path: frozenset[int]) -> tuple[int, int] | None:
        if isinstance(current, _LEAVES):
            size = 1
            if isinstance(current, (str, bytes)):
                size = max(1, len(current))
            return (size, 1) if size <= max_nodes else None
        if isinstance(current, Enum):
            return measure(current.value, path)
        if isinstance(current, Mapping):
            identity = id(current)
            if identity in path:
                return None
            child_path = path | {identity}
            nodes = 1
            depth = 1
            for key, value in current.items():
                for part in (key, value):
                    result = measure(part, child_path)
                    if result is None:
                        return None
                    nodes += result[0]
                    depth = max(depth, result[1] + 1)
                    if nodes > max_nodes or depth > max_depth:
                        return None
            return nodes, depth
        if isinstance(current, (tuple, list, set, frozenset)):
            identity = id(current)
            if identity in path:
                return None
            child_path = path | {identity}
            nodes = 1
            depth = 1
            for element in current:
                result = measure(element, child_path)
                if result is None:
                    return None
                nodes += result[0]
                depth = max(depth, result[1] + 1)
                if nodes > max_nodes or depth > max_depth:
                    return None
            return nodes, depth
        if is_dataclass(current) and not isinstance(current, type):
            identity = id(current)
            if identity in path:
                return None
            child_path = path | {identity}
            nodes = 1
            depth = 1
            for field in fields(current):
                if field.name.startswith("_"):
                    continue
                field_value: object = getattr(current, field.name)
                result = measure(field_value, child_path)
                if result is None:
                    return None
                nodes += result[0]
                depth = max(depth, result[1] + 1)
                if nodes > max_nodes or depth > max_depth:
                    return None
            return nodes, depth
        slotted = _slot_names(type(current))
        if slotted:
            identity = id(current)
            if identity in path:
                return None
            child_path = path | {identity}
            nodes = 1
            depth = 1
            for name in slotted:
                if name.startswith("_"):
                    continue
                try:
                    value = getattr(current, name)
                except AttributeError:
                    continue
                result = measure(value, child_path)
                if result is None:
                    return None
                nodes += result[0]
                depth = max(depth, result[1] + 1)
                if nodes > max_nodes or depth > max_depth:
                    return None
            return nodes, depth
        return None

    return measure(value, frozenset())


__all__ = [
    "AxiomRef",
    "BasisKind",
    "BasisRef",
    "BasisRegistry",
    "CertificateSchema",
    "certificate_limits",
]
