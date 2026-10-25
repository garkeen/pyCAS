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
from enum import StrEnum
from fractions import Fraction

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
    "BasisKind",
    "BasisRef",
    "CertificateSchema",
    "certificate_limits",
]
