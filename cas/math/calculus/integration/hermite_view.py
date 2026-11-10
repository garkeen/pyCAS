"""Request-local view for rational Hermite reduction."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.algebra.parents import Parent
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.foundation.ids import SymbolId
from cas.semantics.bridge import RationalFunctionBridge
from cas.semantics.request import AlgebraRequest

E = TypeVar("E")


@dataclass(frozen=True, slots=True, eq=False)
class HermiteView(Generic[E]):
    request: AlgebraRequest
    field: RationalFunctionField[E]
    parent: Parent[RationalFunction[E]]
    bridge: RationalFunctionBridge[E]
    checker_id: str

    def __post_init__(self) -> None:
        if self.parent.ring is not self.field:
            raise ValueError("the Hermite parent does not own the field")
        if self.bridge.field is not self.field:
            raise ValueError("the Hermite bridge does not own the field")
        if self.bridge.parent is not self.parent:
            raise ValueError("the Hermite bridge does not own the parent")

    @property
    def target(self) -> SymbolId:
        return self.request.target


__all__ = ["HermiteView"]
