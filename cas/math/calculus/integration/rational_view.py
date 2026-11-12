"""Request-local view for rational-function integration operations.

Hermite reduction and rational-logarithmic integration both consume one fixed
``Q(x)`` representation: the request that selected it, the field, the parent
that contains the field's elements, the bridge that converts terms to field
elements and back, and the id of the independent checker admitted for that
view.  The view carries no mathematical result and runs no algorithm.
"""

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
class RationalFunctionView(Generic[E]):
    request: AlgebraRequest
    field: RationalFunctionField[E]
    parent: Parent[RationalFunction[E]]
    bridge: RationalFunctionBridge[E]
    checker_id: str

    def __post_init__(self) -> None:
        if self.parent.ring is not self.field:
            raise ValueError(
                "the rational-function parent does not own the field"
            )
        if self.bridge.field is not self.field:
            raise ValueError(
                "the rational-function bridge does not own the field"
            )
        if self.bridge.parent is not self.parent:
            raise ValueError(
                "the rational-function bridge does not own the parent"
            )

    @property
    def target(self) -> SymbolId:
        return self.request.target


__all__ = ["RationalFunctionView"]
