"""Request-local views for polynomial integration."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.algebra.polynomial import PolynomialRing
from cas.foundation.ids import SymbolId
from cas.semantics.bridge import PolynomialBridge
from cas.semantics.request import AlgebraRequest
from cas.semantics.services import DerivativeService

E = TypeVar("E")


@dataclass(frozen=True, slots=True, eq=False)
class IntegrationView(Generic[E]):
    """One target role with the structures needed to integrate it."""

    request: AlgebraRequest
    ring: PolynomialRing[E]
    bridge: PolynomialBridge[E]
    service: DerivativeService
    checker_id: str

    @property
    def target(self) -> SymbolId:
        return self.request.target


__all__ = ["IntegrationView"]
