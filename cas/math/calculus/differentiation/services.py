"""Candidate generation and certificate construction for derivative operations.

These are mathematical services, not runtime assembly: they know a bridge and a
differential structure or an elementary differentiator, and they never write to
the kernel ledger.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial
from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.elementary import (
    ElementaryDifferentiator,
)
from cas.semantics.bridge import PolynomialBridge
from cas.semantics.differential import DifferentialStructure
from cas.semantics.services import (
    DerivationInvalid,
    DerivationOutcome,
    DerivationUnsupported,
    Derived,
)
from cas.syntax import term as T

E = TypeVar("E")


@dataclass(frozen=True, slots=True)
class PolynomialDerivativeService(Generic[E]):
    """Candidate generation through a polynomial bridge and derivation."""

    bridge: PolynomialBridge[E]
    differential: DifferentialStructure[Polynomial[E]]
    checker_id: str
    specification_kind: str

    def candidate(self, term: T.Term) -> DerivationOutcome:
        value = self.bridge.to_value(term)
        if value is None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the source is outside the polynomial fragment",
            )
        wrapped = self.differential.parent.value(value)
        rendered = self.bridge.to_term(
            self.differential.deriv(wrapped.representation)
        )
        if rendered is None:
            return DerivationInvalid(
                "the derivative cannot be rendered in this language"
            )
        return Derived(rendered)

    def certificate(
        self,
        region: T.Term,
        source: T.Term,
        variable: SymbolId,
        candidate: T.Term,
    ) -> object:
        return DerivativeCertificate(region, source, variable, candidate)


@dataclass(frozen=True, slots=True)
class ElementaryDerivativeService:
    """Candidate generation through the declared elementary differentiator."""

    differentiator: ElementaryDifferentiator
    checker_id: str
    specification_kind: str

    def candidate(self, term: T.Term) -> DerivationOutcome:
        return self.differentiator.derive(term)

    def certificate(
        self,
        region: T.Term,
        source: T.Term,
        variable: SymbolId,
        candidate: T.Term,
    ) -> object:
        return DerivativeCertificate(region, source, variable, candidate)


__all__ = [
    "ElementaryDerivativeService",
    "PolynomialDerivativeService",
]
