"""Candidate generation and certificate construction for derivative operations.

These are mathematical services, not runtime assembly: they know a bridge and a
differential structure or an elementary differentiator, and they never write to
the kernel ledger.

The polynomial services consume the typed source through the bridge's
`to_view`/`render` pair.  A refused view and a refused rendering are both
honest fragment refusals with the missing capability; they are not mathematical
failures.  A built view fixes the parent element the derivation acts on, and
the result is rendered back through the same symbol bindings.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial
from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.typing import TypedExpr
from cas.math.calculus.differentiation.certificate import (
    Derivation,
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.elementary import (
    ElementaryDifferentiator,
)
from cas.semantics.bridge import (
    PolynomialBridge,
    RenderRefused,
    ViewRefused,
)
from cas.semantics.differential import DifferentialStructure
from cas.semantics.request import AlgebraRequest
from cas.semantics.services import (
    DerivationInvalid,
    DerivationOutcome,
    DerivationUnsupported,
    Derived,
)
from cas.syntax import term as T

E = TypeVar("E")


def _refused(refusal: ViewRefused) -> DerivationUnsupported:
    """Carry a view refusal into the service's closed outcome.

    The polynomial services declare one stable fragment message; the bridge's
    specific `missing` capability and any open conditions are preserved, so the
    refusal still says what is needed.
    """
    detail = (
        "the source is outside the polynomial fragment"
        if refusal.reason is Reason.FRAGMENT
        else refusal.detail
    )
    return DerivationUnsupported(
        refusal.reason,
        detail,
        refusal.missing,
        refusal.conditions,
    )


@dataclass(frozen=True, slots=True)
class PolynomialDerivativeService(Generic[E]):
    """Candidate generation through a polynomial bridge and derivation."""

    bridge: PolynomialBridge[E]
    differential: DifferentialStructure[Polynomial[E]]
    checker_id: str
    specification_kind: str

    def supports(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> DerivationUnsupported | None:
        outcome = self.bridge.to_view(source, request)
        if isinstance(outcome, ViewRefused):
            return _refused(outcome)
        return None

    def candidate(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> DerivationOutcome:
        outcome = self.bridge.to_view(source, request)
        if isinstance(outcome, ViewRefused):
            return _refused(outcome)
        view = outcome.view
        try:
            wrapped = self.differential.parent.value(view.value)
        except (TypeError, ValueError) as error:
            return DerivationInvalid(
                "the algebra view value is not in the differential parent: "
                f"{error}"
            )
        rendered = self.bridge.render(
            view, self.differential.deriv(wrapped.representation)
        )
        if isinstance(rendered, RenderRefused):
            # The view already admitted the source, so this refusal concerns
            # the result language, not an invalid derivation.  Reporting it as
            # unsupported keeps the missing capability visible instead of
            # pretending the mathematics failed.
            return DerivationUnsupported(
                rendered.reason, rendered.detail, rendered.missing
            )
        return Derived(rendered.term)

    def certificate(
        self,
        region: T.Term,
        source: T.Term,
        variable: SymbolId,
        derivation: Derived,
    ) -> object:
        return DerivativeCertificate(
            region, source, variable, derivation.term
        )


@dataclass(frozen=True, slots=True)
class ElementaryDerivativeService:
    """Candidate generation through the declared elementary differentiator."""

    differentiator: ElementaryDifferentiator
    checker_id: str
    specification_kind: str

    def supports(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> DerivationUnsupported | None:
        del request
        return self.differentiator.supports(source.term)

    def candidate(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> DerivationOutcome:
        del request
        return self.differentiator.derive(source.term)

    def certificate(
        self,
        region: T.Term,
        source: T.Term,
        variable: SymbolId,
        derivation: Derived,
    ) -> object:
        evidence = derivation.evidence
        if not isinstance(evidence, Derivation):
            raise TypeError(
                "the elementary candidate has no rule-instance derivation"
            )
        return DerivativeCertificate(
            region, source, variable, derivation.term, evidence
        )


__all__ = [
    "ElementaryDerivativeService",
    "PolynomialDerivativeService",
]
