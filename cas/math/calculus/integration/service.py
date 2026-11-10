"""Antiderivative candidate generation for the polynomial fragment.

The service consumes the typed source through the bridge's `to_view`/`render`
pair.  A refused view and a refused rendering are honest fragment refusals that
carry the missing capability; a mathematically undefined antiderivative (for
example over a coefficient structure without a characteristic-zero fraction
field) is also a fragment refusal, not a false claim.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.typing import TypedExpr
from cas.math.calculus.differentiation.certificate import DerivativeCertificate
from cas.semantics.bridge import (
    PolynomialBridge,
    RenderRefused,
    ViewRefused,
)
from cas.semantics.request import AlgebraRequest
from cas.semantics.services import (
    DerivationOutcome,
    DerivationUnsupported,
    Derived,
)
from cas.syntax import term as T

E = TypeVar("E")


def _refused(refusal: ViewRefused) -> DerivationUnsupported:
    """Carry a view refusal into the service's closed outcome.

    The polynomial fragment has one stable refusal message; the specific
    missing capability and open conditions from the bridge are preserved.
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
class PolynomialAntiderivativeService(Generic[E]):
    """A polynomial antiderivative with zero constant of integration.

    The service only generates a candidate.  The registered derivative checker
    verifies `D(candidate) == source`; this service never issues a judgment.
    """

    bridge: PolynomialBridge[E]
    checker_id: str
    specification_kind: str = "HasDerivative"

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
            antiderivative = view.value.owner.antiderivative(view.value, 0)
        except (TypeError, ValueError, ZeroDivisionError) as error:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                str(error),
                frozenset({"polynomial_antiderivative"}),
            )
        rendered = self.bridge.render(view, antiderivative)
        if isinstance(rendered, RenderRefused):
            # The view already admitted the source; the antiderivative exists
            # in the parent but the result language cannot express it.  That is
            # a representation gap, not an invalid derivation.
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


__all__ = ["PolynomialAntiderivativeService"]
