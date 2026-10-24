"""Independent checker for `HasDerivative` on the polynomial fragment.

The checker never generates a derivative. It parses the claim, requires a
certificate that names exactly the same instance, converts both sides through
the explicit bridge, and delegates the mathematics to `verify_derivative` — a
second implementation of the derivative rule that does not call the ring's own
`derivative`.

Outside the fragment it returns `Unverified`, never a refutation.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial, PolynomialRing
from cas.foundation.ids import SymbolId
from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Unverified,
    Verified,
)
from cas.language.decisions import Reason
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
    parse_has_derivative,
)
from cas.math.calculus.differentiation.verify import verify_derivative
from cas.semantics.bridge import to_polynomial
from cas.syntax import term as T

E = TypeVar("E")


@dataclass(frozen=True, slots=True)
class DerivativeCertificate:
    """The instance the caller asks to be verified."""

    region: T.Term
    source: T.Term
    variable: SymbolId
    candidate: T.Term


class DerivativeChecker(Generic[E]):
    """A checker for one univariate polynomial ring and one predicate symbol."""

    id = "calculus.derivative"
    version = "1"

    def __init__(
        self,
        ring: PolynomialRing[E],
        signature: LanguageSignature,
        vocabulary: DerivativeVocabulary,
        to_value: Callable[[T.Term], Polynomial[E] | None] | None = None,
        *,
        identifier: str = "calculus.derivative",
    ) -> None:
        if len(ring.generators) != 1:
            raise TypeError("the derivative fragment is univariate")
        if not identifier:
            raise ValueError("a checker needs an identifier")
        self.id = identifier
        self._ring = ring
        self._signature = signature
        self._vocabulary = vocabulary
        self._to_value = to_value

    def _convert(self, term: T.Term) -> Polynomial[E] | None:
        if self._to_value is not None:
            return self._to_value(term)
        return to_polynomial(self._ring, term, self._signature)

    def check(self, request: CheckRequest) -> CheckOutcome:
        for conclusion in request.conclusions:
            claim = parse_has_derivative(self._vocabulary, conclusion.term)
            if claim is None:
                return InvalidEvidence(
                    "the conclusion is not a HasDerivative specification"
                )
            certificate = request.certificate
            if not isinstance(certificate, DerivativeCertificate):
                return InvalidEvidence("a derivative certificate is required")
            if (
                certificate.region != claim.region
                or certificate.source != claim.source
                or certificate.variable != claim.variable.symbol_id
                or certificate.candidate != claim.candidate
            ):
                return InvalidEvidence(
                    "the certificate does not match the specification"
                )
            if claim.region != T.TRUE:
                return Unverified(
                    Reason.GUARDED,
                    "only the whole-domain region is verified",
                )
            if claim.variable.symbol_id != self._ring.generators[0]:
                return Unverified(
                    Reason.FRAGMENT,
                    "the claim is not stated in this ring's variable",
                )
            source = self._convert(claim.source)
            candidate = self._convert(claim.candidate)
            if source is None or candidate is None:
                return Unverified(
                    Reason.FRAGMENT,
                    "the claim is outside the polynomial fragment",
                )
            if not verify_derivative(self._ring, source, candidate, 0):
                return Refuted(
                    conclusion,
                    (claim.source, claim.candidate),
                    "the candidate is not the derivative of the source",
                )
        return Verified(tuple(request.conclusions))


__all__ = ["DerivativeCertificate", "DerivativeChecker"]
