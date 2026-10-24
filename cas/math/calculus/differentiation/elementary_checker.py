"""Checker for `HasDerivative` on the declared elementary fragment.

The checker never generates a candidate. It validates the certificate against
the claim, asks the independent verifier for the expected derivative, and
accepts only an exact structural match. A different term is left unverified:
without a decision procedure for elementary equality, structural difference is
not a mathematical refutation.
"""

from __future__ import annotations

from collections.abc import Callable

from cas.foundation.ids import SymbolId
from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    InvalidEvidence,
    Unverified,
    Verified,
)
from cas.language.decisions import Reason
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.elementary_verify import (
    verify_elementary_derivative,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
    parse_has_derivative,
)
from cas.math.elementary.declarations import ElementaryLibrary
from cas.semantics.conditions import equivalent
from cas.semantics.services import DerivationUnsupported, Derived
from cas.syntax import term as T


class ElementaryDerivativeChecker:
    """One registered checker for the declared elementary library."""

    version = "1"

    def __init__(
        self,
        library: ElementaryLibrary,
        signature: LanguageSignature,
        vocabulary: DerivativeVocabulary,
        variable: SymbolId,
        name_of: Callable[[SymbolId], str],
        *,
        identifier: str = "calculus.derivative.elementary",
    ) -> None:
        if not identifier:
            raise ValueError("a checker needs an identifier")
        self.id = identifier
        self._library = library
        self._signature = signature
        self._vocabulary = vocabulary
        self._variable = variable
        self._name_of = name_of

    def check(self, request: CheckRequest) -> CheckOutcome:
        for conclusion in request.conclusions:
            claim = parse_has_derivative(self._vocabulary, conclusion.term)
            if claim is None:
                return InvalidEvidence(
                    "the conclusion is not a HasDerivative specification"
                )
            certificate = request.certificate
            if not isinstance(certificate, DerivativeCertificate):
                return InvalidEvidence(
                    "a derivative certificate is required"
                )
            if certificate.region != claim.region:
                return InvalidEvidence(
                    "the certificate does not match the specification"
                )
            if (
                certificate.source != claim.source
                or certificate.variable != claim.variable.symbol_id
                or certificate.candidate != claim.candidate
            ):
                return InvalidEvidence(
                    "the certificate does not match the specification"
                )
            if claim.variable.symbol_id != self._variable:
                return Unverified(
                    Reason.FRAGMENT,
                    "the claim is not stated in this fragment's variable",
                )
            expected = verify_elementary_derivative(
                claim.source,
                self._library,
                self._signature,
                self._variable,
                self._name_of,
            )
            if isinstance(expected, DerivationUnsupported):
                return Unverified(expected.reason, expected.detail)
            if not isinstance(expected, Derived):
                return Unverified(
                    Reason.FRAGMENT,
                    "the verifier could not produce a derivative",
                )
            expected_region = (
                T.TRUE if expected.condition is None else expected.condition
            )
            if claim.region != expected_region and equivalent(
                claim.region, expected_region, self._signature
            ) is not True:
                return Unverified(
                    Reason.FRAGMENT,
                    "the claimed region is not the verified "
                    "differentiability region",
                )
            if expected.term != claim.candidate:
                return Unverified(
                    Reason.FRAGMENT,
                    "the candidate is not the verified derivative term",
                )
        return Verified(tuple(request.conclusions))


__all__ = ["ElementaryDerivativeChecker"]
