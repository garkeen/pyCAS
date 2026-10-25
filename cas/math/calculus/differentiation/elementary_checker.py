"""Checker for `HasDerivative` on the declared elementary fragment.

The checker never generates a candidate. It requires a `Derivation` tree in the
certificate, rebuilds every local rule instance from its children and the
declared laws, and accepts only a tree whose claimed result and region match the
specification. A structural mismatch is left unverified: without a decision
procedure for elementary equality, it is not a mathematical refutation.
"""

from __future__ import annotations

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
    Derivation,
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.derivation import (
    RuleContext,
    verify_derivation,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
    certificate_matches_claim,
    parse_has_derivative,
)
from cas.math.elementary.declarations import ElementaryLibrary
from cas.semantics.conditions import equivalent
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
            if not certificate_matches_claim(certificate, claim):
                return InvalidEvidence(
                    "the certificate does not match the specification"
                )
            if claim.variable.symbol_id != self._variable:
                return Unverified(
                    Reason.FRAGMENT,
                    "the claim is not stated in this fragment's variable",
                )
            derivation = certificate.derivation
            if derivation is None:
                return InvalidEvidence(
                    "the elementary checker needs a rule-instance derivation"
                )
            if not isinstance(derivation, Derivation):
                return InvalidEvidence(
                    "the certificate derivation has the wrong type"
                )
            if (
                derivation.source != claim.source
                or derivation.result != claim.candidate
            ):
                return Unverified(
                    Reason.FRAGMENT,
                    "the derivation does not derive the claimed "
                    "source and candidate",
                )
            problem = verify_derivation(
                derivation,
                RuleContext(
                    self._library, self._signature, self._variable
                ),
            )
            if problem is not None:
                return Unverified(Reason.FRAGMENT, problem)
            expected_region = (
                T.TRUE
                if derivation.condition is None
                else derivation.condition
            )
            if claim.region != expected_region and equivalent(
                claim.region, expected_region, self._signature
            ) is not True:
                return Unverified(
                    Reason.FRAGMENT,
                    "the claimed region is not the verified "
                    "differentiability region",
                )
        return Verified(tuple(request.conclusions))


__all__ = ["ElementaryDerivativeChecker"]
