"""Independent checker for `HasPolynomialGCD` over a univariate field.

The checker proves the candidate is a common divisor by exact division and
proves maximality from the Bezout identity `s*f + t*g = d`.  It never calls the
ring's `gcd` or `xgcd`; those are the search algorithms under test.

Every claimed term is independently elaborated and admitted through the
pre-assembled algebra bridge.  A typing failure or a refused view is
`Unverified`, never a refutation.
"""

from __future__ import annotations

from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.foundation.ids import FrameId
from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Unverified,
    Verified,
    context_algebra_mismatch,
    problem_mismatch,
)
from cas.language.decisions import Reason
from cas.language.problems import Exactness, Role
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.algebra.gcd_specification import (
    GcdCertificate,
    GcdVocabulary,
    certificate_matches_claim,
    parse_gcd,
)
from cas.semantics.bridge import (
    AlgebraView,
    PolynomialBridge,
    ViewRefused,
    typed_view,
)
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

E = TypeVar("E")


class PolynomialGcdChecker(Generic[E]):
    """A checker for one univariate polynomial ring over a field."""

    id = "algebra.polynomial_gcd"
    version = "1"

    def __init__(
        self,
        ring: UnivariatePolynomialRing[E],
        signature: LanguageSignature,
        vocabulary: GcdVocabulary,
        bridge: PolynomialBridge[E],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "algebra.polynomial_gcd",
    ) -> None:
        if not identifier:
            raise ValueError("a checker needs an identifier")
        if not ring.contains(bridge.ring.zero()):
            raise ValueError(
                "the checker ring does not own the bridge's elements"
            )
        self.id = identifier
        self._ring = ring
        self._signature = signature
        self._vocabulary = vocabulary
        self._bridge = bridge
        self._frames = frames
        self._request = request

    def _view(
        self, term: T.Term, frame: FrameId
    ) -> AlgebraView[Polynomial[E]] | Unverified:
        """Independently elaborate and admit one claimed term."""
        outcome = typed_view(
            self._bridge,
            term,
            self._frames,
            frame,
            self._signature,
            self._request,
        )
        if isinstance(outcome, ViewRefused):
            return Unverified(
                reason=outcome.reason,
                detail=outcome.detail,
                missing=outcome.missing,
                conditions=outcome.conditions,
            )
        if not isinstance(outcome, AlgebraView):
            return Unverified(
                reason=Reason.FRAGMENT,
                detail=outcome.detail,
                missing=outcome.missing,
            )
        return outcome

    def check(self, request: CheckRequest) -> CheckOutcome:
        algebra_mismatch = context_algebra_mismatch(
            request.context, self._request
        )
        if algebra_mismatch is not None:
            return InvalidEvidence(algebra_mismatch)
        if len(request.conclusions) != 1:
            return InvalidEvidence(
                "a gcd certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        frame = conclusion.meaning.frame
        claim = parse_gcd(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a HasPolynomialGCD specification"
            )
        candidate_term = request.candidate
        if candidate_term is None:
            return InvalidEvidence("a gcd candidate is required")
        if request.candidate_role is not CandidateRole.RESULT:
            return InvalidEvidence(
                "a gcd candidate needs the result candidate role"
            )
        if candidate_term != claim.candidate:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(certificate, GcdCertificate):
            return InvalidEvidence("a gcd certificate is required")
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        mismatch = problem_mismatch(
            request,
            operations=("polynomial_gcd",),
            target=claim.variable.symbol_id,
            inputs=(claim.left, claim.right),
            roles=self._request.roles,
            interpretation_requirement=(
                self._request.interpretation_requirement
            ),
            exactness=Exactness.EXACT,
            coefficient_domain=self._request.coefficient_domain,
            value_domain=self._request.value_domain,
        )
        if mismatch is not None:
            return InvalidEvidence(mismatch)
        left_view = self._view(claim.left, frame)
        if isinstance(left_view, Unverified):
            return left_view
        if left_view.source.term != claim.left:
            return InvalidEvidence(
                "the elaborated left input does not match the claim"
            )
        if left_view.symbol_for(Role.TARGET, 0) != claim.variable.symbol_id:
            return Unverified(
                Reason.FRAGMENT,
                "the claim is not stated in this view's target variable",
            )
        right_view = self._view(claim.right, frame)
        if isinstance(right_view, Unverified):
            return right_view
        if right_view.source.term != claim.right:
            return InvalidEvidence(
                "the elaborated right input does not match the claim"
            )
        candidate_view = self._view(claim.candidate, frame)
        if isinstance(candidate_view, Unverified):
            return candidate_view
        if candidate_view.source.term != claim.candidate:
            return InvalidEvidence(
                "the elaborated candidate does not match the claim"
            )
        left_coefficient_view = self._view(
            certificate.left_coefficient, frame
        )
        if isinstance(left_coefficient_view, Unverified):
            return left_coefficient_view
        if left_coefficient_view.source.term != certificate.left_coefficient:
            return InvalidEvidence(
                "the elaborated left coefficient does not match the "
                "certificate"
            )
        right_coefficient_view = self._view(
            certificate.right_coefficient, frame
        )
        if isinstance(right_coefficient_view, Unverified):
            return right_coefficient_view
        if right_coefficient_view.source.term != certificate.right_coefficient:
            return InvalidEvidence(
                "the elaborated right coefficient does not match the "
                "certificate"
            )
        left = left_view.value
        right = right_view.value
        candidate = candidate_view.value
        left_coefficient = left_coefficient_view.value
        right_coefficient = right_coefficient_view.value
        if candidate.is_zero():
            if left.is_zero() and right.is_zero():
                return Verified((conclusion,))
            return Refuted(
                conclusion,
                (claim.candidate,),
                "the zero polynomial is not the gcd of nonzero inputs",
            )
        degree = self._ring.degree(candidate, 0)
        leading = self._ring.coefficient(candidate, (degree,))
        if not self._ring.coefficients.is_one(leading):
            return Refuted(
                conclusion,
                (claim.candidate,),
                "the canonical gcd must be monic",
            )
        for value, term in ((left, claim.left), (right, claim.right)):
            _, remainder = self._ring.divmod(value, candidate)
            if not remainder.is_zero():
                return Refuted(
                    conclusion,
                    (term, claim.candidate),
                    "the candidate does not divide an input",
                )
        combination = self._ring.add(
            self._ring.mul(left_coefficient, left),
            self._ring.mul(right_coefficient, right),
        )
        if not self._ring.equal(combination, candidate):
            return InvalidEvidence(
                "the Bezout certificate does not prove the candidate"
            )
        return Verified((conclusion,))


__all__ = ["PolynomialGcdChecker"]
