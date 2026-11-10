"""Independent checker for `HasResultant` over Q.

The checker rebuilds the Sylvester matrix, clears denominators, and evaluates
the resulting integer determinant with Bareiss fraction-free elimination.  The
ring's own `resultant` uses field elimination, so the two computations do not
share the determinant algorithm.

Every claimed polynomial is independently elaborated and admitted through the
pre-assembled algebra bridge.  A typing failure or a refused view is
`Unverified`, never a refutation.
"""

from __future__ import annotations

from fractions import Fraction
from math import lcm

from cas.algebra.integer_matrix import IntegerMatrixSpace
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
from cas.math.algebra.resultant_specification import (
    ResultantCertificate,
    ResultantVocabulary,
    certificate_matches_claim,
    parse_resultant,
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


class ResultantChecker:
    """A checker for one univariate polynomial ring over Q."""

    id = "algebra.resultant"
    version = "1"

    def __init__(
        self,
        ring: UnivariatePolynomialRing[Fraction],
        signature: LanguageSignature,
        vocabulary: ResultantVocabulary,
        bridge: PolynomialBridge[Fraction],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "algebra.resultant",
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
    ) -> AlgebraView[Polynomial[Fraction]] | Unverified:
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
                "a resultant certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        frame = conclusion.meaning.frame
        claim = parse_resultant(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a HasResultant specification"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence("a resultant candidate is required")
        if request.candidate_role is not CandidateRole.RESULT:
            return InvalidEvidence(
                "a resultant candidate needs the result candidate role"
            )
        if candidate != claim.result:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(certificate, ResultantCertificate):
            return InvalidEvidence("a resultant certificate is required")
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        mismatch = problem_mismatch(
            request,
            operations=("resultant",),
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
        claimed = _rational(claim.result)
        if claimed is None:
            return Unverified(
                Reason.FRAGMENT,
                "the claimed resultant is not a rational literal",
            )
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
        value = _resultant(self._ring, left_view.value, right_view.value)
        if value == claimed:
            return Verified((conclusion,))
        return Refuted(
            conclusion,
            (claim.result,),
            "the claimed value is not the Sylvester determinant",
        )


def _rational(term: T.Term) -> Fraction | None:
    if isinstance(term, T.IntLit):
        return Fraction(term.value)
    if isinstance(term, T.RatLit):
        return term.value
    return None


def _resultant(
    ring: UnivariatePolynomialRing[Fraction],
    left: Polynomial[Fraction],
    right: Polynomial[Fraction],
) -> Fraction:
    if left.is_zero() or right.is_zero():
        return Fraction(0)
    left_degree = ring.degree(left, 0)
    right_degree = ring.degree(right, 0)
    if left_degree == 0 and right_degree == 0:
        return Fraction(1)
    if left_degree == 0:
        return ring.coefficient(left, (0,)) ** right_degree
    if right_degree == 0:
        return ring.coefficient(right, (0,)) ** left_degree
    size = left_degree + right_degree
    left_coefficients = [
        ring.coefficient(left, (index,))
        for index in range(left_degree, -1, -1)
    ]
    right_coefficients = [
        ring.coefficient(right, (index,))
        for index in range(right_degree, -1, -1)
    ]
    rows: list[list[Fraction]] = []
    for shift in range(right_degree):
        row = [Fraction(0) for _ in range(size)]
        for index, coefficient in enumerate(left_coefficients):
            row[shift + index] = coefficient
        rows.append(row)
    for shift in range(left_degree):
        row = [Fraction(0) for _ in range(size)]
        for index, coefficient in enumerate(right_coefficients):
            row[shift + index] = coefficient
        rows.append(row)
    denominator = 1
    for row in rows:
        for entry in row:
            denominator = lcm(denominator, entry.denominator)
    space = IntegerMatrixSpace(size, size)
    integer = space.matrix(
        tuple(
            tuple(int(entry * denominator) for entry in row)
            for row in rows
        )
    )
    determinant = space.determinant(integer)
    return Fraction(determinant, denominator**size)


__all__ = ["ResultantChecker"]
