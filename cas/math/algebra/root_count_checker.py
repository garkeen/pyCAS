"""Independent checker for `HasRootCount` over a univariate rational field.

The checker never imports the root-count search module.  It independently
elaborates and admits the polynomial, endpoints and every Sturm-chain entry,
then verifies the supplied chain link by link: the first entry is the
polynomial, the second is its derivative (for a nonconstant polynomial), every
later entry is the negative remainder of the two preceding entries, every
entry before the terminator is nonzero, and the last entry is a nonzero
constant.  It does not rebuild a fresh chain from the polynomial.  The sign
variations and the open-interval formula ``V(a) - V(b) - [p(b) = 0]`` are then
computed from the verified certificate chain.

A wrong count for a verified squarefree chain is `Refuted` with a detail.  A
malformed certificate, a certificate/claim mismatch, a candidate mismatch, or a
chain that is missing, extra, mistyped, non-terminating or does not satisfy the
recurrence is `InvalidEvidence`.  A zero polynomial, a nonconstant endpoint or
a reversed interval is `Unverified(FRAGMENT)` with the missing capability: a
fragment boundary is not a mathematical refutation.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.protocols import Ordered
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
from cas.language.problems import Exactness
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.algebra.root_count_specification import (
    RootCountCertificate,
    RootCountVocabulary,
    certificate_matches_claim,
    parse_root_count,
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


class RootCountChecker(Generic[E]):
    """A checker for one univariate polynomial ring over a field."""

    id = "algebra.root_count"
    version = "1"

    def __init__(
        self,
        ring: UnivariatePolynomialRing[E],
        signature: LanguageSignature,
        vocabulary: RootCountVocabulary,
        bridge: PolynomialBridge[E],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "algebra.root_count",
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
                "a root-count certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        frame = conclusion.meaning.frame
        claim = parse_root_count(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a HasRootCount specification"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence("a root-count candidate is required")
        if request.candidate_role is not CandidateRole.RESULT:
            return InvalidEvidence(
                "a root-count candidate needs the result candidate role"
            )
        if candidate != claim.count:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(certificate, RootCountCertificate):
            return InvalidEvidence("a root-count certificate is required")
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        mismatch = problem_mismatch(
            request,
            operations=("root_count",),
            target=self._request.roles.target,
            inputs=(claim.polynomial, claim.lower, claim.upper),
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
        claimed_count = _rational(claim.count)
        if claimed_count is None:
            return Unverified(
                Reason.FRAGMENT,
                "the claimed root count is not a rational literal",
                missing=frozenset({"integer_root_count"}),
            )
        polynomial_view = self._view(claim.polynomial, frame)
        if isinstance(polynomial_view, Unverified):
            return polynomial_view
        if polynomial_view.source.term != claim.polynomial:
            return InvalidEvidence(
                "the elaborated polynomial does not match the claim"
            )
        lower_view = self._view(claim.lower, frame)
        if isinstance(lower_view, Unverified):
            return lower_view
        if lower_view.source.term != claim.lower:
            return InvalidEvidence(
                "the elaborated lower endpoint does not match the claim"
            )
        upper_view = self._view(claim.upper, frame)
        if isinstance(upper_view, Unverified):
            return upper_view
        if upper_view.source.term != claim.upper:
            return InvalidEvidence(
                "the elaborated upper endpoint does not match the claim"
            )
        coefficients = self._ring.coefficients
        if coefficients.characteristic != 0:
            return Unverified(
                Reason.FRAGMENT,
                "root counting needs a characteristic-zero coefficient field",
                missing=frozenset({"characteristic_zero_field"}),
            )
        if not isinstance(coefficients, Ordered):
            return Unverified(
                Reason.FRAGMENT,
                "root counting needs an ordered coefficient field",
                missing=frozenset({"ordered_coefficient_field"}),
            )
        if not self._ring.is_constant(lower_view.value):
            return Unverified(
                Reason.FRAGMENT,
                "the lower endpoint is not a constant polynomial",
                missing=frozenset({"rational_endpoint"}),
            )
        if not self._ring.is_constant(upper_view.value):
            return Unverified(
                Reason.FRAGMENT,
                "the upper endpoint is not a constant polynomial",
                missing=frozenset({"rational_endpoint"}),
            )
        lower = self._ring.coefficient(lower_view.value, (0,))
        upper = self._ring.coefficient(upper_view.value, (0,))
        if not coefficients.less(lower, upper):
            return Unverified(
                Reason.FRAGMENT,
                "the root-count interval needs lower < upper",
                missing=frozenset({"ordered_endpoints"}),
            )
        polynomial = polynomial_view.value
        if polynomial.is_zero():
            return Unverified(
                Reason.FRAGMENT,
                "the zero polynomial has every real number as a root",
                missing=frozenset({"nonzero_polynomial"}),
            )
        chain_values: list[Polynomial[E]] = []
        for term in certificate.chain:
            view = self._view(term, frame)
            if isinstance(view, Unverified):
                return view
            if view.source.term != term:
                return InvalidEvidence(
                    "an elaborated Sturm-chain entry does not match the "
                    "certificate"
                )
            chain_values.append(view.value)
        chain_issue = self._chain_mismatch(
            polynomial, tuple(chain_values)
        )
        if chain_issue is not None:
            return InvalidEvidence(chain_issue)
        lower_variations = _sign_variations(
            self._ring, coefficients, tuple(chain_values), lower
        )
        upper_variations = _sign_variations(
            self._ring, coefficients, tuple(chain_values), upper
        )
        upper_root = (
            1
            if coefficients.is_zero(_evaluate(self._ring, polynomial, upper))
            else 0
        )
        expected_count = lower_variations - upper_variations - upper_root
        if claimed_count != expected_count:
            return Refuted(
                conclusion,
                (claim.count,),
                "the claimed count is not the number of distinct real roots "
                "of this squarefree polynomial in the open interval",
            )
        return Verified((conclusion,))

    def _chain_mismatch(
        self,
        polynomial: Polynomial[E],
        chain: tuple[Polynomial[E], ...],
    ) -> str | None:
        """Why the supplied chain is not a Sturm chain for ``polynomial``.

        This verifies the certificate instead of rebuilding a second chain
        from the polynomial.  The recurrence is checked with the ring's own
        exact primitives; every non-final entry must be nonzero so the next
        division is defined, and the terminator must be a nonzero constant.
        """
        ring = self._ring
        if not chain:
            return "the certificate Sturm chain is empty"
        for entry in chain:
            if entry.is_zero():
                return "the Sturm chain contains a zero entry"
        if not ring.equal(chain[0], polynomial):
            return "the first Sturm-chain entry is not the polynomial"
        if ring.is_constant(polynomial):
            if len(chain) != 1:
                return (
                    "a constant polynomial needs a one-entry Sturm chain"
                )
            return None
        if len(chain) < 2:
            return "the Sturm chain is missing the derivative entry"
        derivative = ring.derivative(polynomial, 0)
        if not ring.equal(chain[1], derivative):
            return "the second Sturm-chain entry is not the derivative"
        for index in range(len(chain) - 2):
            _, remainder = ring.divmod(chain[index], chain[index + 1])
            if remainder.is_zero():
                return (
                    "the Sturm chain reaches a zero remainder before a "
                    "constant terminator"
                )
            following = ring.neg(remainder)
            if not ring.equal(chain[index + 2], following):
                return (
                    "the certificate chain does not satisfy the Sturm "
                    "recurrence"
                )
        if not ring.is_constant(chain[-1]):
            return "the Sturm chain does not end at a constant"
        return None


def _rational(term: T.Term) -> Fraction | None:
    if isinstance(term, T.IntLit):
        return Fraction(term.value)
    if isinstance(term, T.RatLit):
        return term.value
    return None


def _evaluate(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
    point: E,
) -> E:
    coefficients = ring.coefficients
    result = coefficients.zero()
    if value.is_zero():
        return result
    for exponent in range(ring.degree(value, 0), -1, -1):
        result = coefficients.add(
            coefficients.mul(result, point),
            ring.coefficient(value, (exponent,)),
        )
    return result


def _sign_variations(
    ring: UnivariatePolynomialRing[E],
    coefficients: Ordered[E],
    chain: tuple[Polynomial[E], ...],
    point: E,
) -> int:
    variations = 0
    previous = 0
    for value in chain:
        sign = coefficients.sign(_evaluate(ring, value, point))
        if sign == 0:
            continue
        if previous != 0 and sign != previous:
            variations += 1
        previous = sign
    return variations


__all__ = ["RootCountChecker"]
