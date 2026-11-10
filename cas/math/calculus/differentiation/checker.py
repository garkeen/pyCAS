"""Independent checker for `HasDerivative` on the polynomial fragment.

The checker never generates a derivative. It parses the claim, requires a
certificate that names exactly the same instance, independently elaborates and
admits both sides through the pre-assembled algebra bridge, and delegates the
mathematics to `verify_derivative` — a second implementation of the derivative
rule that does not call the ring's own `derivative`.

A typing failure or a refused view is `Unverified`, never a refutation.
"""

from __future__ import annotations

from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial, PolynomialRing
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
from cas.language.problems import Exactness, ProblemSpec, Role
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeClaim,
    DerivativeVocabulary,
    certificate_matches_claim,
    parse_has_derivative,
)
from cas.math.calculus.differentiation.verify import verify_derivative
from cas.semantics.bridge import (
    AlgebraView,
    PolynomialBridge,
    ViewRefused,
    typed_view,
)
from cas.semantics.conditions import is_empty_condition
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import binding as B
from cas.syntax import term as T

E = TypeVar("E")


class DerivativeChecker(Generic[E]):
    """A checker for one univariate polynomial ring and one predicate symbol."""

    id = "calculus.derivative"
    version = "1"

    def __init__(
        self,
        ring: PolynomialRing[E],
        signature: LanguageSignature,
        vocabulary: DerivativeVocabulary,
        bridge: PolynomialBridge[E],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "calculus.derivative",
    ) -> None:
        if len(ring.generators) != 1:
            raise TypeError("the derivative fragment is univariate")
        if not ring.contains(bridge.ring.zero()):
            raise ValueError(
                "the checker ring does not own the bridge's elements"
            )
        if not identifier:
            raise ValueError("a checker needs an identifier")
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
        for conclusion in request.conclusions:
            frame = conclusion.meaning.frame
            claim = parse_has_derivative(self._vocabulary, conclusion.term)
            if claim is None:
                return InvalidEvidence(
                    "the conclusion is not a HasDerivative specification"
                )
            candidate_term = request.candidate
            if candidate_term is None:
                return InvalidEvidence(
                    "a derivative candidate is required"
                )
            problem = request.problem
            role = request.candidate_role
            if role is CandidateRole.RESULT:
                expected = claim.candidate
            elif role is CandidateRole.SOURCE:
                expected = claim.source
            else:
                return InvalidEvidence(
                    "a derivative candidate needs the result or source "
                    "candidate role"
                )
            if candidate_term != expected:
                return InvalidEvidence(
                    "the candidate does not match the specification"
                )
            certificate = request.certificate
            if not isinstance(certificate, DerivativeCertificate):
                return InvalidEvidence("a derivative certificate is required")
            if certificate.derivation is not None:
                return InvalidEvidence(
                    "the polynomial checker does not interpret a "
                    "rule-instance derivation"
                )
            if not certificate_matches_claim(certificate, claim):
                return InvalidEvidence(
                    "the certificate does not match the specification"
                )
            mismatch = problem_mismatch(
                request,
                operations=("differentiate", "integrate", "specialize"),
                target=claim.variable.symbol_id,
                roles=self._request.roles,
                interpretation_requirement=(
                    self._request.interpretation_requirement
                ),
                exactness=Exactness.EXACT,
                coefficient_domain=self._request.coefficient_domain,
                value_domain=self._request.value_domain,
                # A problem with no region accepts a conditional answer that
                # the workflow records in `result_region`; only an explicitly
                # requested region demands coverage by the claim.
                region=(
                    claim.region
                    if problem is not None and problem.region is not None
                    else None
                ),
            )
            if mismatch is not None:
                return InvalidEvidence(mismatch)
            if problem is not None:
                problem_inputs = tuple(
                    item.term for item in problem.inputs
                )
                if (
                    problem.operation == "differentiate"
                    and problem_inputs != (claim.source,)
                ):
                    return InvalidEvidence(
                        "the problem inputs do not match the specification"
                    )
                if (
                    problem.operation == "integrate"
                    and problem_inputs != (claim.candidate,)
                ):
                    return InvalidEvidence(
                        "the problem inputs do not match the specification"
                    )
                specialization_issue = _specialization_mismatch(
                    problem, certificate, claim
                )
                if specialization_issue is not None:
                    return InvalidEvidence(specialization_issue)
            if is_empty_condition(claim.region, self._signature):
                return Unverified(
                    Reason.GUARDED,
                    "the claimed region is empty",
                )
            source = self._view(claim.source, frame)
            if isinstance(source, Unverified):
                return source
            if source.source.term != claim.source:
                return InvalidEvidence(
                    "the elaborated source does not match the claim"
                )
            if source.symbol_for(Role.TARGET, 0) != claim.variable.symbol_id:
                return Unverified(
                    Reason.FRAGMENT,
                    "the claim is not stated in this view's target variable",
                )
            candidate = self._view(claim.candidate, frame)
            if isinstance(candidate, Unverified):
                return candidate
            if candidate.source.term != claim.candidate:
                return InvalidEvidence(
                    "the elaborated candidate does not match the claim"
                )
            if verify_derivative(
                self._ring, source.value, candidate.value, 0
            ):
                continue
            if claim.region == T.TRUE:
                return Refuted(
                    conclusion,
                    (claim.source, claim.candidate),
                    "the candidate is not the derivative of the source",
                )
            # A global coefficient mismatch does not decide a restricted
            # region: the difference may vanish on that region.  Refutation
            # would require an identity test adapted to the region or a
            # counterexample, neither of which this fragment provides.
            return Unverified(
                Reason.FRAGMENT,
                "a global coefficient mismatch does not refute a "
                "restricted claim",
            )
        return Verified(tuple(request.conclusions))


def _specialization_mismatch(
    problem: ProblemSpec,
    certificate: DerivativeCertificate,
    claim: DerivativeClaim,
) -> str | None:
    """Whether a `specialize` certificate really derives its claim's source.

    The checker must not trust the specialised source text: it rebuilds the
    source by substituting the certificate's exact rational values into the
    generic problem input and requires the result to be the claimed source.
    """
    if problem.operation != "specialize":
        return None
    generic_source = certificate.generic_source
    specialization = certificate.specialization
    if generic_source is None or specialization is None:
        return (
            "a specialize problem needs the generic source and the "
            "specialization mapping"
        )
    if problem.inputs[0].term != generic_source:
        return "the generic source does not match the problem input"
    mapping = {
        symbol: T.number(value)
        for symbol, value in specialization.values.items()
    }
    if B.substitute_free(generic_source, mapping) != claim.source:
        return (
            "the specialized source is not the substitution of the generic "
            "source"
        )
    return None


__all__ = ["DerivativeChecker"]
