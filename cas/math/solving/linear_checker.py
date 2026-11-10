"""Independent checker for finite solution-set claims over Q.

The checker never solves the equation.  It parses the claimed set, evaluates
the supplied polynomial at every member, and for degree at most one proves
completeness from the unique-root formula.  Higher degree completeness is
`Unverified(FRAGMENT)`; soundness is still checked member by member.

The source polynomial is independently elaborated and admitted through the
pre-assembled algebra bridge.  A typing failure or a refused view is
`Unverified`, never a refutation.
"""

from __future__ import annotations

from fractions import Fraction

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
from cas.language.problems import Coverage, Exactness, Role
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.sets import set_members
from cas.language.signatures import LanguageSignature
from cas.math.solving.linear_specification import (
    LinearSolutionCertificate,
    SolutionSetKind,
    SolutionSetVocabulary,
    certificate_matches_claim,
    parse_solution_set,
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


class LinearSolutionChecker:
    """A checker for one univariate polynomial ring over Q."""

    id = "solving.linear"
    version = "1"

    def __init__(
        self,
        ring: UnivariatePolynomialRing[Fraction],
        signature: LanguageSignature,
        vocabulary: SolutionSetVocabulary,
        bridge: PolynomialBridge[Fraction],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "solving.linear",
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
                "a solution-set certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        frame = conclusion.meaning.frame
        claim = parse_solution_set(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a solution-set specification"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence(
                "a solution-set candidate is required"
            )
        if request.candidate_role is not CandidateRole.SET:
            return InvalidEvidence(
                "a solution-set candidate needs the set candidate role"
            )
        if candidate != claim.set_term:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(certificate, LinearSolutionCertificate):
            return InvalidEvidence("a solution certificate is required")
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        mismatch = problem_mismatch(
            request,
            operations=("solve_linear",),
            target=claim.variable.symbol_id,
            inputs=(claim.source,),
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
        problem = request.problem
        if problem is not None:
            expected = (
                Coverage.COMPLETE_SET
                if claim.kind is SolutionSetKind.COMPLETE
                else Coverage.SOUND_SET
            )
            if problem.coverage is not expected:
                return InvalidEvidence(
                    "the problem coverage does not match the specification"
                )
        source_view = self._view(claim.source, frame)
        if isinstance(source_view, Unverified):
            return source_view
        if source_view.source.term != claim.source:
            return InvalidEvidence(
                "the elaborated source does not match the claim"
            )
        if source_view.symbol_for(Role.TARGET, 0) != claim.variable.symbol_id:
            return Unverified(
                Reason.FRAGMENT,
                "the claim is not stated in this view's target variable",
            )
        members = set_members(claim.set_term, self._signature)
        if members is None:
            return InvalidEvidence(
                "the third argument is not a finite-set term"
            )
        values: list[Fraction] = []
        for member in members:
            value = _rational(member)
            if value is None:
                return Unverified(
                    Reason.FRAGMENT,
                    "the solution set contains a non-rational member",
                )
            values.append(value)
        source = source_view.value
        for member, value in zip(members, values):
            if _evaluate(self._ring, source, value) != 0:
                return Refuted(
                    conclusion,
                    (member,),
                    "the set contains a value that is not a root",
                )
        if claim.kind is SolutionSetKind.SOUND:
            return Verified((conclusion,))
        return self._complete(conclusion, source, members, values)

    def _complete(
        self,
        conclusion: Proposition,
        source: Polynomial[Fraction],
        members: tuple[T.Term, ...],
        values: list[Fraction],
    ) -> CheckOutcome:
        degree = self._ring.degree(source, 0) if not source.is_zero() else -1
        if source.is_zero():
            return Refuted(
                conclusion,
                (_outside(members),),
                "the zero polynomial has every real number as a root",
            )
        if degree == 0:
            if not members:
                return Verified((conclusion,))
            return Refuted(
                conclusion,
                (members[0],),
                "a nonzero constant has no roots",
            )
        if degree == 1:
            root = _root(self._ring, source)
            root_term = T.number(root)
            if members == (root_term,):
                return Verified((conclusion,))
            if not members:
                return Refuted(
                    conclusion,
                    (root_term,),
                    "the unique root is missing from the set",
                )
            return Refuted(
                conclusion,
                (root_term,),
                "the set is not the singleton of the unique root",
            )
        return Unverified(
            Reason.FRAGMENT,
            "complete solution sets are only checked for degree at most one",
        )


def _rational(term: T.Term) -> Fraction | None:
    if isinstance(term, T.IntLit):
        return Fraction(term.value)
    if isinstance(term, T.RatLit):
        return term.value
    return None


def _evaluate(
    ring: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
    point: Fraction,
) -> Fraction:
    coefficients = ring.coefficients
    result = coefficients.zero()
    for exponents, coefficient in value.terms:
        term = coefficient
        for exponent in exponents:
            term = coefficients.mul(
                term, coefficients.pow(point, exponent)
            )
        result = coefficients.add(result, term)
    return result


def _root(
    ring: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> Fraction:
    constant = ring.coefficient(value, (0,))
    leading = ring.coefficient(value, (1,))
    return ring.coefficients.neg(
        ring.coefficients.div(constant, leading)
    )


def _outside(members: tuple[T.Term, ...]) -> T.Term:
    """A rational term not structurally present in a finite set."""
    known = set(members)
    candidate = 0
    while True:
        term = T.number(candidate)
        if term not in known:
            return term
        candidate = -candidate if candidate > 0 else -candidate + 1


__all__ = ["LinearSolutionChecker"]
