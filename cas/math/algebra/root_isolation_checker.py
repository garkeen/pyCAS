"""Independent checker for `HasRootIsolation` over a univariate rational field.

The checker never imports the root-isolation search module or its operation.
It independently elaborates and admits the polynomial, verifies the supplied
Sturm chain link by link through the shared checker-side
`sturm_certificate` helper, recomputes Cauchy's root bound, and checks the
candidate interval set.  It does not rebuild a second chain.

A verified set has rational non-root endpoints, strictly increasing lower
endpoints, disjoint open interiors, every interval inside the certified bound,
exactly one distinct root per interval, and the same total number of roots as
the whole interval `(-B, B)`.  A wrong count, missing root or overlapping
interval is `Refuted`.  A malformed certificate or set is `InvalidEvidence`.
A zero polynomial, a non-squarefree polynomial or a non-ordered field is
`Unverified(FRAGMENT)`: a fragment boundary is not a mathematical refutation.
"""

from __future__ import annotations

from fractions import Fraction

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
from cas.language.problems import (
    Coverage,
    Exactness,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.sets import set_members
from cas.language.signatures import LanguageSignature
from cas.math.algebra.root_isolation_specification import (
    RootIsolationCertificate,
    RootIsolationVocabulary,
    certificate_matches_claim,
    parse_root_isolation,
)
from cas.math.algebra.sturm_certificate import (
    ChainFragmentGap,
    ChainMismatch,
    open_interval_count,
    verify_sturm_chain,
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


class RootIsolationChecker:
    """A checker for one univariate polynomial ring over Q."""

    id = "algebra.root_isolation"
    version = "1"

    def __init__(
        self,
        ring: UnivariatePolynomialRing[Fraction],
        signature: LanguageSignature,
        vocabulary: RootIsolationVocabulary,
        bridge: PolynomialBridge[Fraction],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "algebra.root_isolation",
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
                "a root-isolation certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        frame = conclusion.meaning.frame
        claim = parse_root_isolation(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a HasRootIsolation specification"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence(
                "a root-isolation candidate is required"
            )
        if request.candidate_role is not CandidateRole.RESULT:
            return InvalidEvidence(
                "a root-isolation candidate needs the result candidate role"
            )
        if candidate != claim.intervals:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(certificate, RootIsolationCertificate):
            return InvalidEvidence(
                "a root-isolation certificate is required"
            )
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        mismatch = problem_mismatch(
            request,
            operations=("isolate_roots",),
            target=self._request.roles.target,
            inputs=(claim.polynomial,),
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
            if problem.coverage is not Coverage.COMPLETE_SET:
                return InvalidEvidence(
                    "root isolation requires complete-set coverage"
                )
            if problem.result_language is not ResultLanguage.SET:
                return InvalidEvidence(
                    "root isolation requires a set result language"
                )
        polynomial_view = self._view(claim.polynomial, frame)
        if isinstance(polynomial_view, Unverified):
            return polynomial_view
        if polynomial_view.source.term != claim.polynomial:
            return InvalidEvidence(
                "the elaborated polynomial does not match the claim"
            )
        coefficients = self._ring.coefficients
        if coefficients.characteristic != 0:
            return Unverified(
                Reason.FRAGMENT,
                "root isolation needs a characteristic-zero coefficient field",
                missing=frozenset({"characteristic_zero_field"}),
            )
        if not isinstance(coefficients, Ordered):
            return Unverified(
                Reason.FRAGMENT,
                "root isolation needs an ordered coefficient field",
                missing=frozenset({"ordered_coefficient_field"}),
            )
        polynomial = polynomial_view.value
        if polynomial.is_zero():
            return Unverified(
                Reason.FRAGMENT,
                "the zero polynomial has every real number as a root",
                missing=frozenset({"nonzero_polynomial"}),
            )
        chain_values: list[Polynomial[Fraction]] = []
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
        chain = tuple(chain_values)
        chain_result = verify_sturm_chain(self._ring, polynomial, chain)
        if isinstance(chain_result, ChainFragmentGap):
            return Unverified(
                Reason.FRAGMENT,
                chain_result.detail,
                missing=chain_result.missing,
            )
        if isinstance(chain_result, ChainMismatch):
            return InvalidEvidence(chain_result.detail)
        certificate_bound = _rational(certificate.bound)
        if certificate_bound is None:
            return InvalidEvidence(
                "the certificate bound is not a rational literal"
            )
        cauchy = _cauchy_bound(self._ring, polynomial)
        if certificate_bound < cauchy:
            return InvalidEvidence(
                "the certificate bound is below the Cauchy root bound"
            )
        members = set_members(claim.intervals, self._signature)
        if members is None:
            return InvalidEvidence(
                "the second argument is not a finite-set term"
            )
        parsed: list[tuple[Fraction, Fraction, T.Term]] = []
        for member in members:
            if not isinstance(member, T.Apply) or not isinstance(
                member.operator, T.SymbolRef
            ):
                return InvalidEvidence(
                    "an interval-set member is not an Interval application"
                )
            if member.operator.symbol_id != self._vocabulary.interval_symbol:
                return InvalidEvidence(
                    "an interval-set member is not this vocabulary's Interval"
                )
            if len(member.arguments) != 2:
                return InvalidEvidence(
                    "an Interval application needs two endpoints"
                )
            lower = _rational(member.arguments[0])
            upper = _rational(member.arguments[1])
            if lower is None or upper is None:
                return Unverified(
                    Reason.FRAGMENT,
                    "an interval endpoint is not a rational literal",
                    missing=frozenset({"rational_endpoint"}),
                )
            if not lower < upper:
                return Refuted(
                    conclusion,
                    (member,),
                    "an interval needs lower < upper",
                )
            if not (-certificate_bound < lower and upper < certificate_bound):
                return Refuted(
                    conclusion,
                    (member,),
                    "an interval endpoint lies outside the certified bound",
                )
            if _is_root(self._ring, polynomial, lower) or _is_root(
                self._ring, polynomial, upper
            ):
                return Refuted(
                    conclusion,
                    (member,),
                    "an interval endpoint is a root; isolation intervals need "
                    "non-root endpoints",
                )
            parsed.append((lower, upper, member))
        parsed.sort(key=lambda item: item[0])
        previous_upper: Fraction | None = None
        for lower, upper, member in parsed:
            if previous_upper is not None and not previous_upper <= lower:
                return Refuted(
                    conclusion,
                    (member,),
                    "isolation intervals overlap or are not strictly ordered",
                )
            previous_upper = upper
        total = open_interval_count(
            self._ring,
            polynomial,
            chain,
            -certificate_bound,
            certificate_bound,
        )
        covered = 0
        for lower, upper, member in parsed:
            count = open_interval_count(
                self._ring, polynomial, chain, lower, upper
            )
            if count != 1:
                return Refuted(
                    conclusion,
                    (member,),
                    "an isolation interval does not contain exactly one "
                    "distinct real root",
                )
            covered += count
        if covered != total:
            return Refuted(
                conclusion,
                (claim.intervals,),
                "the intervals do not cover every distinct real root inside "
                "the certified bound",
            )
        return Verified((conclusion,))


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
    if value.is_zero():
        return result
    for exponent in range(ring.degree(value, 0), -1, -1):
        result = coefficients.add(
            coefficients.mul(result, point),
            ring.coefficient(value, (exponent,)),
        )
    return result


def _is_root(
    ring: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
    point: Fraction,
) -> bool:
    return ring.coefficients.is_zero(_evaluate(ring, value, point))


def _cauchy_bound(
    ring: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> Fraction:
    """Cauchy's strict bound, recomputed independently of the search side."""
    coefficients = ring.coefficients
    if ring.is_constant(value):
        return coefficients.one()
    degree = ring.degree(value, 0)
    leading = ring.coefficient(value, (degree,))
    maximum = coefficients.zero()
    for exponent in range(degree):
        ratio = coefficients.div(
            ring.coefficient(value, (exponent,)), leading
        )
        magnitude = ratio if ratio >= 0 else -ratio
        if magnitude > maximum:
            maximum = magnitude
    return coefficients.add(coefficients.one(), maximum)


__all__ = ["RootIsolationChecker"]
