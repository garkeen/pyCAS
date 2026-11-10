"""Independent checker for `EqualOn` and `SamePartialFunction`.

The checker never searches for a representation.  It reads the certificate's
two `FunctionValue` objects, verifies that they are exactly the functions named
by the claim, and decides only the fragments it can prove:

- `EqualOn` accepts structurally identical representations, and polynomial
  representations whose difference is the zero polynomial, after proving that
  the claimed region is a total subregion of both intrinsic domains and both
  representation regions.  "Total" is checked with the definedness premises of
  every participating proposition: an open premise is `Unverified`, never read
  as an empty or total region.  A nonzero polynomial difference refutes a claim
  on `TRUE`; a restricted region is not refuted by a global difference.
- An `EqualOn` certificate may carry a `CoversCertificate` for the right
  function value's intrinsic domain over its representation regions.  The
  checker independently re-verifies that certificate and requires it to match
  the right value exactly.  A failed or mismatched coverage claim is
  `InvalidEvidence`, never `Refuted` and never `Verified`.
- `SamePartialFunction` accepts identical signatures, intrinsic-domain
  propositions and representation multisets.  A condition with an open
  definedness premise is not admitted as a complete-domain participant.  A
  different parameter count, parameter sort or result sort is refuted.
  Different parameter symbols are `Unverified(FRAGMENT)`: alpha-equivalence of
  function bindings is not decided here.  Different formulas are `Unverified`,
  never `DIFFERENT`, because two formulas may define the same domain or
  function extensionally.  This certificate does not carry a coverage claim;
  one supplied anyway is `InvalidEvidence`.

Every representation converted to a polynomial is independently elaborated and
admitted through the pre-assembled algebra bridge.  A typing failure or a
refused view is `Unverified`, never a refutation.

The intrinsic domain and every representation region are propositions with a
meaning key.  Before the checker uses either, it requires that key to name the
request's world and a frame visible from the request frame.  A certificate from
another scope is `InvalidEvidence`, not a refutation.
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
    problem_mismatch,
)
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.functions import (
    FunctionValue,
    same_parameter_shape,
    same_representation_multiset,
)
from cas.language.problems import Exactness, ProblemSpec, ValueDomain
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.functions.equality import (
    FunctionEqualityCertificate,
    FunctionEqualityClaim,
    FunctionEqualityKind,
    FunctionEqualityVocabulary,
    certificate_matches_claim,
    coverage_matches_value,
    parse_function_equality,
)
from cas.semantics import elaborate
from cas.semantics.bridge import (
    AlgebraView,
    PolynomialBridge,
    ViewRefused,
    typed_view,
)
from cas.semantics.conditions import is_empty_condition
from cas.semantics.frames import FrameStore
from cas.semantics.regions import (
    coordinate_symbols,
    premises_proved_from,
    proved_subregion,
    verify_region_certificate,
)
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

E = TypeVar("E")


class FunctionEqualityChecker(Generic[E]):
    """A checker for the function-equality predicates of one world."""

    id = "functions.equality"
    version = "1"

    def __init__(
        self,
        ring: PolynomialRing[E],
        signature: LanguageSignature,
        vocabulary: FunctionEqualityVocabulary,
        bridge: PolynomialBridge[E],
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "functions.equality",
    ) -> None:
        if len(ring.generators) != 1:
            raise TypeError("the function-equality fragment is univariate")
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
        """Independently elaborate and admit one representation term."""
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
        context = request.context
        if context is not None and context.algebra is not None:
            return InvalidEvidence(
                "a function problem has no algebra request"
            )
        if len(request.conclusions) != 1:
            return InvalidEvidence(
                "a function-equality certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        claim = parse_function_equality(self._vocabulary, conclusion.term)
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not an EqualOn or SamePartialFunction "
                "specification"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence(
                "a function-equality candidate is required"
            )
        problem = request.problem
        # A comparison publishes the proved proposition; an extension publishes
        # the new representation that the claim names on its right.
        role = request.candidate_role
        if role is CandidateRole.CONCLUSION:
            expected = conclusion.term
        elif role is CandidateRole.RIGHT:
            expected = claim.right
        else:
            return InvalidEvidence(
                "a function-equality candidate needs the conclusion or right "
                "candidate role"
            )
        if candidate != expected:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(certificate, FunctionEqualityCertificate):
            return InvalidEvidence(
                "a function-equality certificate is required"
            )
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        if problem is not None:
            region = (
                claim.region
                if claim.kind is FunctionEqualityKind.EQUAL_ON
                and problem.region is not None
                else None
            )
            mismatch = problem_mismatch(
                request,
                operations=("extend_function", "compare_functions"),
                inputs=(claim.left, claim.right),
                exactness=Exactness.EXACT,
                coefficient_domain=None,
                value_domain=ValueDomain.REAL,
                region=region,
            )
            if mismatch is not None:
                return InvalidEvidence(mismatch)
            if problem.target is not None:
                return InvalidEvidence(
                    "a function problem has no target variable"
                )
            mismatch = _function_input_mismatch(problem, certificate)
            if mismatch is not None:
                return InvalidEvidence(mismatch)
        if claim.kind is FunctionEqualityKind.EQUAL_ON:
            return self._check_equal_on(
                request.frame, conclusion, claim, certificate
            )
        return self._check_same(
            request.frame, conclusion, claim, certificate, problem
        )

    def _require_visible(
        self,
        proposition: Proposition,
        frame: FrameId,
        role: str,
    ) -> InvalidEvidence | None:
        """Refuse a certificate proposition read outside the request scope.

        The proposition's meaning key is the authority: a term that happens to
        match is not readable when its world or frame is unrelated to the
        request.  Ancestor frames remain visible, so a value defined earlier in
        the same chain stays usable.
        """
        if (
            proposition.meaning.world != self._frames.world.id
            or not self._frames.is_visible(proposition.meaning.frame, frame)
        ):
            return InvalidEvidence(
                f"the certificate's {role} belongs to another scope"
            )
        return None

    def _require_value_visible(
        self,
        value: FunctionValue,
        frame: FrameId,
        side: str,
    ) -> InvalidEvidence | None:
        """Require every domain/representation proposition to be readable."""
        invalid = self._require_visible(
            value.intrinsic_domain,
            frame,
            f"{side} intrinsic domain",
        )
        if invalid is not None:
            return invalid
        for index, representation in enumerate(value.representations):
            invalid = self._require_visible(
                representation.valid_on,
                frame,
                f"{side} representation {index} region",
            )
            if invalid is not None:
                return invalid
        return None

    def _require_value_regions_inside_domain(
        self,
        value: FunctionValue,
        side: str,
    ) -> InvalidEvidence | Unverified | None:
        """Check every representation region against the intrinsic domain.

        A `FunctionValue` is data: its constructor does not prove that a
        representation region is inside its declared domain.  The checker
        re-establishes that fact for every representation after the caller has
        checked visibility and the parameter sorts.  A provably outside region
        is invalid evidence; an undecided inclusion is `Unverified(GUARDED)`,
        never read as true.
        """
        for index, representation in enumerate(value.representations):
            contained = proved_subregion(
                representation.valid_on,
                value.intrinsic_domain,
                self._signature,
                same_meaning=False,
            )
            if contained is False:
                return InvalidEvidence(
                    f"the {side} representation {index} region is outside "
                    "its intrinsic domain"
                )
            if contained is None:
                return Unverified(
                    Reason.GUARDED,
                    f"the {side} representation {index} region is not proved "
                    "inside its intrinsic domain",
                )
        return None

    def _check_equal_on(
        self,
        frame: FrameId,
        conclusion: Proposition,
        claim: FunctionEqualityClaim,
        certificate: FunctionEqualityCertificate,
    ) -> CheckOutcome:
        left = certificate.left
        right = certificate.right
        for value, index, side in (
            (left, certificate.left_index, "left"),
            (right, certificate.right_index, "right"),
        ):
            invalid = self._require_visible(
                value.intrinsic_domain,
                frame,
                f"{side} intrinsic domain",
            )
            if invalid is not None:
                return invalid
            invalid = self._require_visible(
                value.representations[index].valid_on,
                frame,
                f"{side} representation region",
            )
            if invalid is not None:
                return invalid
        if not same_parameter_shape(left, right):
            return Refuted(
                conclusion,
                (claim.left, claim.right),
                "the functions have different parameter signatures",
            )
        if left.parameter_symbols != right.parameter_symbols:
            return Unverified(
                Reason.FRAGMENT,
                "parameter symbols differ; alpha-equivalence is not decided",
            )
        for value in (left, right):
            refusal = _dense_parameter_refusal(value)
            if refusal is not None:
                return refusal
        for value, side in ((left, "left"), (right, "right")):
            visible_invalid = self._require_value_visible(value, frame, side)
            if visible_invalid is not None:
                return visible_invalid
        coverage = certificate.coverage
        if coverage is not None:
            if not verify_region_certificate(coverage, self._signature):
                return InvalidEvidence(
                    "the coverage certificate is not proved in the "
                    "restricted region fragment"
                )
            if not coverage_matches_value(coverage, right):
                return InvalidEvidence(
                    "the coverage certificate does not match the right "
                    "function value"
                )
        for value, side in ((left, "left"), (right, "right")):
            region_invalid = self._require_value_regions_inside_domain(
                value, side
            )
            if region_invalid is not None:
                return region_invalid
        assert claim.region is not None
        region = claim.region
        issued = elaborate.proposition(
            region,
            self._frames,
            conclusion.meaning.frame,
            self._signature,
        )
        if not isinstance(issued, Proposition):
            return Unverified(
                Reason.FRAGMENT,
                "the claimed region cannot be issued as a proposition",
                missing=issued.missing,
            )
        claimed_region = issued
        foreign = coordinate_symbols(claimed_region.term) - set(
            left.parameter_symbols
        )
        if foreign:
            return Unverified(
                Reason.FRAGMENT,
                "the claimed region mentions variables that are not function "
                "parameters",
            )
        if is_empty_condition(claimed_region.term, self._signature):
            return Unverified(Reason.GUARDED, "the claimed region is empty")
        if not _real_valued(left) or not _real_valued(right):
            return Unverified(
                Reason.FRAGMENT,
                "function equality is stated for real-valued functions",
            )
        if S.join(left.result_sort, right.result_sort) is None:
            return Unverified(
                Reason.FRAGMENT,
                "the two functions have no common result sort",
            )
        for value, index, side in (
            (left, certificate.left_index, "left"),
            (right, certificate.right_index, "right"),
        ):
            representation = value.representations[index]
            if (
                proved_subregion(
                    claimed_region,
                    value.intrinsic_domain,
                    self._signature,
                    same_meaning=False,
                )
                is not True
            ):
                return Unverified(
                    Reason.GUARDED,
                    f"the region is not proved inside the {side} "
                    "intrinsic domain",
                )
            if (
                proved_subregion(
                    claimed_region,
                    representation.valid_on,
                    self._signature,
                    same_meaning=False,
                )
                is not True
            ):
                return Unverified(
                    Reason.GUARDED,
                    f"the region is not proved inside the {side} "
                    "representation region",
                )
        left_term = certificate.left_representation
        right_term = certificate.right_representation
        if left_term == right_term:
            return Verified((conclusion,))
        conclusion_frame = conclusion.meaning.frame
        left_view = self._view(left_term, conclusion_frame)
        if isinstance(left_view, Unverified):
            return left_view
        if left_view.source.term != left_term:
            return InvalidEvidence(
                "the elaborated left representation does not match the "
                "certificate"
            )
        right_view = self._view(right_term, conclusion_frame)
        if isinstance(right_view, Unverified):
            return right_view
        if right_view.source.term != right_term:
            return InvalidEvidence(
                "the elaborated right representation does not match the "
                "certificate"
            )
        if self._ring.equal(left_view.value, right_view.value):
            return Verified((conclusion,))
        if claimed_region.term == T.TRUE and not claimed_region.definedness:
            return Refuted(
                conclusion,
                (left_term, right_term),
                "the representations differ as polynomials",
            )
        return Unverified(
            Reason.FRAGMENT,
            "the representations are not proved equal on the region",
        )

    def _check_same(
        self,
        frame: FrameId,
        conclusion: Proposition,
        claim: FunctionEqualityClaim,
        certificate: FunctionEqualityCertificate,
        problem: ProblemSpec | None,
    ) -> CheckOutcome:
        if certificate.coverage is not None:
            return InvalidEvidence(
                "a SamePartialFunction certificate does not carry a "
                "coverage claim"
            )
        left = certificate.left
        right = certificate.right
        for value, side in ((left, "left"), (right, "right")):
            visible_invalid = self._require_value_visible(value, frame, side)
            if visible_invalid is not None:
                return visible_invalid
        for value in (left, right):
            refusal = _dense_parameter_refusal(value)
            if refusal is not None:
                return refusal
        for value, side in ((left, "left"), (right, "right")):
            region_invalid = self._require_value_regions_inside_domain(
                value, side
            )
            if region_invalid is not None:
                return region_invalid
        # `SamePartialFunction` states equality of the complete domains.  A
        # condition with an open definedness premise does not describe a total
        # region, so it is not admitted as a complete-domain participant even
        # when two values carry the identical proposition.
        for value, side in ((left, "left"), (right, "right")):
            conditions: list[tuple[str, Proposition]] = [
                ("intrinsic domain", value.intrinsic_domain)
            ]
            conditions.extend(
                (
                    f"representation {index} region",
                    representation.valid_on,
                )
                for index, representation in enumerate(
                    value.representations
                )
            )
            for role, condition in conditions:
                if (
                    premises_proved_from(
                        condition, condition, self._signature
                    )
                    is not True
                ):
                    return Unverified(
                        Reason.GUARDED,
                        f"the {side} {role} has an unproved definedness "
                        "premise",
                    )
        if not same_parameter_shape(left, right):
            return Refuted(
                conclusion,
                (claim.left, claim.right),
                "the functions have different parameter signatures",
            )
        if left.parameter_symbols != right.parameter_symbols:
            return Unverified(
                Reason.FRAGMENT,
                "parameter symbols differ; alpha-equivalence is not decided",
            )
        if problem is not None and problem.region is not None:
            invalid = self._require_visible(
                problem.region, frame, "problem region"
            )
            if invalid is not None:
                return invalid
            for value, side in ((left, "left"), (right, "right")):
                contained = proved_subregion(
                    problem.region,
                    value.intrinsic_domain,
                    self._signature,
                    same_meaning=False,
                )
                if contained is False:
                    return InvalidEvidence(
                        f"the problem region is outside the {side} complete "
                        "domain"
                    )
                if contained is None:
                    return Unverified(
                        Reason.GUARDED,
                        f"the problem region is not proved inside the {side} "
                        "complete domain",
                        conditions=(problem.region,),
                    )
        if left.intrinsic_domain != right.intrinsic_domain:
            return Unverified(
                Reason.FRAGMENT,
                "the intrinsic domains are not identical propositions",
            )
        if not _same_representations(left, right):
            return Unverified(
                Reason.FRAGMENT,
                "the representation multisets are not identical",
            )
        return Verified((conclusion,))


def _function_input_mismatch(
    problem: ProblemSpec,
    certificate: FunctionEqualityCertificate,
) -> str | None:
    """Why a certificate's function values do not match the fixed problem.

    A function problem fixes the `FunctionValue` objects themselves: the
    parameter binding, intrinsic domain and every representation region are
    part of the identity.  Comparing only the representation terms would accept
    a value with another domain.  A missing function input is invalid evidence,
    never a refutation.
    """
    expected = problem.function_inputs
    if problem.operation == "compare_functions":
        if len(expected) != 2:
            return (
                "a compare_functions problem must fix exactly two function "
                "inputs"
            )
        if certificate.left != expected[0] or certificate.right != expected[1]:
            return (
                "the certificate function values do not match the problem "
                "function inputs"
            )
    elif problem.operation == "extend_function":
        if len(expected) != 1:
            return (
                "an extend_function problem must fix exactly one function "
                "input"
            )
        if certificate.left != expected[0]:
            return (
                "the certificate function value does not match the problem "
                "function input"
            )
    return None


def _dense_parameter_refusal(value: FunctionValue) -> Unverified | None:
    """Refuse dense interval reasoning over non-dense parameter sorts.

    The region fragment reads comparisons in a dense linear order.  A function
    parameter declared over the integers (or any other non-dense sort) does not
    justify that reading, so equality is reported as `Unverified(GUARDED)`
    instead of being verified by an interval argument that does not apply.
    """
    for parameter in value.parameters:
        if parameter.sort not in (S.RATIONAL, S.REAL):
            return Unverified(
                Reason.GUARDED,
                "function equality over non-dense parameter sorts is not "
                "supported",
            )
    return None


def _real_valued(value: FunctionValue) -> bool:
    return value.result_sort.embeds_into(S.REAL)


def _same_representations(left: FunctionValue, right: FunctionValue) -> bool:
    return same_representation_multiset(left, right)


__all__ = ["FunctionEqualityChecker"]
