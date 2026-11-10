"""Independent checker for Hermite reductions.

The checker never calls the reduction search.  It re-parses the claimed
decomposition, differentiates `v` with the rational-function field, adds `r`,
and compares the result with `f`; it separately checks that the denominator of
`r` is squarefree.  A malformed certificate is `InvalidEvidence`, a false
global identity is `Refuted`, and a fragment outside the rational-function
bridge is `Unverified`.

The source's intrinsic domain and representation region are real premises of
the claim.  The checker consumes the view's `Definedness`: a strict validity
region carries a `SubregionCertificate`, which the checker re-verifies; without
a certificate the context's definedness service (or the condition fragment)
must prove the inclusion.  A non-total source carries the rational bridge's
single ``Ne(D, 0)`` condition, where ``D`` is the product of every inverse base
in the source (including factors cancelled in ``K(x)``).
The checker proves the claim region is a non-empty subregion of every source
region, and proves the denominators of the claimed parts divide ``D`` in the
polynomial ring.  ``D != 0`` then implies both parts are defined on the claim
region.  The formal identity in ``K(x)`` is verified as in the total case.

A global identity failure refutes a global claim.  On a restricted region it is
only a fragment limitation: a nonzero rational function can still vanish on a
finite exceptional set, so the checker reports ``Unverified`` rather than
``Refuted``.  A non-total source never supports a global ``U = TRUE`` claim.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial
from cas.algebra.rational import RationalFunction, RationalFunctionField
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
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.calculus.integration.hermite_specification import (
    HermiteCertificate,
    HermiteClaim,
    HermiteVocabulary,
    certificate_matches_claim,
    parse_hermite_reduction,
)
from cas.semantics import elaborate
from cas.semantics.bridge import (
    AlgebraView,
    RationalFunctionBridge,
    ViewRefused,
    typed_view,
)
from cas.semantics.conditions import is_empty_condition, is_subregion
from cas.semantics.regions import verify_region_certificate
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

E = TypeVar("E")


@dataclass(frozen=True, slots=True)
class HermiteChecker(Generic[E]):
    """Verify `f = D(v) + r` and the squarefree-denominator condition."""

    bridge: RationalFunctionBridge[E]
    vocabulary: HermiteVocabulary
    request: AlgebraRequest
    id: str = "calculus.hermite"
    version: str = "1"

    @property
    def field(self) -> RationalFunctionField[E]:
        return self.bridge.field

    def _view(
        self, term: T.Term, request: CheckRequest
    ) -> AlgebraView[RationalFunction[E]] | Unverified:
        """Admit one claimed term through the rational bridge."""
        outcome = typed_view(
            self.bridge,
            term,
            self.bridge.frames,
            request.frame,
            self.bridge.signature,
            self.request,
        )
        if isinstance(outcome, ViewRefused):
            return Unverified(
                outcome.reason,
                outcome.detail,
                missing=outcome.missing,
                conditions=outcome.conditions,
            )
        if isinstance(outcome, AlgebraView):
            return outcome
        return Unverified(
            Reason.FRAGMENT,
            outcome.detail,
            missing=outcome.missing,
        )

    def _subregion(
        self,
        request: CheckRequest,
        subregion: T.Term,
        region: T.Term,
    ) -> bool | None:
        """Decide a region inclusion through the context's decision service.

        A kernel-built request carries the service; a direct test that
        constructs a bare context keeps the condition fragment fallback.
        """
        context = request.context
        if context is not None and context.decision is not None:
            return context.decision.is_subregion(subregion, region)
        return is_subregion(subregion, region, self.bridge.signature)

    def _covers(
        self,
        request: CheckRequest,
        region: Proposition,
        domain: Proposition,
    ) -> bool | None:
        """Whether `region` is proved inside `domain`.

        A kernel-built request carries the definedness service, which also
        enforces that both propositions are readable in the verification
        context.  A direct test without the service keeps the condition
        fragment fallback.
        """
        context = request.context
        if context is not None and context.definedness is not None:
            return context.definedness.covers(region, domain)
        return self._subregion(request, region.term, domain.term)

    def _claim_region(
        self, request: CheckRequest, claim: HermiteClaim
    ) -> Proposition | Unverified:
        """Issue the claim region as a proposition in the request frame.

        The region is a subterm of an already typed conclusion, so it is
        proposition-sorted; re-issuing it gives the definedness service the
        meaning key it needs without trusting the certificate.
        """
        outcome = elaborate.proposition(
            claim.region,
            self.bridge.frames,
            request.frame,
            self.bridge.signature,
        )
        if isinstance(outcome, Proposition):
            return outcome
        return Unverified(
            Reason.FRAGMENT,
            "the claim region is not a proposition in the request frame: "
            + outcome.detail,
            frozenset({"region_typing"}),
        )

    def _denominator_term(self, region: Proposition) -> T.Term | None:
        """The `D` of a single `Ne(D, 0)` proposition, or None.

        The rational bridge issues exactly one denominator-nonzero condition.
        Any other region shape is not a source denominator condition and must
        not be read as one.
        """
        term = region.term
        if not isinstance(term, T.Apply) or not isinstance(
            term.operator, T.SymbolRef
        ):
            return None
        if (
            self.bridge.signature.head_of(term.operator.symbol_id)
            is not StructuralHead.NE
        ):
            return None
        if len(term.arguments) != 2:
            return None
        left, right = term.arguments
        zero = T.number(0)
        if right == zero:
            return left
        if left == zero:
            return right
        return None

    def _source_denominator(
        self,
        regions: tuple[Proposition, ...],
        request: CheckRequest,
    ) -> Polynomial[E] | Unverified | None:
        """Convert the bridge's source denominator condition to a polynomial.

        `D` is the product of every inverse base in the source, including
        factors that the fraction field cancels, so `D != 0` is exactly the
        source's intrinsic definedness condition.  A region that is not a
        denominator-nonzero condition cannot discharge the claimed parts'
        denominators; `None` reports that no such condition exists.
        """
        for region in regions:
            term = self._denominator_term(region)
            if term is None:
                continue
            view = self._view(term, request)
            if isinstance(view, Unverified):
                return view
            value = view.value
            polynomials = self.field.polynomials
            if not polynomials.is_one(value.denominator):
                return Unverified(
                    Reason.FRAGMENT,
                    "the source denominator condition is not a polynomial",
                    frozenset({"regional_hermite_denominator"}),
                    regions,
                )
            return value.numerator
        return None

    def check(self, request: CheckRequest) -> CheckOutcome:
        algebra_mismatch = context_algebra_mismatch(
            request.context, self.request
        )
        if algebra_mismatch is not None:
            return InvalidEvidence(algebra_mismatch)
        for conclusion in request.conclusions:
            claim = parse_hermite_reduction(
                self.vocabulary, conclusion.term
            )
            if claim is None:
                return InvalidEvidence(
                    "the conclusion is not a HasHermiteReduction specification"
                )
            candidate = request.candidate
            if candidate is None:
                return InvalidEvidence(
                    "a Hermite candidate is required"
                )
            if request.candidate_role is not CandidateRole.REMAINDER:
                return InvalidEvidence(
                    "a Hermite candidate needs the remainder candidate role"
                )
            if candidate != claim.remainder:
                return InvalidEvidence(
                    "the candidate does not match the specification"
                )
            certificate = request.certificate
            if not isinstance(certificate, HermiteCertificate):
                return InvalidEvidence(
                    "a Hermite reduction certificate is required"
                )
            if not certificate_matches_claim(certificate, claim):
                return InvalidEvidence(
                    "the certificate does not match the specification"
                )
            if request.structured is not None:
                components = dict(request.structured)
                if (
                    components.get("polynomial_part")
                    != claim.polynomial_part
                    or components.get("remainder") != claim.remainder
                ):
                    return InvalidEvidence(
                        "the structured result does not match the verified "
                        "decomposition"
                    )
            mismatch = problem_mismatch(
                request,
                operations=("hermite_reduce",),
                target=claim.variable.symbol_id,
                inputs=(claim.source,),
                roles=self.request.roles,
                interpretation_requirement=(
                    self.request.interpretation_requirement
                ),
                exactness=Exactness.EXACT,
                coefficient_domain=self.request.coefficient_domain,
                value_domain=self.request.value_domain,
                # An unrestricted problem admits a conditional answer that the
                # workflow records in `result_region`; an explicitly requested
                # region must be covered by the claim.
                region=(
                    claim.region
                    if request.problem is not None
                    and request.problem.region is not None
                    else None
                ),
            )
            if mismatch is not None:
                return InvalidEvidence(mismatch)
            source_view = self._view(claim.source, request)
            if isinstance(source_view, Unverified):
                return source_view
            try:
                definedness = source_view.definedness
            except ValueError:
                # A view that bypassed the issuing factory may carry an
                # invalid raw pair; its definedness certificate cannot be
                # built.  Report that as invalid evidence, not a refutation.
                return InvalidEvidence(
                    "the representation validity region is not proved inside "
                    "the source domain"
                )
            if definedness.certificate is not None:
                if not verify_region_certificate(
                    definedness.certificate, self.bridge.signature
                ):
                    return InvalidEvidence(
                        "the definedness region certificate does not verify"
                    )
            elif (
                definedness.domain is not None
                and definedness.valid_on is not None
                and self._covers(
                    request,
                    definedness.valid_on.condition,
                    definedness.domain.condition,
                )
                is not True
            ):
                return InvalidEvidence(
                    "the representation validity region is not proved inside "
                    "the source domain"
                )
            source_domain = (
                definedness.domain.condition
                if definedness.domain is not None
                else None
            )
            valid_on = (
                definedness.valid_on.condition
                if definedness.valid_on is not None
                else None
            )
            non_total: list[Proposition] = []
            for region in (source_domain, valid_on):
                if (
                    region is not None
                    and region.term != T.TRUE
                    and region not in non_total
                ):
                    non_total.append(region)
            regions = tuple(non_total)
            if (
                claim.region == T.TRUE
                and source_domain is not None
                and source_domain.term != T.TRUE
            ):
                # The source carries a denominator-nonzero condition.  A
                # global identity on K(x) does not make the source expression
                # defined where that condition fails, so a `U = TRUE` claim is
                # not supported.
                return Unverified(
                    Reason.GUARDED,
                    "the source carries a denominator-nonzero condition, so a "
                    "global Hermite claim is not supported",
                    frozenset({"regional_hermite"}),
                    regions,
                )
            if claim.region != T.TRUE and is_empty_condition(
                claim.region, self.bridge.signature
            ):
                return Unverified(
                    Reason.GUARDED,
                    "the claim region is empty",
                    frozenset({"region_coverage"}),
                    regions,
                )
            open_regions: tuple[Proposition, ...] = ()
            if regions:
                claim_region = self._claim_region(request, claim)
                if isinstance(claim_region, Unverified):
                    return claim_region
                open_regions = tuple(
                    region
                    for region in regions
                    if self._covers(request, claim_region, region)
                    is not True
                )
            if open_regions:
                return Unverified(
                    Reason.GUARDED,
                    "the claim region is not proved inside the source regions",
                    frozenset({"region_coverage"}),
                    open_regions,
                )
            polynomial_part_view = self._view(
                claim.polynomial_part, request
            )
            if isinstance(polynomial_part_view, Unverified):
                return polynomial_part_view
            remainder_view = self._view(claim.remainder, request)
            if isinstance(remainder_view, Unverified):
                return remainder_view
            source = source_view.value
            polynomial_part = polynomial_part_view.value
            remainder = remainder_view.value
            if regions:
                polynomials = self.field.polynomials
                required: list[tuple[str, Polynomial[E]]] = []
                for name, part_view in (
                    ("polynomial part", polynomial_part_view),
                    ("remainder", remainder_view),
                ):
                    part_value = part_view.value
                    if not polynomials.is_constant(
                        part_value.denominator
                    ):
                        required.append((name, part_value.denominator))
                    part_regions: list[Proposition] = []
                    for region in (
                        part_view.source_domain,
                        part_view.valid_on,
                    ):
                        if (
                            region is not None
                            and region.term != T.TRUE
                            and region not in part_regions
                        ):
                            part_regions.append(region)
                    if part_regions:
                        part_denominator = self._source_denominator(
                            tuple(part_regions), request
                        )
                        if isinstance(part_denominator, Unverified):
                            return part_denominator
                        if part_denominator is not None and (
                            not polynomials.is_constant(part_denominator)
                        ):
                            required.append((name, part_denominator))
                if required:
                    source_denominator = self._source_denominator(
                        regions, request
                    )
                    if isinstance(source_denominator, Unverified):
                        return source_denominator
                    if source_denominator is None:
                        return Unverified(
                            Reason.GUARDED,
                            "the claimed parts have denominators, but the "
                            "source region is not a denominator-nonzero "
                            "condition",
                            frozenset({"regional_hermite_denominator"}),
                            regions,
                        )
                    for name, denominator in required:
                        try:
                            polynomials.exact_div(
                                source_denominator, denominator
                            )
                        except (TypeError, ValueError, ZeroDivisionError):
                            return Unverified(
                                Reason.GUARDED,
                                "the denominator of the claimed "
                                f"{name} does not divide the source "
                                "denominator",
                                frozenset({"regional_hermite_denominator"}),
                                regions,
                            )
            reconstructed = self.field.add(
                self.field.derivative(polynomial_part), remainder
            )
            if not self.field.equal(source, reconstructed):
                if regions or claim.region != T.TRUE:
                    # A nonzero rational function can vanish on a finite
                    # exceptional set, so a global mismatch does not refute a
                    # claim restricted to a region.
                    return Unverified(
                        Reason.FRAGMENT,
                        "the Hermite identity fails in K(x), which does not "
                        "refute a claim restricted to a region",
                        frozenset({"regional_hermite_identity"}),
                        regions,
                    )
                return Refuted(
                    conclusion,
                    (claim.source, claim.remainder),
                    "the Hermite identity does not hold",
                )
            denominator = remainder.denominator
            polynomials = self.field.polynomials
            if not polynomials.is_one(
                polynomials.gcd(
                    denominator, polynomials.derivative(denominator, 0)
                )
            ):
                return Refuted(
                    conclusion,
                    (claim.remainder,),
                    "the remainder denominator is not squarefree",
                )
        return Verified(tuple(request.conclusions))


__all__ = ["HermiteChecker"]
