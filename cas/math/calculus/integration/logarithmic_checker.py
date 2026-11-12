"""Independent checker for the `HasRationalLogAntiderivative` specification.

The checker never calls the rational-residue search
(``cas.algebra.logarithmic_integration``), Hermite reduction or factorization.
It re-elaborates every claimed term through the rational-function bridge,
rebuilds the finite logarithm-term set from the canonical encoding, and
recomputes the final identity

    source = D(polynomial_part) + sum(c_i * D(g_i)/g_i)

in ``Q(x)``.  The logarithm arguments are required to be monic, nonzero,
nonconstant, squarefree polynomials that are pairwise coprime; the claimed
visible result is rebuilt from the polynomial part and the canonical term set.

Verification order
------------------

1. The kernel-fixed algebra request must be the one this checker was built for.
2. Exactly one conclusion must parse as `HasRationalLogAntiderivative`.
3. The candidate is the claimed visible result and its role is `RESULT`.
4. The certificate is a `RationalLogAntiderivativeCertificate` matching the
   claim.
5. The structured result is exactly
   ``(("polynomial_part", part), ("log_terms", terms))``.
6. The fixed problem names operation ``integrate_rational_logarithmic``, the
   claim variable/source, the fixed roles, interpretation, exactness and the
   rational/real domain requirement.  It must request a decomposition and one
   verified result, carry no function inputs, and a restricted problem region
   must be covered by the claim region.
7. The claim region is issued as a proposition and proved nonempty.
8. The source is independently typed and admitted through the rational bridge.
   Its `Definedness` is re-verified exactly as the Hermite checker does: a
   strict validity region must carry a `SubregionCertificate`, or the context's
   definedness service (or the condition fragment) must prove the inclusion.
   Every non-total source condition is a premise of the claim.
9. The log-term set parses back to exactly the canonical encoding.  Every
   argument is admitted through the rational bridge and must be a polynomial.
   The polynomial must be monic, nonzero, nonconstant, squarefree, and the
   arguments must be pairwise coprime.  Encoding or shape violations are
   invalid evidence; an argument that is a genuinely non-polynomial rational
   function is a fragment limitation.
10. The polynomial part is independently admitted.  Its `Definedness` is
    consumed the same way; a non-total part contributes its own nonzero
    denominator conditions.
11. The visible result is rebuilt by `rational_log_antiderivative_term`; the
    claim and the candidate must both equal it.
12. The claim region must be proved inside the source and polynomial-part
    regions and inside ``Gt(g_i, 0)`` for every logarithm argument.  A
    non-total source or part never supports a global ``U = TRUE`` claim, and a
    logarithm never supports a global claim because its argument positivity is
    not a global fact in this fragment.
13. The identity is recomputed in ``K(x)``.  A failure on a fully total,
    log-free global claim is a refutation.  A failure on a restricted claim or
    on a claim with logarithm-domain conditions is only a fragment limitation:
    a nonzero rational function can vanish on an exceptional set, so it is
    reported as `Unverified`, never `Refuted`.
14. Only then is the single conclusion reported as verified.

Classification
--------------

A bridge or typing refusal is `Unverified(FRAGMENT)` with its structured
`missing`/`conditions`.  A malformed certificate, candidate, structured result,
log-term encoding, non-monic/nonconstant/non-squarefree/non-coprime argument or
duplicate coefficient is `InvalidEvidence`.  A global identity failure on a
total, log-free claim is `Refuted`.  An unproved source/part/log-domain
coverage is `Unverified(GUARDED)`.  A restricted identity failure is
`Unverified(FRAGMENT)` with ``regional_logarithmic_identity``.  The checker has
no search budget, so no `BUDGET` outcome is produced.  It publishes no
judgment; it only returns the closed `CheckOutcome`.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TypeAlias

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.algebra.rationals import RationalField
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
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    Exactness,
    ResultLanguage,
    ValueDomain,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.signatures import (
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogAntiderivativeCertificate,
    RationalLogAntiderivativeClaim,
    RationalLogVocabulary,
    certificate_matches_claim,
    parse_rational_log_antiderivative,
    parse_rational_log_terms,
    rational_log_antiderivative_term,
)
from cas.semantics import elaborate
from cas.semantics.bridge import (
    AlgebraView,
    RationalFunctionBridge,
    ViewRefused,
    typed_view,
)
from cas.semantics.conditions import and_all, is_empty_condition, is_subregion
from cas.semantics.frames import FrameStore
from cas.semantics.regions import (
    premises_proved_from,
    verify_region_certificate,
)
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

_LogValue: TypeAlias = tuple[Fraction, T.Term, Polynomial[Fraction]]

_LOG_OPERATOR = OperatorSignature((S.REAL,), S.REAL)


class LogarithmicIntegrationChecker:
    """An independent `HasRationalLogAntiderivative` checker over ``Q(x)``."""

    id = "calculus.integration.rational_logarithmic"
    version = "1"

    def __init__(
        self,
        bridge: RationalFunctionBridge[Fraction],
        signature: LanguageSignature,
        vocabulary: RationalLogVocabulary,
        frames: FrameStore,
        request: AlgebraRequest,
        *,
        identifier: str = "calculus.integration.rational_logarithmic",
    ) -> None:
        if not identifier:
            raise ValueError("a checker needs an identifier")
        if not isinstance(bridge, RationalFunctionBridge):
            raise TypeError(
                "a rational-logarithmic checker needs a rational bridge"
            )
        field: RationalFunctionField[Fraction] = bridge.field
        polynomials = field.polynomials
        if not isinstance(polynomials, UnivariatePolynomialRing):
            raise TypeError(
                "a rational-logarithmic checker needs a univariate "
                "polynomial ring"
            )
        if not isinstance(polynomials.coefficients, RationalField):
            raise TypeError(
                "a rational-logarithmic checker needs rational coefficients"
            )
        if not isinstance(signature, LanguageSignature):
            raise TypeError(
                "a rational-logarithmic checker needs a signature"
            )
        if not isinstance(vocabulary, RationalLogVocabulary):
            raise TypeError(
                "a rational-logarithmic checker needs a vocabulary"
            )
        if frames is not bridge.frames:
            raise ValueError(
                "the checker frame store is not the rational bridge's store"
            )
        if dict(signature.heads) != dict(bridge.signature.heads):
            raise ValueError(
                "the checker signature does not share the bridge's structural "
                "heads"
            )
        if dict(signature.binders) != dict(bridge.signature.binders):
            raise ValueError(
                "the checker signature does not share the bridge's binders"
            )
        if signature.head_of(vocabulary.symbol) is not None:
            raise ValueError(
                "the rational-log predicate cannot be a structural head"
            )
        declared_predicate = signature.operator_of(vocabulary.symbol)
        if declared_predicate is None:
            raise ValueError(
                "the signature does not declare the rational-log predicate"
            )
        if declared_predicate != vocabulary.signature:
            raise ValueError(
                "the signature's rational-log predicate does not match the "
                "vocabulary"
            )
        declared_log = signature.operator_of(vocabulary.log_symbol)
        if declared_log != _LOG_OPERATOR:
            raise ValueError(
                "the signature's logarithm operator does not have the "
                "declared real-to-real type"
            )
        for head in (
            StructuralHead.PLUS,
            StructuralHead.TIMES,
            StructuralHead.SET,
            StructuralHead.GT,
        ):
            if signature.symbol_of(head) is None:
                raise ValueError(
                    "the rational-log language has no "
                    f"{head.value} head"
                )
        target = request.roles.target
        if target is None:
            raise ValueError(
                "a rational-logarithmic checker needs a target request"
            )
        if target != polynomials.generators[0]:
            raise ValueError(
                "the request target is not the rational-function generator"
            )
        if request.roles.parameters or request.parameter_ring is not None:
            raise ValueError(
                "a rational-logarithmic checker cannot take formal parameters"
            )
        if request.coefficient.ring is not field.coefficients:
            raise ValueError(
                "the request coefficient structure is not the field's "
                "coefficient structure"
            )
        if request.coefficient_domain is not ValueDomain.RATIONAL:
            raise ValueError(
                "a rational-logarithmic checker needs rational coefficients"
            )
        if request.value_domain is not ValueDomain.REAL:
            raise ValueError(
                "a rational-logarithmic checker needs real values"
            )
        self.id = identifier
        self._bridge = bridge
        self._signature = signature
        self._vocabulary = vocabulary
        self._frames = frames
        self._request = request

    @property
    def field(self) -> RationalFunctionField[Fraction]:
        """The rational-function field the bridge interprets."""
        return self._bridge.field

    def _view(
        self, term: T.Term, request: CheckRequest
    ) -> AlgebraView[RationalFunction[Fraction]] | Unverified:
        """Independently elaborate and admit one claimed term."""
        outcome = typed_view(
            self._bridge,
            term,
            self._frames,
            request.frame,
            self._signature,
            self._request,
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
        fragment fallback.  The service and the fallback only prove contain-
        ment; an undecided inclusion is never read as true.

        The condition fragment normalizes one-atom comparisons, so a claimed
        region built by `and_all` may contain ``Ne(Power(x, 2), 1)`` where the
        source view records ``Ne(Plus(-1, Power(x, 2)), 0)``.  Those are the
        same condition, but the interval implication cannot prove a
        disequality from itself.  When the normal implication is undecided,
        the checker therefore also accepts a required condition that appears
        as a normalized top-level conjunct of the claim region.  Premises must
        still be proved from the claim region; this is explicit conjunction
        membership, not a new implication rule.
        """
        context = request.context
        if context is not None and context.definedness is not None:
            outcome = context.definedness.covers(region, domain)
        else:
            outcome = is_subregion(
                region.term, domain.term, self._signature
            )
        if outcome is not False:
            if outcome is True:
                return True
            if self._contains_condition(region, domain):
                return True
        return outcome

    def _conjuncts(self, term: T.Term) -> tuple[T.Term, ...]:
        """The top-level conjunction operands of a condition term."""
        if (
            isinstance(term, T.Apply)
            and isinstance(term.operator, T.SymbolRef)
            and self._signature.head_of(term.operator.symbol_id)
            is StructuralHead.AND
        ):
            out: list[T.Term] = []
            for argument in term.arguments:
                out.extend(self._conjuncts(argument))
            return tuple(out)
        return (term,)

    def _contains_condition(
        self, region: Proposition, domain: Proposition
    ) -> bool:
        """Whether `region` explicitly contains `domain` after normalization."""
        if region.meaning.world != domain.meaning.world:
            return False
        if premises_proved_from(
            region, region, self._signature
        ) is not True:
            return False
        if premises_proved_from(
            region, domain, self._signature
        ) is not True:
            return False
        normalized_region = and_all(self._signature, region.term)
        normalized_domain = and_all(self._signature, domain.term)
        return normalized_domain in self._conjuncts(normalized_region)

    def _empty(self, request: CheckRequest, term: T.Term) -> bool:
        """Whether the claim region is proved empty."""
        context = request.context
        if context is not None and context.decision is not None:
            return context.decision.is_empty(term)
        return is_empty_condition(term, self._signature)

    def _claim_region(
        self, request: CheckRequest, claim: RationalLogAntiderivativeClaim
    ) -> Proposition | Unverified:
        """Issue the claim region as a proposition in the request frame."""
        outcome = elaborate.proposition(
            claim.region,
            self._frames,
            request.frame,
            self._signature,
        )
        if isinstance(outcome, Proposition):
            return outcome
        return Unverified(
            Reason.FRAGMENT,
            "the claim region is not a proposition in the request frame: "
            + outcome.detail,
            frozenset({"region_typing"}),
        )

    def _definedness_regions(
        self,
        request: CheckRequest,
        view: AlgebraView[RationalFunction[Fraction]],
        label: str,
    ) -> tuple[Proposition, ...] | InvalidEvidence:
        """Re-verify a view's definedness and return its non-total conditions."""
        try:
            definedness = view.definedness
        except ValueError:
            return InvalidEvidence(
                f"the {label} representation validity region is not proved "
                "inside its domain"
            )
        if definedness.certificate is not None:
            if not verify_region_certificate(
                definedness.certificate, self._signature
            ):
                return InvalidEvidence(
                    f"the {label} definedness region certificate does not "
                    "verify"
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
                f"the {label} representation validity region is not proved "
                "inside its domain"
            )
        regions: list[Proposition] = []
        for region in (
            (
                definedness.domain.condition
                if definedness.domain is not None
                else None
            ),
            (
                definedness.valid_on.condition
                if definedness.valid_on is not None
                else None
            ),
        ):
            if region is not None and region.term != T.TRUE:
                if region not in regions:
                    regions.append(region)
        return tuple(regions)

    def _log_values(
        self,
        request: CheckRequest,
        claim: RationalLogAntiderivativeClaim,
    ) -> tuple[_LogValue, ...] | InvalidEvidence | Unverified:
        """Parse the canonical log-term set and admit every argument."""
        entries = parse_rational_log_terms(
            self._signature,
            self._vocabulary.log_function,
            claim.log_terms,
        )
        if entries is None:
            return InvalidEvidence(
                "the log-term set is not the canonical encoded set"
            )
        polynomials = self.field.polynomials
        values: list[_LogValue] = []
        for coefficient, argument_term in entries:
            view = self._view(argument_term, request)
            if isinstance(view, Unverified):
                return view
            if view.source.term != argument_term:
                return InvalidEvidence(
                    "an elaborated logarithm argument does not match the claim"
                )
            if (
                view.source_domain is not None
                or view.valid_on is not None
            ):
                # A polynomial argument is a total expression.  A cancelled
                # inverse still marks a hole in the source term, so the
                # logarithm would be a partial function even when the formal
                # value is a polynomial.
                return Unverified(
                    Reason.FRAGMENT,
                    "the logarithm argument is not a total polynomial "
                    "expression",
                    frozenset({"polynomial_log_argument"}),
                )
            value = view.value
            if not polynomials.is_constant(value.denominator):
                return Unverified(
                    Reason.FRAGMENT,
                    "the logarithm argument is not a polynomial",
                    frozenset({"polynomial_log_argument"}),
                )
            argument = value.numerator
            if argument.is_zero():
                return InvalidEvidence(
                    "a claimed logarithm argument is the zero polynomial"
                )
            degree = polynomials.degree(argument, 0)
            if degree < 1:
                return InvalidEvidence(
                    "a claimed logarithm argument must be nonconstant"
                )
            if not polynomials.coefficients.is_one(
                polynomials.coefficient(argument, (degree,))
            ):
                return InvalidEvidence(
                    "a claimed logarithm argument must be monic"
                )
            if not polynomials.is_one(
                polynomials.gcd(
                    argument, polynomials.derivative(argument, 0)
                )
            ):
                return InvalidEvidence(
                    "a claimed logarithm argument must be squarefree"
                )
            values.append((coefficient, argument_term, argument))
        for index, (_, _, argument) in enumerate(values):
            for _, _, other in values[index + 1 :]:
                if not polynomials.is_one(
                    polynomials.gcd(argument, other)
                ):
                    return InvalidEvidence(
                        "two claimed logarithm arguments are not coprime"
                    )
        return tuple(values)

    def _log_domain(
        self, request: CheckRequest, argument_term: T.Term
    ) -> Proposition | Unverified:
        """Issue the ``Gt(argument, 0)`` logarithm-domain condition."""
        term = T.app(
            self._signature.head_term(StructuralHead.GT),
            argument_term,
            T.number(0),
        )
        outcome = elaborate.proposition(
            term,
            self._frames,
            request.frame,
            self._signature,
        )
        if isinstance(outcome, Proposition):
            return outcome
        return Unverified(
            Reason.FRAGMENT,
            "the logarithm-domain condition is not a proposition in the "
            "request frame: " + outcome.detail,
            frozenset({"log_domain"}),
        )

    def check(self, request: CheckRequest) -> CheckOutcome:
        algebra_mismatch = context_algebra_mismatch(
            request.context, self._request
        )
        if algebra_mismatch is not None:
            return InvalidEvidence(algebra_mismatch)
        if len(request.conclusions) != 1:
            return InvalidEvidence(
                "a rational-log certificate names exactly one claim"
            )
        conclusion = request.conclusions[0]
        claim = parse_rational_log_antiderivative(
            self._vocabulary, conclusion.term
        )
        if claim is None:
            return InvalidEvidence(
                "the conclusion is not a HasRationalLogAntiderivative "
                "specification"
            )
        target = self._request.roles.target
        if target is None:
            return InvalidEvidence(
                "the checker request has no target"
            )
        if claim.variable.symbol_id != target:
            return InvalidEvidence(
                "the specification variable is not the request target"
            )
        candidate = request.candidate
        if candidate is None:
            return InvalidEvidence(
                "a rational-log antiderivative candidate is required"
            )
        if request.candidate_role is not CandidateRole.RESULT:
            return InvalidEvidence(
                "a rational-log antiderivative candidate needs the result "
                "candidate role"
            )
        if candidate != claim.result:
            return InvalidEvidence(
                "the candidate does not match the specification"
            )
        certificate = request.certificate
        if not isinstance(
            certificate, RationalLogAntiderivativeCertificate
        ):
            return InvalidEvidence(
                "a rational-log antiderivative certificate is required"
            )
        if not certificate_matches_claim(certificate, claim):
            return InvalidEvidence(
                "the certificate does not match the specification"
            )
        if request.structured != (
            ("polynomial_part", claim.polynomial_part),
            ("log_terms", claim.log_terms),
        ):
            return InvalidEvidence(
                "the structured result is not exactly the claimed polynomial "
                "part and logarithm-term set"
            )
        mismatch = problem_mismatch(
            request,
            operations=("integrate_rational_logarithmic",),
            target=claim.variable.symbol_id,
            inputs=(claim.source,),
            roles=self._request.roles,
            interpretation_requirement=(
                self._request.interpretation_requirement
            ),
            exactness=Exactness.EXACT,
            coefficient_domain=ValueDomain.RATIONAL,
            value_domain=ValueDomain.REAL,
            region=(
                claim.region
                if request.problem is not None
                and request.problem.region is not None
                else None
            ),
        )
        if mismatch is not None:
            return InvalidEvidence(mismatch)
        problem = request.problem
        if problem is not None:
            if problem.coverage is not Coverage.ONE_VERIFIED:
                return InvalidEvidence(
                    "a rational-log antiderivative requires one-verified "
                    "coverage"
                )
            if problem.result_language is not ResultLanguage.DECOMPOSITION:
                return InvalidEvidence(
                    "a rational-log antiderivative requires a decomposition "
                    "result language"
                )
            if problem.function_inputs:
                return InvalidEvidence(
                    "a rational-log antiderivative problem cannot carry "
                    "function inputs"
                )
        claim_region = self._claim_region(request, claim)
        if isinstance(claim_region, Unverified):
            return claim_region
        if claim.region != T.TRUE and self._empty(request, claim.region):
            return Unverified(
                Reason.GUARDED,
                "the claim region is empty",
                frozenset({"region_coverage"}),
            )
        source_view = self._view(claim.source, request)
        if isinstance(source_view, Unverified):
            return source_view
        if source_view.source.term != claim.source:
            return InvalidEvidence(
                "the elaborated source does not match the claim"
            )
        source_regions = self._definedness_regions(
            request, source_view, "source"
        )
        if isinstance(source_regions, InvalidEvidence):
            return source_regions
        log_values = self._log_values(request, claim)
        if isinstance(log_values, (InvalidEvidence, Unverified)):
            return log_values
        part_view = self._view(claim.polynomial_part, request)
        if isinstance(part_view, Unverified):
            return part_view
        if part_view.source.term != claim.polynomial_part:
            return InvalidEvidence(
                "the elaborated polynomial part does not match the claim"
            )
        part_regions = self._definedness_regions(
            request, part_view, "polynomial part"
        )
        if isinstance(part_regions, InvalidEvidence):
            return part_regions
        expected = rational_log_antiderivative_term(
            self._signature,
            claim.polynomial_part,
            claim.log_terms,
        )
        if claim.result != expected:
            return InvalidEvidence(
                "the claimed result is not the canonical visible "
                "antiderivative"
            )
        if candidate != expected:
            return InvalidEvidence(
                "the candidate is not the canonical visible antiderivative"
            )
        log_regions: list[Proposition] = []
        for _, argument_term, _ in log_values:
            domain = self._log_domain(request, argument_term)
            if isinstance(domain, Unverified):
                return domain
            log_regions.append(domain)
        source_or_part = tuple(source_regions) + tuple(part_regions)
        if claim.region == T.TRUE and source_or_part:
            return Unverified(
                Reason.GUARDED,
                "the source or polynomial part carries a definedness "
                "condition, so a global rational-logarithmic claim is not "
                "supported",
                frozenset({"region_coverage"}),
                source_or_part,
            )
        uncovered: list[Proposition] = []
        missing: set[str] = set()
        for region in source_regions:
            if self._covers(request, claim_region, region) is not True:
                uncovered.append(region)
                missing.add("region_coverage")
        for region in part_regions:
            if self._covers(request, claim_region, region) is not True:
                uncovered.append(region)
                missing.add("region_coverage")
        for region in log_regions:
            if self._covers(request, claim_region, region) is not True:
                uncovered.append(region)
                missing.add("log_domain")
        if uncovered:
            return Unverified(
                Reason.GUARDED,
                "the claim region is not proved inside the source, "
                "polynomial-part or logarithm domains",
                frozenset(missing),
                tuple(uncovered),
            )
        polynomials = self.field.polynomials
        total = self.field.derivative(part_view.value)
        for coefficient, _, argument in log_values:
            log_derivative = self.field.fraction(
                polynomials.mul(
                    polynomials.constant(coefficient),
                    polynomials.derivative(argument, 0),
                ),
                argument,
            )
            total = self.field.add(total, log_derivative)
        if not self.field.equal(total, source_view.value):
            conditions = tuple(
                dict.fromkeys(
                    tuple(source_regions)
                    + tuple(part_regions)
                    + tuple(log_regions)
                )
            )
            if (
                claim.region == T.TRUE
                and not source_regions
                and not part_regions
                and not log_values
            ):
                return Refuted(
                    conclusion,
                    (
                        claim.source,
                        claim.polynomial_part,
                        claim.log_terms,
                    ),
                    "the rational-logarithmic identity does not hold",
                )
            return Unverified(
                Reason.FRAGMENT,
                "the rational-logarithmic identity fails in Q(x), which does "
                "not refute a claim restricted to a region or logarithm "
                "domain",
                frozenset({"regional_logarithmic_identity"}),
                conditions,
            )
        return Verified((conclusion,))


__all__ = ["LogarithmicIntegrationChecker"]
