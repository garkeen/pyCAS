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
    context_algebra_mismatch,
    problem_mismatch,
)
from cas.language import typing as Ty
from cas.language.decisions import Reason
from cas.language.problems import Exactness
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.certificate import (
    Derivation,
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.checker import (
    _specialization_mismatch,
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
from cas.semantics import elaborate
from cas.semantics.conditions import is_empty_condition, is_subregion
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
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
        frames: FrameStore,
        request: AlgebraRequest,
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
        self._frames = frames
        self._request = request

    def check(self, request: CheckRequest) -> CheckOutcome:
        algebra_mismatch = context_algebra_mismatch(
            request.context, self._request
        )
        if algebra_mismatch is not None:
            return InvalidEvidence(algebra_mismatch)
        for conclusion in request.conclusions:
            typed = elaborate.typed(
                conclusion.term,
                self._frames,
                conclusion.meaning.frame,
                self._signature,
            )
            if not isinstance(typed, Ty.TypedExpr):
                return Unverified(
                    Reason.FRAGMENT,
                    typed.detail,
                    missing=typed.missing,
                )
            claim = parse_has_derivative(self._vocabulary, typed.term)
            if claim is None:
                return InvalidEvidence(
                    "the conclusion is not a HasDerivative specification"
                )
            candidate_term = request.candidate
            if candidate_term is None:
                return InvalidEvidence(
                    "a derivative candidate is required"
                )
            original_problem = request.problem
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
                return InvalidEvidence(
                    "a derivative certificate is required"
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
                # An unrestricted problem admits a conditional answer; an
                # explicitly requested region must be covered by the claim.
                region=(
                    claim.region
                    if original_problem is not None
                    and original_problem.region is not None
                    else None
                ),
            )
            if mismatch is not None:
                return InvalidEvidence(mismatch)
            if original_problem is not None:
                problem_inputs = tuple(
                    item.term for item in original_problem.inputs
                )
                if (
                    original_problem.operation == "differentiate"
                    and problem_inputs != (claim.source,)
                ):
                    return InvalidEvidence(
                        "the problem inputs do not match the specification"
                    )
                if (
                    original_problem.operation == "integrate"
                    and problem_inputs != (claim.candidate,)
                ):
                    return InvalidEvidence(
                        "the problem inputs do not match the specification"
                    )
                specialization_issue = _specialization_mismatch(
                    original_problem, certificate, claim
                )
                if specialization_issue is not None:
                    return InvalidEvidence(specialization_issue)
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
            if is_empty_condition(claim.region, self._signature):
                return Unverified(
                    Reason.GUARDED,
                    "the claimed region is empty",
                )
            if (
                is_subregion(
                    claim.region, expected_region, self._signature
                )
                is not True
            ):
                return Unverified(
                    Reason.FRAGMENT,
                    "the claimed region is not contained in the "
                    "verified differentiability region",
                )
        return Verified(tuple(request.conclusions))


__all__ = ["ElementaryDerivativeChecker"]
