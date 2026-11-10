"""Registered resultant operation for univariate polynomials over Q.

The typed problem inputs are the mathematical source.  `propose` admits each
of them through the pre-assembled algebra bridge, computes the resultant on
the parent elements and renders the exact rational value as a term.  A refused
view is a structured fragment refusal with the missing capability.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction

from cas.algebra.polynomial import UnivariatePolynomialRing
from cas.foundation.ids import SymbolId
from cas.language import propositions as Pr
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.algebra.resultant_specification import (
    ResultantCertificate,
    ResultantVocabulary,
    has_resultant,
)
from cas.operations.capabilities import (
    Capability,
    CapabilityRequirements,
)
from cas.operations.parameters import EMPTY_PARAMETER_SCHEMA
from cas.operations.protocols import (
    Admitted,
    CheckerBinding,
    ExecutionRequest,
    FragmentReport,
    InputAdmission,
    InputSchema,
    InvalidRequest,
    MathematicalProposal,
    OperationRequest,
    ParameterSchema,
    ProblemBuilt,
    ProblemInvalid,
    ProblemOutcome,
    ProblemUnsupported,
    ProposalInvalid,
    ProposalOutcome,
    ProposalUnsupported,
    Proposed,
    Refused,
    RequestMismatch,
    ResultSchema,
    ResultShape,
    fit_request,
    invalid_problem,
    unsupported_problem,
    unsupported_request,
)
from cas.semantics import elaborate
from cas.semantics.bridge import PolynomialBridge, ViewRefused
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

_FRAGMENT = frozenset({"univariate_polynomial_representation"})

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.POLYNOMIAL_RING}
)


@dataclass(frozen=True, slots=True)
class ResultantOperation:
    """Registered problem and proposal builder for resultants."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: ResultantVocabulary
    checker_id: str
    ring: UnivariatePolynomialRing[Fraction]
    bridge: PolynomialBridge[Fraction]
    name_of: Callable[[SymbolId], str]
    request: AlgebraRequest
    id: str = "resultant"
    version: str = "1"
    problem_kind: str = "resultant"
    specification_kind: str = "HasResultant"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        if self.ring is not self.bridge.ring:
            raise ValueError("the resultant ring is not the bridge's ring")
        if self.ring.generators != (self.request.target,):
            raise ValueError(
                "the request target is not the resultant ring's generator"
            )
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    self.checker_id,
                    candidate_role=CandidateRole.RESULT,
                ),
            ),
        )

    @property
    def target(self) -> SymbolId:
        """The target role fixed by the operation's request."""
        return self.request.target

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("resultant/univariate-q", self._admit_input)

    @property
    def parameter_schema(self) -> ParameterSchema[None]:
        return EMPTY_PARAMETER_SCHEMA

    @property
    def result_schema(self) -> ResultSchema:
        return ResultSchema(
            frozenset({ResultLanguage.EXPRESSION}),
            ResultShape.EXPRESSION,
        )

    @property
    def capability_requirements(self) -> frozenset[Capability]:
        return _CAPABILITY_REQUIREMENTS

    def _admit_input(self, request: OperationRequest) -> InputAdmission:
        typed_inputs = elaborate.typed_inputs(
            request.inputs,
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(typed_inputs, tuple):
            return InvalidRequest((typed_inputs.detail,))
        for typed in typed_inputs:
            outcome = self.bridge.to_view(typed, self.request)
            if isinstance(outcome, ViewRefused):
                missing = outcome.missing
                if outcome.reason is Reason.FRAGMENT:
                    missing = missing | _FRAGMENT
                return Refused(
                    outcome.reason,
                    outcome.detail,
                    FragmentReport(
                        missing=missing, conditions=outcome.conditions
                    ),
                )
        return Admitted()

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        if len(request.inputs) != 2:
            return ProblemInvalid("resultant takes two inputs")
        if request.target is None:
            return ProblemInvalid("resultant needs a target variable")
        if request.target != self.request.target:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                missing=frozenset({"target_view"}),
            )
        if request.region is not None:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "resultant has no restricted-region form",
                missing=frozenset({"restricted_region"}),
            )
        typed_inputs = elaborate.typed_inputs(
            request.inputs,
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(typed_inputs, tuple):
            return ProblemInvalid(typed_inputs.detail)
        result_language = self.result_schema.single_language()
        problem = ProblemSpec(
            operation=self.problem_kind,
            inputs=typed_inputs,
            roles=self.request.roles,
            region=None,
            result_language=result_language,
            coverage=Coverage.ONE_VERIFIED,
            interpretation_requirement=(
                self.request.interpretation_requirement
            ),
            domain_requirement=DomainRequirement(
                coefficient=self.request.coefficient_domain,
                values=self.request.value_domain,
            ),
        )
        fit = fit_request(
            request,
            result_language=result_language,
            parameter_mode=self.request.parameter_mode,
            coverages=frozenset({Coverage.ONE_VERIFIED}),
        )
        if isinstance(fit, RequestMismatch):
            return unsupported_request(fit, problem)
        admission = self.input_schema.admit(request)
        if isinstance(admission, Refused):
            return unsupported_problem(admission, problem)
        if isinstance(admission, InvalidRequest):
            return invalid_problem(admission)
        return ProblemBuilt(problem, algebra=self.request)

    def propose(
        self,
        execution: ExecutionRequest,
    ) -> ProposalOutcome:
        request = execution.request
        problem = execution.problem
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return ProposalInvalid("; ".join(parameters.issues))
        algebra = execution.algebra
        if algebra is None:
            return ProposalInvalid("the execution has no algebra view")
        left_typed, right_typed = problem.inputs
        left_outcome = self.bridge.to_view(left_typed, algebra)
        if isinstance(left_outcome, ViewRefused):
            return ProposalUnsupported(
                left_outcome.reason,
                left_outcome.detail,
                missing=left_outcome.missing,
                conditions=left_outcome.conditions,
            )
        right_outcome = self.bridge.to_view(right_typed, algebra)
        if isinstance(right_outcome, ViewRefused):
            return ProposalUnsupported(
                right_outcome.reason,
                right_outcome.detail,
                missing=right_outcome.missing,
                conditions=right_outcome.conditions,
            )
        left_view = left_outcome.view
        right_view = right_outcome.view
        value = self.ring.resultant(left_view.value, right_view.value)
        result = T.number(value)
        left_term = left_view.source.term
        right_term = right_view.source.term
        variable_term = T.symbol(
            self.target, self.name_of(self.target)
        )
        issued = elaborate.proposition(
            has_resultant(
                self.vocabulary,
                left_term,
                right_term,
                variable_term,
                result,
            ),
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the resultant specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=result,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=ResultantCertificate(
                    left_term,
                    right_term,
                    self.target,
                    result,
                ),
            )
        )


__all__ = ["ResultantOperation"]
