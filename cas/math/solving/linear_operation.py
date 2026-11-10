"""Registered finite-set solver for one linear polynomial over Q.

The operation computes the unique root (or the empty set for a nonzero
constant) and proposes the set as the visible result.  Completeness is claimed
only for degree at most one; the zero polynomial is refused because its
solution set is all reals, outside the finite-set fragment.  The independent
`LinearSolutionChecker` verifies both soundness and, where claimed, completeness.

The typed problem input is the mathematical source.  `propose` admits it
through the pre-assembled algebra bridge; a refused view is a structured
fragment refusal with the missing capability, never a silent absence.
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
from cas.language.sets import set_term
from cas.language.signatures import LanguageSignature
from cas.math.solving.linear_specification import (
    LinearSolutionCertificate,
    SolutionSetVocabulary,
    has_solution_set,
    has_solution_subset,
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

_FRAGMENT = frozenset({"polynomial_representation"})

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.POLYNOMIAL_RING, Capability.FIELD}
)


@dataclass(frozen=True, slots=True)
class LinearSolveOperation:
    """Registered problem and proposal builder for finite solution sets."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: SolutionSetVocabulary
    checker_id: str
    ring: UnivariatePolynomialRing[Fraction]
    bridge: PolynomialBridge[Fraction]
    name_of: Callable[[SymbolId], str]
    request: AlgebraRequest
    id: str = "solve_linear"
    version: str = "1"
    problem_kind: str = "solve_linear"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        if self.ring is not self.bridge.ring:
            raise ValueError("the linear-solver ring is not the bridge's ring")
        if self.ring.generators != (self.request.target,):
            raise ValueError(
                "the request target is not the linear-solver ring's generator"
            )
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    "HasSolutionSet",
                    self.problem_kind,
                    self.checker_id,
                    candidate_role=CandidateRole.SET,
                ),
                CheckerBinding(
                    "HasSolutionSubset",
                    self.problem_kind,
                    self.checker_id,
                    candidate_role=CandidateRole.SET,
                ),
            ),
        )

    @property
    def target(self) -> SymbolId:
        """The target role fixed by the operation's request."""
        return self.request.target

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("solve_linear/finite-set-q", self._admit_input)

    @property
    def parameter_schema(self) -> ParameterSchema[None]:
        return EMPTY_PARAMETER_SCHEMA

    @property
    def result_schema(self) -> ResultSchema:
        return ResultSchema(
            frozenset({ResultLanguage.SET}),
            ResultShape.SET,
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
        outcome = self.bridge.to_view(typed_inputs[0], self.request)
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
        value = outcome.view.value
        coverage = request.coverage
        if coverage is Coverage.COMPLETE_SET:
            if value.is_zero():
                return Refused(
                    Reason.FRAGMENT,
                    "the zero polynomial has all reals as its solution set, "
                    "outside the finite-set fragment",
                    FragmentReport(missing=frozenset({"finite_solution_set"})),
                )
            if self.ring.degree(value, 0) > 1:
                return Refused(
                    Reason.FRAGMENT,
                    "only linear and constant polynomials have a complete "
                    "finite solution set in this fragment",
                    FragmentReport(
                        missing=frozenset({"linear_complete_solver"})
                    ),
                )
        return Admitted()

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        if len(request.inputs) != 1:
            return ProblemInvalid("solve_linear takes one input")
        if request.target is None:
            return ProblemInvalid("solve_linear needs a target variable")
        if request.target != self.request.target:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                missing=frozenset({"target_view"}),
            )
        if request.region is not None:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "solving on a restricted region is not implemented",
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
            coverage=request.coverage,
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
            coverages=frozenset(
                {Coverage.SOUND_SET, Coverage.COMPLETE_SET}
            ),
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
        outcome = self.bridge.to_view(problem.inputs[0], algebra)
        if isinstance(outcome, ViewRefused):
            return ProposalUnsupported(
                outcome.reason,
                outcome.detail,
                missing=outcome.missing,
                conditions=outcome.conditions,
            )
        view = outcome.view
        source = view.source.term
        value = view.value
        degree = self.ring.degree(value, 0) if not value.is_zero() else -1
        members: tuple[T.Term, ...] = ()
        if degree == 1:
            constant = self.ring.coefficient(value, (0,))
            leading = self.ring.coefficient(value, (1,))
            root = self.ring.coefficients.neg(
                self.ring.coefficients.div(constant, leading)
            )
            members = (T.number(root),)
        result = set_term(self.signature, members)
        variable_term = T.symbol(
            self.target, self.name_of(self.target)
        )
        if problem.coverage is Coverage.COMPLETE_SET:
            specification = has_solution_set(
                self.vocabulary, source, variable_term, result
            )
            specification_kind = "HasSolutionSet"
        else:
            specification = has_solution_subset(
                self.vocabulary, source, variable_term, result
            )
            specification_kind = "HasSolutionSubset"
        issued = elaborate.proposition(
            specification,
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the solution-set specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=result,
                specifications=(issued,),
                specification_kind=specification_kind,
                certificate=LinearSolutionCertificate(
                    source, self.target, result, problem.coverage
                ),
                answer_coverage=problem.coverage,
            )
        )


__all__ = ["LinearSolveOperation"]
