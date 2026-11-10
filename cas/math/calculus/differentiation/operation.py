"""The registered differentiation operation.

The workflow does not know `HasDerivative`, the derivative certificate or the
shape of a differentiability region. This module owns all of that and returns a
`MathematicalProposal`, which the workflow commits through the declared checker
binding.

The target is request-local: the operation owns one pre-assembled
`DifferentiationView` per admitted target and selects it from
`OperationRequest.target`.  It never reads a global variable or rewrites a
previous view.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

from cas.foundation.ids import SymbolId
from cas.language import propositions as Pr
from cas.language import typing as Ty
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.problem import (
    derivative_specification,
    expression_problem,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
)
from cas.math.calculus.differentiation.view import DifferentiationView
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
from cas.semantics.conditions import is_empty_condition, is_subregion
from cas.semantics.frames import FrameStore
from cas.semantics.regions import region_from_proposition
from cas.semantics.services import (
    DerivationInvalid,
    DerivationUnsupported,
    Derived,
)
from cas.semantics.specialization import coverage_claim
from cas.syntax import term as T

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.POLYNOMIAL_RING}
)


@dataclass(frozen=True, slots=True)
class DifferentiationOperation:
    """Registered problem and proposal builders for derivative claims."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: DerivativeVocabulary
    views: tuple[DifferentiationView[Any], ...]
    name_of: Callable[[SymbolId], str]
    default_target: SymbolId
    id: str = "differentiate"
    version: str = "1"
    problem_kind: str = "differentiate"
    specification_kind: str = "HasDerivative"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        if not self.views:
            raise ValueError("a differentiation operation needs an algebra view")
        targets = tuple(view.target for view in self.views)
        if len(set(targets)) != len(targets):
            raise ValueError("a target has more than one differentiation view")
        if self.default_target not in targets:
            raise ValueError("the default target has no differentiation view")
        for view in self.views:
            if view.service.specification_kind != self.specification_kind:
                raise ValueError(
                    "a derivative service reports another specification kind"
                )
        object.__setattr__(
            self,
            "checker_bindings",
            tuple(
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    view.service.checker_id,
                    target=view.target,
                    candidate_role=CandidateRole.RESULT,
                )
                for view in self.views
            ),
        )

    def view_for(self, target: SymbolId | None) -> DifferentiationView[Any] | None:
        """The view that fixes `target`, or None when the target is not admitted."""
        if target is None:
            return None
        for view in self.views:
            if view.target == target:
                return view
        return None

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema(
            "differentiate/elementary-or-polynomial", self._admit_input
        )

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
        view = self.view_for(request.target)
        if view is None:
            return Refused(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                FragmentReport(missing=frozenset({"target_view"})),
            )
        source = elaborate.typed(
            request.inputs[0], self.frames, request.frame, self.signature
        )
        if not isinstance(source, Ty.TypedExpr):
            return InvalidRequest((source.detail,))
        issue = view.service.supports(source, view.request)
        if issue is None:
            return Admitted()
        missing = (
            frozenset({"derivative_rule"})
            if issue.reason is Reason.FRAGMENT
            else issue.missing
        )
        return Refused(
            issue.reason,
            issue.detail,
            FragmentReport(missing=missing, conditions=issue.conditions),
        )

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        view = self.view_for(request.target)
        if view is None:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                missing=frozenset({"target_view"}),
            )
        result_language = self.result_schema.single_language()
        outcome = expression_problem(
            request,
            operation=self.problem_kind,
            algebra=view.request,
            frames=self.frames,
            signature=self.signature,
            result_language=result_language,
        )
        if not isinstance(outcome, ProblemBuilt):
            return outcome
        fit = fit_request(
            request,
            result_language=result_language,
            parameter_mode=view.request.parameter_mode,
            coverages=frozenset({Coverage.ONE_VERIFIED}),
        )
        if isinstance(fit, RequestMismatch):
            return unsupported_request(fit, outcome.problem)
        admission = self.input_schema.admit(request)
        if isinstance(admission, Refused):
            return unsupported_problem(admission, outcome.problem)
        if isinstance(admission, InvalidRequest):
            return invalid_problem(admission)
        return outcome

    def propose(
        self,
        execution: ExecutionRequest,
    ) -> ProposalOutcome:
        request = execution.request
        problem = execution.problem
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return ProposalInvalid("; ".join(parameters.issues))
        view = self.view_for(request.target)
        if view is None:
            return ProposalUnsupported(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                missing=frozenset({"target_view"}),
            )
        algebra = execution.algebra
        if algebra is None:
            return ProposalInvalid("the execution has no algebra view")
        source = problem.inputs[0]
        derivation = view.service.candidate(source, algebra)
        if isinstance(derivation, DerivationUnsupported):
            missing = derivation.missing
            if not missing and derivation.reason is Reason.FRAGMENT:
                missing = frozenset({"derivative_rule"})
            return ProposalUnsupported(
                derivation.reason,
                derivation.detail,
                missing=missing,
                conditions=derivation.conditions,
            )
        if isinstance(derivation, DerivationInvalid):
            return ProposalInvalid(derivation.detail)
        if not isinstance(derivation, Derived):
            raise TypeError(
                f"unknown derivation outcome: {type(derivation).__name__}"
            )

        condition: Pr.Proposition | None = None
        if derivation.condition is not None:
            region_outcome = elaborate.proposition(
                derivation.condition,
                self.frames,
                request.frame,
                self.signature,
            )
            if not isinstance(region_outcome, Pr.Proposition):
                return ProposalInvalid(
                    "the differentiability region is not a proposition"
                )
            condition = region_outcome
        verified_region = T.TRUE if condition is None else condition.term

        requested = problem.region
        if requested is None:
            result_region = condition
        else:
            if is_empty_condition(requested.term, self.signature):
                return ProposalUnsupported(
                    Reason.GUARDED,
                    "the requested region is empty",
                    missing=frozenset({"nonempty_region"}),
                    conditions=(requested,),
                )
            covered = is_subregion(
                requested.term, verified_region, self.signature
            )
            if covered is not True:
                return ProposalUnsupported(
                    Reason.GUARDED,
                    "the requested region is not covered by the "
                    "derivative region",
                    missing=frozenset({"region_coverage"}),
                    conditions=(requested,),
                )
            result_region = None if requested.term == T.TRUE else requested

        specification_region = (
            T.TRUE if result_region is None else result_region.term
        )
        issued = derivative_specification(
            self.vocabulary,
            specification_region,
            source.term,
            view.request.target,
            derivation.term,
            frames=self.frames,
            frame=request.frame,
            signature=self.signature,
            name_of=self.name_of,
        )
        if issued is None:
            return ProposalInvalid(
                "the derivative specification is not a proposition"
            )

        coverage = None
        valid_on = None
        if view.request.parameter_mode is not ParameterMode.SPECIFIED_VALUES:
            if condition is not None:
                valid_on = condition
            else:
                true_region = elaborate.proposition(
                    T.TRUE,
                    self.frames,
                    request.frame,
                    self.signature,
                )
                if not isinstance(true_region, Pr.Proposition):
                    return ProposalInvalid(
                        "the validity region is not a proposition"
                    )
                valid_on = true_region
            coverage = coverage_claim(
                view.request.parameter_mode,
                region_from_proposition(valid_on),
                (),
            )

        return Proposed(
            MathematicalProposal(
                result=derivation.term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=view.service.certificate(
                    specification_region,
                    source.term,
                    view.request.target,
                    derivation,
                ),
                result_region=result_region,
                coverage=coverage,
                valid_on=valid_on,
            )
        )


__all__ = ["DifferentiationOperation"]
