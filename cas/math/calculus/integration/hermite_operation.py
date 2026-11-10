"""Registered Hermite-reduction operation.

The operation proposes the remainder `r` of `f = D(v) + r`; the certificate
carries `v` and the original `f`.  The independent `HermiteChecker` verifies the
identity and the squarefree-denominator condition.  This is not a complete
integral: the remainder is the part whose integral is not produced.

The rational bridge fixes the source's denominator-nonzero region.  When the
source has no such hole the claim keeps the existing `U = TRUE` region; when it
does, the operation states that region in the specification and certificate and
records it as the proposal's result region.  The view's intrinsic source domain
and representation validity region are both consumed: their conjunction is the
stronger region the claim and the result carry.  Regional verification itself is
still left to the checker, which defers a non-total region as `GUARDED`.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

from cas.algebra.hermite import HermiteError, hermite_reduce
from cas.foundation.ids import SymbolId
from cas.language import propositions as Pr
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.problem import expression_problem
from cas.math.calculus.integration.hermite_specification import (
    HermiteCertificate,
    HermiteVocabulary,
    has_hermite_reduction,
)
from cas.math.calculus.integration.hermite_view import HermiteView
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
    StructuredResult,
    fit_request,
    invalid_problem,
    unsupported_problem,
    unsupported_request,
)
from cas.semantics import elaborate
from cas.semantics.bridge import (
    AlgebraView,
    RenderRefused,
    ViewBuilt,
    ViewRefused,
    typed_view,
)
from cas.semantics.conditions import and_all
from cas.semantics.frames import FrameStore
from cas.syntax import term as T

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.RATIONAL_FUNCTION_FIELD}
)


@dataclass(frozen=True, slots=True)
class HermiteReductionOperation:
    """Registered problem and proposal builders for Hermite reductions."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: HermiteVocabulary
    views: tuple[HermiteView[Any], ...]
    name_of: Callable[[SymbolId], str]
    default_target: SymbolId
    id: str = "hermite_reduce"
    version: str = "1"
    problem_kind: str = "hermite_reduce"
    specification_kind: str = "HasHermiteReduction"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        if not self.views:
            raise ValueError("a Hermite operation needs an algebra view")
        targets = tuple(view.target for view in self.views)
        if len(set(targets)) != len(targets):
            raise ValueError("a target has more than one Hermite view")
        if self.default_target not in targets:
            raise ValueError("the default target has no Hermite view")
        object.__setattr__(
            self,
            "checker_bindings",
            tuple(
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    view.checker_id,
                    target=view.target,
                    candidate_role=CandidateRole.REMAINDER,
                )
                for view in self.views
            ),
        )

    def view_for(self, target: SymbolId | None) -> HermiteView[Any] | None:
        if target is None:
            return None
        for view in self.views:
            if view.target == target:
                return view
        return None

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("hermite/rational-function", self._admit_input)

    @property
    def parameter_schema(self) -> ParameterSchema[None]:
        return EMPTY_PARAMETER_SCHEMA

    @property
    def result_schema(self) -> ResultSchema:
        return ResultSchema(
            frozenset({ResultLanguage.DECOMPOSITION}),
            ResultShape.DECOMPOSITION,
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
        if view.request.parameter_mode is not ParameterMode.SPECIFIED_VALUES:
            return Refused(
                Reason.FRAGMENT,
                "Hermite reduction over a parameter family needs a "
                "coefficient fraction field",
                FragmentReport(
                    missing=frozenset({"coefficient_fraction_field"})
                ),
            )
        outcome = typed_view(
            view.bridge,
            request.inputs[0],
            self.frames,
            request.frame,
            self.signature,
            view.request,
        )
        if isinstance(outcome, ViewRefused):
            return Refused(
                outcome.reason,
                outcome.detail,
                FragmentReport(
                    missing=outcome.missing,
                    conditions=outcome.conditions,
                ),
            )
        if isinstance(outcome, AlgebraView):
            return Admitted()
        return Refused(
            Reason.FRAGMENT,
            outcome.detail,
            FragmentReport(missing=outcome.missing),
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
        if algebra is not view.request:
            return ProposalInvalid(
                "the execution algebra view is not the selected Hermite view"
            )
        source = problem.inputs[0].term
        converted = view.bridge.to_view(problem.inputs[0], view.request)
        if isinstance(converted, ViewRefused):
            return ProposalUnsupported(
                converted.reason,
                converted.detail,
                missing=converted.missing,
                conditions=converted.conditions,
            )
        if not isinstance(converted, ViewBuilt):
            return ProposalInvalid(
                "an admitted Hermite input could not be converted"
            )
        source_view = converted.view
        try:
            reduction = hermite_reduce(view.field, source_view.value)
        except HermiteError as error:
            return ProposalUnsupported(
                Reason.FRAGMENT,
                str(error),
                missing=frozenset({"hermite_reduction"}),
            )
        polynomial_part = view.bridge.render(
            source_view, reduction.polynomial_part
        )
        remainder = view.bridge.render(source_view, reduction.remainder)
        if isinstance(polynomial_part, RenderRefused):
            return ProposalUnsupported(
                polynomial_part.reason,
                polynomial_part.detail,
                missing=polynomial_part.missing,
            )
        if isinstance(remainder, RenderRefused):
            return ProposalUnsupported(
                remainder.reason,
                remainder.detail,
                missing=remainder.missing,
            )
        polynomial_part_term = polynomial_part.term
        remainder_term = remainder.term
        regions = tuple(
            item
            for item in (
                source_view.source_domain,
                source_view.valid_on,
            )
            if item is not None
        )
        region: Pr.Proposition | None
        if not regions:
            region = None
        elif all(item == regions[0] for item in regions):
            region = None if regions[0].term == T.TRUE else regions[0]
        else:
            combined = and_all(
                self.signature, *(item.term for item in regions)
            )
            if combined == T.TRUE:
                region = None
            else:
                issued_region = elaborate.proposition(
                    combined,
                    self.frames,
                    request.frame,
                    self.signature,
                )
                if not isinstance(issued_region, Pr.Proposition):
                    return ProposalInvalid(
                        "the Hermite validity region is not a proposition"
                    )
                region = issued_region
        region_term = T.TRUE if region is None else region.term
        variable_term = T.symbol(
            view.request.target, self.name_of(view.request.target)
        )
        issued = elaborate.proposition(
            has_hermite_reduction(
                self.vocabulary,
                region_term,
                source,
                variable_term,
                polynomial_part_term,
                remainder_term,
            ),
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the Hermite specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=remainder_term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=HermiteCertificate(
                    region_term,
                    source,
                    view.request.target,
                    polynomial_part_term,
                    remainder_term,
                ),
                result_region=region,
                structured=StructuredResult(
                    "HermiteReduction",
                    (
                        ("polynomial_part", polynomial_part_term),
                        ("remainder", remainder_term),
                    ),
                ),
            )
        )


__all__ = ["HermiteReductionOperation"]
