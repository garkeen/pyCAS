"""Registered point-specialisation of a verified derivative family.

The operation receives the source term, the verified family and exact rational
values. It either substitutes the generic formula or recomputes in the concrete
view; both paths end in a fresh `HasDerivative` specification verified by the
specialised checker.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import typing as Ty
from cas.language.problems import Coverage, ResultLanguage
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.problem import (
    derivative_specification,
    expression_problem,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
)
from cas.math.calculus.differentiation.view import SpecializationView
from cas.operations.capabilities import (
    Capability,
    CapabilityRequirements,
)
from cas.operations.protocols import (
    Admitted,
    CheckerBinding,
    ExecutionRequest,
    FragmentReport,
    GenericResultInput,
    InputAdmission,
    InputSchema,
    InvalidRequest,
    MathematicalProposal,
    OperationRequest,
    ParameterOutcome,
    ParameterSchema,
    Parsed,
    ProblemBuilt,
    ProblemOutcome,
    ProposalInvalid,
    ProposalOutcome,
    ProposalUnsupported,
    Proposed,
    Refused,
    RequestMismatch,
    ResultSchema,
    ResultShape,
    ValueMappingInput,
    fit_request,
    invalid_problem,
    unsupported_problem,
    unsupported_request,
)
from cas.semantics import elaborate
from cas.semantics.bridge import RenderRefused, ViewRefused
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.semantics.specialization import (
    Applied,
    InvalidSpecialization,
    NeedsRecomputation,
    OutsideValidity,
    Specialization,
)
from cas.semantics.specialization import specialize as specialize_family
from cas.syntax import binding as B
from cas.syntax import term as T

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.POLYNOMIAL_RING, Capability.GENERIC_RESULT}
)


@dataclass(frozen=True, slots=True)
class SpecializationParameters:
    """The parsed parameter payload of `specialize`."""

    family: GenericResultInput
    values: ValueMappingInput


def _parse_specialization_parameters(
    parameters: tuple[tuple[str, object], ...],
) -> ParameterOutcome[SpecializationParameters]:
    names = tuple(name for name, _ in parameters)
    if len(parameters) != 2 or set(names) != {"family", "values"}:
        return InvalidRequest((
            "specialize takes exactly the parameters 'family' and 'values'",
        ))
    by_name = dict(parameters)
    family = by_name["family"]
    values = by_name["values"]
    if not isinstance(family, GenericResultInput):
        return InvalidRequest((
            "the 'family' parameter must be a GenericResultInput",
        ))
    if not isinstance(values, ValueMappingInput):
        return InvalidRequest((
            "the 'values' parameter must be a ValueMappingInput",
        ))
    return Parsed(SpecializationParameters(family, values))


_SPECIALIZATION_PARAMETER_SCHEMA: ParameterSchema[
    SpecializationParameters
] = ParameterSchema(
    "specialize/exact-point",
    _parse_specialization_parameters,
)


@dataclass(frozen=True, slots=True)
class SpecializationOperation:
    """Problem and proposal builders for exact point specialisation."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: DerivativeVocabulary
    name_of: Callable[[SymbolId], str]
    view: SpecializationView
    parameter_request: AlgebraRequest
    id: str = "specialize"
    version: str = "1"
    problem_kind: str = "specialize"
    specification_kind: str = "HasDerivative"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    @property
    def variable(self) -> SymbolId:
        """The target role fixed by the specialized view."""
        return self.view.request.target

    def __post_init__(self) -> None:
        if self.view.request.target != self.parameter_request.target:
            raise ValueError(
                "the specialization view and the family request "
                "disagree about the target"
            )
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    self.view.checker.id,
                    candidate_role=CandidateRole.RESULT,
                ),
            ),
        )

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("specialize/exact-point", self._admit_input)

    @property
    def parameter_schema(
        self,
    ) -> ParameterSchema[SpecializationParameters]:
        return _SPECIALIZATION_PARAMETER_SCHEMA

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
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return parameters
        values = parameters.value.values
        try:
            specialization = Specialization(values.values)
        except (TypeError, ValueError) as error:
            return InvalidRequest((f"invalid specialization: {error}",))
        if set(specialization.values) != set(
            self.parameter_request.parameters
        ):
            return InvalidRequest((
                "a specialization must assign exactly the request parameters",
            ))
        mapping = {
            symbol: T.number(value)
            for symbol, value in specialization.values.items()
        }
        substituted = B.substitute_free(request.inputs[0], mapping)
        typed = elaborate.typed(
            substituted, self.frames, request.frame, self.signature
        )
        if not isinstance(typed, Ty.TypedExpr):
            return InvalidRequest((typed.detail,))
        outcome = self.view.bridge.to_view(typed, self.view.request)
        if isinstance(outcome, ViewRefused):
            return Refused(
                outcome.reason,
                outcome.detail,
                FragmentReport(
                    missing=outcome.missing,
                    conditions=outcome.conditions,
                ),
            )
        return Admitted()

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        result_language = self.result_schema.single_language()
        outcome = expression_problem(
            request,
            operation=self.problem_kind,
            algebra=self.view.request,
            frames=self.frames,
            signature=self.signature,
            result_language=result_language,
        )
        if not isinstance(outcome, ProblemBuilt):
            return outcome
        fit = fit_request(
            request,
            result_language=result_language,
            parameter_mode=self.view.request.parameter_mode,
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
        algebra = execution.algebra
        if algebra is None:
            return ProposalInvalid("the execution has no algebra view")
        family_input = parameters.value.family
        values_input = parameters.value.values
        source = problem.inputs[0]
        try:
            specialization = Specialization(values_input.values)
        except (TypeError, ValueError) as error:
            return ProposalInvalid(f"invalid specialization: {error}")

        outcome = specialize_family(
            family_input.result,
            self.parameter_request,
            specialization,
            self.signature,
        )
        if isinstance(outcome, InvalidSpecialization):
            return ProposalInvalid(outcome.detail)

        mapping = {
            symbol: T.number(value)
            for symbol, value in specialization.values.items()
        }
        substituted_source = B.substitute_free(source.term, mapping)
        typed_source = elaborate.typed(
            substituted_source, self.frames, request.frame, self.signature
        )
        if not isinstance(typed_source, Ty.TypedExpr):
            return ProposalInvalid(typed_source.detail)
        source_view = self.view.bridge.to_view(
            typed_source, algebra
        )
        if isinstance(source_view, ViewRefused):
            return ProposalUnsupported(
                source_view.reason,
                source_view.detail,
                missing=source_view.missing,
                conditions=source_view.conditions,
            )
        # The claim's source is the exact substitution of the generic problem
        # input.  The checker rebuilds this term from the certificate's
        # `generic_source` and `specialization` and refuses any other text.
        specialized_source = substituted_source
        source_value = source_view.view.value

        if isinstance(outcome, Applied):
            applied_source = elaborate.typed(
                outcome.result, self.frames, request.frame, self.signature
            )
            if not isinstance(applied_source, Ty.TypedExpr):
                return ProposalInvalid(applied_source.detail)
            applied_view = self.view.bridge.to_view(
                applied_source, algebra
            )
            if isinstance(applied_view, ViewRefused):
                return ProposalInvalid(
                    "the specialized generic formula is outside the "
                    f"specialized view: {applied_view.detail}"
                )
            candidate_view = applied_view.view
            candidate_value = candidate_view.value
            trace = ("generic_formula",)
        elif isinstance(outcome, (NeedsRecomputation, OutsideValidity)):
            candidate_view = source_view.view
            candidate_value = self.view.differential.deriv(source_value)
            trace = ("recomputed",)
        else:
            raise TypeError(
                f"unknown specialization outcome: {type(outcome).__name__}"
            )
        rendered_candidate = self.view.bridge.render(
            candidate_view, candidate_value
        )
        if isinstance(rendered_candidate, RenderRefused):
            return ProposalInvalid(
                "the specialized derivative cannot be rendered: "
                f"{rendered_candidate.detail}"
            )
        candidate_term = rendered_candidate.term

        issued = derivative_specification(
            self.vocabulary,
            T.TRUE,
            specialized_source,
            self.variable,
            candidate_term,
            frames=self.frames,
            frame=request.frame,
            signature=self.signature,
            name_of=self.name_of,
        )
        if issued is None:
            return ProposalInvalid(
                "the specialized specification is not a proposition"
            )

        return Proposed(
            MathematicalProposal(
                result=candidate_term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=DerivativeCertificate(
                    T.TRUE,
                    specialized_source,
                    self.variable,
                    candidate_term,
                    generic_source=source.term,
                    specialization=specialization,
                ),
                trace=trace,
            )
        )


__all__ = ["SpecializationOperation"]
