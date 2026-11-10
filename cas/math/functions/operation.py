"""Registered explicit function extension.

Extending a partial function is not a silent data edit.  The operation fixes a
problem, proposes the new representation as the visible result, and asks the
independent `FunctionEqualityChecker` to prove `EqualOn(old_domain, old, new)`.
Only after that judgment is committed does the workspace record the new
function version.

The enlarged intrinsic domain is a user declaration.  The checker proves the
new representation agrees with the old function on the old domain; it does not
pretend to prove that the enlarged domain is the true maximal domain.  The
operation also requires a `CoversCertificate` showing that the new value's
representations cover its declared intrinsic domain.  That certificate is a
representational obligation, not a proof of the values outside the old domain.

Every domain and representation check uses `proved_subregion`: a condition is
admitted only when its own definedness premises and the target's premises are
proved.  `FunctionValue` records total conditions in this batch, so a partial
new domain or representation region is refused with a structured
`ProposalUnsupported` instead of constructing a value whose premises later
consumers would ignore.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.functions import same_parameter_signature
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
    VariableRoles,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import LanguageSignature
from cas.math.functions.equality import (
    FunctionEqualityCertificate,
    FunctionEqualityVocabulary,
    equal_on,
    function_coverage_certificate,
    function_coverage_regions,
    same_partial_function,
)
from cas.operations.capabilities import (
    Capability,
    CapabilityRequirements,
)
from cas.operations.protocols import (
    Admitted,
    CheckerBinding,
    ExecutionRequest,
    FragmentReport,
    FunctionComparisonInput,
    FunctionExtensionInput,
    InputAdmission,
    InputSchema,
    InvalidRequest,
    MathematicalProposal,
    OperationRequest,
    ParameterOutcome,
    ParameterSchema,
    Parsed,
    ProblemBuilt,
    ProblemInvalid,
    ProblemOutcome,
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
from cas.semantics.frames import FrameStore
from cas.semantics.regions import proved_subregion
from cas.syntax import term as T

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.FUNCTION_VALUE}
)


@dataclass(frozen=True, slots=True)
class ExtensionParameters:
    """The parsed parameter payload of `extend_function`."""

    extension: FunctionExtensionInput


def _parse_extension_parameters(
    parameters: tuple[tuple[str, object], ...],
) -> ParameterOutcome[ExtensionParameters]:
    if len(parameters) != 1 or parameters[0][0] != "extension":
        return InvalidRequest(
            ("extend_function takes exactly one parameter named 'extension'",)
        )
    extension = parameters[0][1]
    if not isinstance(extension, FunctionExtensionInput):
        return InvalidRequest((
            "the 'extension' parameter must be a FunctionExtensionInput",
        ))
    return Parsed(ExtensionParameters(extension))


_EXTENSION_PARAMETER_SCHEMA: ParameterSchema[ExtensionParameters] = (
    ParameterSchema("extend_function/extension", _parse_extension_parameters)
)


@dataclass(frozen=True, slots=True)
class ComparisonParameters:
    """The parsed parameter payload of `compare_functions`."""

    comparison: FunctionComparisonInput


def _parse_comparison_parameters(
    parameters: tuple[tuple[str, object], ...],
) -> ParameterOutcome[ComparisonParameters]:
    if len(parameters) != 1 or parameters[0][0] != "comparison":
        return InvalidRequest((
            "compare_functions takes exactly one parameter named "
            "'comparison'",
        ))
    comparison = parameters[0][1]
    if not isinstance(comparison, FunctionComparisonInput):
        return InvalidRequest((
            "the 'comparison' parameter must be a FunctionComparisonInput",
        ))
    return Parsed(ComparisonParameters(comparison))


_COMPARISON_PARAMETER_SCHEMA: ParameterSchema[ComparisonParameters] = (
    ParameterSchema(
        "compare_functions/comparison", _parse_comparison_parameters
    )
)


@dataclass(frozen=True, slots=True)
class FunctionExtensionOperation:
    """Registered problem and proposal builder for one function extension."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: FunctionEqualityVocabulary
    checker_id: str
    roles: VariableRoles
    id: str = "extend_function"
    version: str = "1"
    problem_kind: str = "extend_function"
    specification_kind: str = "EqualOn"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    self.checker_id,
                    candidate_role=CandidateRole.RIGHT,
                ),
            ),
        )

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("extend_function/equal-on", self._admit_input)

    @property
    def parameter_schema(self) -> ParameterSchema[ExtensionParameters]:
        return _EXTENSION_PARAMETER_SCHEMA

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
        outcome = self.parameter_schema.parse(request.parameters)
        if isinstance(outcome, InvalidRequest):
            return outcome
        extension = outcome.value.extension
        if not extension.value.result_sort.embeds_into(S.REAL):
            return Refused(
                Reason.FRAGMENT,
                "function equality is stated for real-valued functions",
                FragmentReport(missing=frozenset({"real_valued_function"})),
            )
        return Admitted()

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        extension = parameters.value.extension
        if len(request.inputs) != 2:
            return ProblemInvalid("extend_function takes two representations")
        if request.target is not None:
            return ProblemInvalid("extend_function has no target variable")
        if request.region is not None:
            return ProblemInvalid(
                "extend_function states its regions in the extension input"
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
            roles=self.roles,
            region=None,
            result_language=result_language,
            coverage=Coverage.ONE_VERIFIED,
            function_inputs=(extension.value,),
            domain_requirement=DomainRequirement(
                coefficient=None, values=ValueDomain.REAL
            ),
        )
        fit = fit_request(
            request,
            result_language=result_language,
            parameter_mode=self.roles.parameter_mode,
            coverages=frozenset({Coverage.ONE_VERIFIED}),
        )
        if isinstance(fit, RequestMismatch):
            return unsupported_request(fit, problem)
        admission = self.input_schema.admit(request)
        if isinstance(admission, Refused):
            return unsupported_problem(admission, problem)
        if isinstance(admission, InvalidRequest):
            return invalid_problem(admission)
        return ProblemBuilt(problem, algebra=None)

    def propose(
        self,
        execution: ExecutionRequest,
    ) -> ProposalOutcome:
        request = execution.request
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return ProposalInvalid("; ".join(parameters.issues))
        extension = parameters.value.extension
        value = extension.value
        if not value.result_sort.embeds_into(S.REAL):
            return ProposalInvalid(
                "an admitted function extension is not real-valued"
            )
        old_term, new_term = request.inputs
        old_index = value.representation_index_of(old_term)
        if old_index is None:
            return ProposalInvalid(
                "the first input is not a representation of the function"
            )
        old_domain = value.intrinsic_domain
        if (
            proved_subregion(
                old_domain, extension.domain, self.signature
            )
            is not True
        ):
            return ProposalInvalid(
                "the new intrinsic domain does not contain the old domain"
            )
        if (
            proved_subregion(
                extension.valid_on,
                extension.domain,
                self.signature,
            )
            is not True
        ):
            return ProposalInvalid(
                "the new representation region is not inside the new domain"
            )
        for representation in value.representations:
            if (
                proved_subregion(
                    representation.valid_on,
                    extension.domain,
                    self.signature,
                )
                is not True
            ):
                return ProposalInvalid(
                    "an existing representation is outside the new domain"
                )
        # A `FunctionValue` records total domain and representation
        # conditions in this batch; the workspace, the checker and the coverage
        # helper all read their terms.  A partial condition would be silently
        # stripped by those consumers, so the extension is refused instead of
        # constructing a value whose premises no later consumer accounts for.
        partial = tuple(
            premise
            for region in (extension.domain, extension.valid_on)
            for premise in region.definedness
        )
        if partial:
            return ProposalUnsupported(
                Reason.GUARDED,
                "the extension would record a partial function region; "
                "domain and representation conditions must be total in this "
                "batch",
                missing=frozenset({"function_region_premises"}),
                conditions=partial,
            )
        new_value = value.extended(
            extension.domain, new_term, extension.valid_on
        )
        coverage = function_coverage_certificate(
            new_value, self.signature
        )
        if coverage is None:
            _, pieces = function_coverage_regions(new_value)
            return ProposalUnsupported(
                Reason.GUARDED,
                "the new intrinsic domain is not covered by the function "
                "representations",
                missing=frozenset({"representation_coverage"}),
                conditions=tuple(
                    region.condition for region in pieces
                ),
            )
        issued = elaborate.proposition(
            equal_on(
                self.vocabulary,
                old_domain.term,
                old_term,
                new_term,
            ),
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the extension specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=new_term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=FunctionEqualityCertificate(
                    old_domain.term,
                    value,
                    new_value,
                    old_index,
                    len(new_value.representations) - 1,
                    coverage=coverage,
                ),
            )
        )


@dataclass(frozen=True, slots=True)
class FunctionComparisonOperation:
    """Prove `EqualOn` or `SamePartialFunction` for two explicit values.

    With a request region the operation asks for `EqualOn`; without one it asks
    for full partial-function equality.  The visible result is the proved
    specification itself, so the workflow records a proposition result.
    """

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: FunctionEqualityVocabulary
    checker_id: str
    roles: VariableRoles
    id: str = "compare_functions"
    version: str = "1"
    problem_kind: str = "compare_functions"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    "EqualOn",
                    self.problem_kind,
                    self.checker_id,
                    candidate_role=CandidateRole.CONCLUSION,
                ),
                CheckerBinding(
                    "SamePartialFunction",
                    self.problem_kind,
                    self.checker_id,
                    candidate_role=CandidateRole.CONCLUSION,
                ),
            ),
        )

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("compare_functions/equality", self._admit_input)

    @property
    def parameter_schema(self) -> ParameterSchema[ComparisonParameters]:
        return _COMPARISON_PARAMETER_SCHEMA

    @property
    def result_schema(self) -> ResultSchema:
        return ResultSchema(
            frozenset({ResultLanguage.PROPOSITION}),
            ResultShape.PROPOSITION,
        )

    @property
    def capability_requirements(self) -> frozenset[Capability]:
        return _CAPABILITY_REQUIREMENTS

    def _admit_input(self, request: OperationRequest) -> InputAdmission:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return parameters
        comparison = parameters.value.comparison
        if not same_parameter_signature(comparison.left, comparison.right):
            return Refused(
                Reason.FRAGMENT,
                "the functions have different parameter signatures",
                FragmentReport(missing=frozenset({"parameter_signature"})),
            )
        return Admitted()

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        comparison = parameters.value.comparison
        if len(request.inputs) != 2:
            return ProblemInvalid("compare_functions takes two representations")
        if request.target is not None:
            return ProblemInvalid("compare_functions has no target variable")
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
            roles=self.roles,
            region=request.region,
            result_language=result_language,
            coverage=Coverage.ONE_VERIFIED,
            function_inputs=(comparison.left, comparison.right),
            domain_requirement=DomainRequirement(
                coefficient=None, values=ValueDomain.REAL
            ),
        )
        fit = fit_request(
            request,
            result_language=result_language,
            parameter_mode=self.roles.parameter_mode,
            coverages=frozenset({Coverage.ONE_VERIFIED}),
        )
        if isinstance(fit, RequestMismatch):
            return unsupported_request(fit, problem)
        admission = self.input_schema.admit(request)
        if isinstance(admission, Refused):
            return unsupported_problem(admission, problem)
        if isinstance(admission, InvalidRequest):
            return invalid_problem(admission)
        return ProblemBuilt(problem, algebra=None)

    def propose(
        self,
        execution: ExecutionRequest,
    ) -> ProposalOutcome:
        request = execution.request
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return ProposalInvalid("; ".join(parameters.issues))
        comparison = parameters.value.comparison
        left_term, right_term = request.inputs
        left_representation = comparison.left.representations[
            comparison.left_index
        ]
        right_representation = comparison.right.representations[
            comparison.right_index
        ]
        if (
            left_representation.term != left_term
            or right_representation.term != right_term
        ):
            return ProposalInvalid(
                "the comparison indices do not name the requested terms"
            )
        if request.region is not None:
            specification = equal_on(
                self.vocabulary,
                request.region.term,
                left_term,
                right_term,
            )
            kind = "EqualOn"
            certificate_region: T.Term | None = request.region.term
        else:
            specification = same_partial_function(
                self.vocabulary, left_term, right_term
            )
            kind = "SamePartialFunction"
            certificate_region = None
        issued = elaborate.proposition(
            specification,
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the function-comparison specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=issued.term,
                specifications=(issued,),
                specification_kind=kind,
                certificate=FunctionEqualityCertificate(
                    certificate_region,
                    comparison.left,
                    comparison.right,
                    comparison.left_index,
                    comparison.right_index,
                ),
            )
        )


__all__ = [
    "FunctionComparisonOperation",
    "FunctionExtensionOperation",
]
