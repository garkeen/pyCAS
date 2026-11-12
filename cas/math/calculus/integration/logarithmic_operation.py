"""Registered rational-logarithmic integration operation over ``Q(x)``.

The operation proposes the exact decomposition

    source = D(polynomial_part) + sum(c_i * D(g_i)/g_i)

when every residue of the rational function is rational, and publishes the
visible antiderivative assembled from the polynomial part and the canonical
logarithm-term set.  The independent `LogarithmicIntegrationChecker` re-proves
the identity, the squarefree/coprime argument conditions and the domain
conditions; this module neither publishes a judgment nor imports the checker.

The low-level search is the rational-residue (Rothstein--Trager) logarithmic
part of M. Rothstein, "A new algorithm for the integration of elementary
functions", SYMSAC '76, and his 1976 MIT thesis; B. Trager, "Algebraic factoring
and rational function integration", SYMSAC '76; D. Lazard, R. Rioboo and
B. Trager, "Integration of rational functions: rational computation of the
logarithmic part", *Journal of Symbolic Computation* 9 (1990), 113--116.  The
surrounding design is M. Bronstein, *Symbolic Integration I: Transcendental
Functions*, 2nd edition, Springer 2005, Chapter 8; reference implementations
are FriCAS ``src/algebra/intrf.spad`` and Maxima ``src/risch.lisp``, used for
algorithm structure only.

Region and refusal boundary
---------------------------

The rational bridge fixes each source's denominator-nonzero region.  The
proposal states the conjunction of the source's and polynomial part's
definedness regions with the declared logarithm domain instantiated at every
logarithm argument: a logarithm is never globally valid in this fragment, so a
log-bearing result always carries those conditions.  The domain is read from
the admitted `FunctionSymbol` (`LogFunctionSemantics`), not rebuilt as a
hardcoded comparison.  A restricted problem region is admitted only when the
restricted condition logic proves it inside that conjunction; an undecided
inclusion is `GUARDED`, never assumed.

Inputs whose residue polynomial has an irreducible factor of degree at least
two leave the fragment: the operation returns a structured `ProposalUnsupported`
with ``rational_residues``/``algebraic_logarithmic_part`` and no partial
integral.  Budget exhaustion (`max_degree` or factorization) is reported as
`BUDGET` with the low-level `missing` tokens and likewise returns no partial
result.  Algebraic residues, ``RootSum`` representations, the real-log branch
and the transcendental Risch tower remain future slices.

Admission checks the exact one-input rational-function representation; it never
runs the integration algorithm, so an admitted input is not a promise that a
complete integral exists.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from fractions import Fraction

from cas.algebra.logarithmic_integration import (
    LogarithmicIntegrationBudget,
    LogarithmicIntegrationBudgetError,
    LogarithmicIntegrationFragmentError,
    rational_log_integral,
)
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
from cas.math.calculus.integration.logarithmic_specification import (
    LogFunctionSemantics,
    RationalLogAntiderivativeCertificate,
    RationalLogVocabulary,
    has_rational_log_antiderivative,
    rational_log_antiderivative_term,
    rational_log_term_set,
    require_log_semantics,
)
from cas.math.calculus.integration.rational_view import (
    RationalFunctionView,
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
from cas.semantics.conditions import and_all, is_subregion
from cas.semantics.frames import FrameSorts, FrameStore
from cas.syntax import term as T

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.RATIONAL_FUNCTION_FIELD}
)
_MISSING_TARGET_VIEW = frozenset({"target_view"})
_MISSING_COEFFICIENT_FIELD = frozenset({"coefficient_fraction_field"})


@dataclass(frozen=True, slots=True)
class LogarithmicIntegrationOperation:
    """Registered problem and proposal builders for rational logarithmic parts."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: RationalLogVocabulary
    views: tuple[RationalFunctionView[Fraction], ...]
    name_of: Callable[[SymbolId], str]
    default_target: SymbolId
    budget: LogarithmicIntegrationBudget = LogarithmicIntegrationBudget()
    id: str = "integrate_rational_logarithmic"
    version: str = "1"
    problem_kind: str = "integrate_rational_logarithmic"
    specification_kind: str = "HasRationalLogAntiderivative"
    checker_bindings: tuple[CheckerBinding, ...] = ()
    log_semantics: LogFunctionSemantics = field(
        init=False, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if not isinstance(self.budget, LogarithmicIntegrationBudget):
            raise TypeError(
                "a rational-logarithmic operation needs a "
                "LogarithmicIntegrationBudget"
            )
        semantics = require_log_semantics(self.vocabulary)
        if semantics.function.symbol != self.vocabulary.log_symbol:
            raise ValueError(
                "the declared logarithm semantics does not match the "
                "vocabulary"
            )
        if not self.views:
            raise ValueError(
                "a rational-logarithmic operation needs an algebra view"
            )
        targets = tuple(view.target for view in self.views)
        if len(set(targets)) != len(targets):
            raise ValueError(
                "a target has more than one rational-logarithmic view"
            )
        if self.default_target not in targets:
            raise ValueError(
                "the default target has no rational-logarithmic view"
            )
        object.__setattr__(self, "log_semantics", semantics)
        object.__setattr__(
            self,
            "checker_bindings",
            tuple(
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    view.checker_id,
                    target=view.target,
                    candidate_role=CandidateRole.RESULT,
                )
                for view in self.views
            ),
        )

    def view_for(
        self, target: SymbolId | None
    ) -> RationalFunctionView[Fraction] | None:
        if target is None:
            return None
        for view in self.views:
            if view.target == target:
                return view
        return None

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema(
            "integrate_rational_logarithmic/rational-function",
            self._admit_input,
        )

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
        if len(request.inputs) != 1:
            return InvalidRequest(
                (
                    "integrate_rational_logarithmic takes exactly one "
                    "rational function",
                )
            )
        view = self.view_for(request.target)
        if view is None:
            return Refused(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                FragmentReport(missing=_MISSING_TARGET_VIEW),
            )
        if view.request.parameter_mode is not ParameterMode.SPECIFIED_VALUES:
            return Refused(
                Reason.FRAGMENT,
                "rational logarithmic integration over a parameter family "
                "needs a coefficient fraction field",
                FragmentReport(missing=_MISSING_COEFFICIENT_FIELD),
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
                missing=_MISSING_TARGET_VIEW,
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

    def propose(self, execution: ExecutionRequest) -> ProposalOutcome:
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
                missing=_MISSING_TARGET_VIEW,
            )
        algebra = execution.algebra
        if algebra is None:
            return ProposalInvalid("the execution has no algebra view")
        if algebra is not view.request:
            return ProposalInvalid(
                "the execution algebra view is not the selected "
                "rational-function view"
            )
        if problem.operation != self.problem_kind:
            return ProposalInvalid(
                "the fixed problem is not a rational logarithmic integration "
                "problem"
            )
        if len(problem.inputs) != 1:
            return ProposalInvalid(
                "integrate_rational_logarithmic takes exactly one rational "
                "function"
            )
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
                "an admitted rational-logarithmic input could not be converted"
            )
        source_view = converted.view
        try:
            integral = rational_log_integral(
                view.field, source_view.value, self.budget
            )
        except LogarithmicIntegrationBudgetError as error:
            return ProposalUnsupported(
                Reason.BUDGET, error.detail, missing=error.missing
            )
        except LogarithmicIntegrationFragmentError as error:
            return ProposalUnsupported(
                Reason.FRAGMENT, error.detail, missing=error.missing
            )
        part = view.bridge.render(source_view, integral.polynomial_part)
        if isinstance(part, RenderRefused):
            return ProposalUnsupported(
                part.reason, part.detail, missing=part.missing
            )
        rendered_arguments: list[T.Term] = []
        for log_term in integral.log_terms:
            rendered = view.bridge.render(
                source_view, view.field.of_polynomial(log_term.argument)
            )
            if isinstance(rendered, RenderRefused):
                return ProposalUnsupported(
                    rendered.reason,
                    rendered.detail,
                    missing=rendered.missing,
                )
            rendered_arguments.append(rendered.term)
        part_term = part.term
        log_terms_term = rational_log_term_set(
            self.signature,
            self.vocabulary.log_function,
            tuple(
                (log_term.coefficient, rendered)
                for log_term, rendered in zip(
                    integral.log_terms, rendered_arguments
                )
            ),
        )
        result_term = rational_log_antiderivative_term(
            self.signature, part_term, log_terms_term
        )
        conditions: list[T.Term] = []
        for item in (source_view.source_domain, source_view.valid_on):
            if item is not None and item.term not in conditions:
                conditions.append(item.term)
        part_view = typed_view(
            view.bridge,
            part_term,
            self.frames,
            request.frame,
            self.signature,
            view.request,
        )
        if isinstance(part_view, ViewRefused):
            return ProposalUnsupported(
                part_view.reason,
                part_view.detail,
                missing=part_view.missing,
                conditions=part_view.conditions,
            )
        if not isinstance(part_view, AlgebraView):
            return ProposalInvalid(
                "the rendered polynomial part could not be read back: "
                + part_view.detail
            )
        for item in (part_view.source_domain, part_view.valid_on):
            if item is not None and item.term not in conditions:
                conditions.append(item.term)
        for rendered_argument in rendered_arguments:
            conditions.append(
                self.log_semantics.domain(
                    rendered_argument, self.signature
                )
            )
        environment = FrameSorts(self.frames, request.frame)
        combined = and_all(
            self.signature, *conditions, environment=environment
        )
        region: Pr.Proposition | None
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
                    "the rational-logarithmic validity region is not a "
                    "proposition"
                )
            region = issued_region
        region_term = T.TRUE if region is None else region.term
        if problem.region is not None:
            covered = is_subregion(
                problem.region.term,
                region_term,
                self.signature,
                environment,
            )
            if covered is not True:
                return ProposalUnsupported(
                    Reason.GUARDED,
                    "the requested region is not proved inside the "
                    "rational-logarithmic validity region",
                    missing=frozenset({"region_coverage"}),
                    conditions=(problem.region,),
                )
        source_term = source_view.source.term
        target = view.request.target
        variable_term = T.symbol(target, self.name_of(target))
        issued = elaborate.proposition(
            has_rational_log_antiderivative(
                self.vocabulary,
                region_term,
                source_term,
                variable_term,
                part_term,
                log_terms_term,
                result_term,
            ),
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the rational-logarithmic specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=result_term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=RationalLogAntiderivativeCertificate(
                    region_term,
                    source_term,
                    target,
                    part_term,
                    log_terms_term,
                    result_term,
                ),
                result_region=region,
                answer_coverage=Coverage.ONE_VERIFIED,
                structured=StructuredResult(
                    "RationalLogAntiderivative",
                    (
                        ("polynomial_part", part_term),
                        ("log_terms", log_terms_term),
                    ),
                ),
            )
        )


__all__ = ["LogarithmicIntegrationOperation"]
