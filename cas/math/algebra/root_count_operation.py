"""Registered real-root counting for one squarefree polynomial over Q.

The operation computes the number of distinct real roots in an open interval
with rational endpoints and proposes `HasRootCount(p, a, b, n)`.  The
independent `RootCountChecker` verifies the supplied Sturm chain step by step;
this module is the search side and is never imported by the checker.

Fragment: ``p`` must be a nonzero squarefree polynomial over Q, ``a`` and ``b``
must be rational constants with ``a < b``, and the interval is open.  A
non-squarefree polynomial, the zero polynomial, a nonconstant endpoint, a
reversed interval or a non-rational term is refused as a structured fragment
gap with the missing capability; no count is guessed and no judgment is
proposed.  Root isolation, interval objects, multiplicity output and real
algebraic numbers are outside this batch.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.protocols import Ordered
from cas.algebra.real_roots import (
    RealRootFragmentError,
    count_real_roots_open,
    sturm_chain,
)
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
from cas.math.algebra.root_count_specification import (
    RootCountCertificate,
    RootCountVocabulary,
    has_root_count,
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
from cas.semantics.bridge import (
    AlgebraView,
    PolynomialBridge,
    RenderRefused,
    ViewRefused,
)
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

E = TypeVar("E")

_FRAGMENT = frozenset({"univariate_polynomial_representation"})

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.FIELD, Capability.ORDERED_FIELD, Capability.POLYNOMIAL_RING}
)


@dataclass(frozen=True, slots=True)
class _RootCountFragment(Generic[E]):
    """The admitted values and Sturm chain of one in-fragment request."""

    lower: E
    upper: E
    chain: tuple[Polynomial[E], ...]


@dataclass(frozen=True, slots=True)
class _FragmentGap:
    """A structured fragment refusal shared by admission and proposal."""

    detail: str
    missing: frozenset[str]

    def __post_init__(self) -> None:
        if not self.detail:
            raise ValueError("a fragment gap needs a detail")
        if not self.missing:
            raise ValueError("a fragment gap needs a missing set")
        object.__setattr__(self, "missing", frozenset(self.missing))


@dataclass(frozen=True, slots=True)
class RootCountOperation(Generic[E]):
    """Registered problem and proposal builder for real-root counts."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: RootCountVocabulary
    checker_id: str
    ring: UnivariatePolynomialRing[E]
    bridge: PolynomialBridge[E]
    request: AlgebraRequest
    id: str = "root_count"
    version: str = "1"
    problem_kind: str = "root_count"
    specification_kind: str = "HasRootCount"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        if self.ring is not self.bridge.ring:
            raise ValueError("the root-count ring is not the bridge's ring")
        if self.ring.generators != (self.request.target,):
            raise ValueError(
                "the request target is not the root-count ring's generator"
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
        return InputSchema("root_count/squarefree-q", self._admit_input)

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
        if len(request.inputs) != 3:
            return InvalidRequest(
                ("root_count takes the polynomial and two endpoints",)
            )
        typed_inputs = elaborate.typed_inputs(
            request.inputs,
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(typed_inputs, tuple):
            return InvalidRequest((typed_inputs.detail,))
        views: list[AlgebraView[Polynomial[E]]] = []
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
            views.append(outcome.view)
        fragment = self._fragment(
            views[0].value, views[1].value, views[2].value
        )
        if isinstance(fragment, _FragmentGap):
            return Refused(
                Reason.FRAGMENT,
                fragment.detail,
                FragmentReport(missing=fragment.missing),
            )
        return Admitted()

    def _fragment(
        self,
        polynomial: Polynomial[E],
        lower: Polynomial[E],
        upper: Polynomial[E],
    ) -> _RootCountFragment[E] | _FragmentGap:
        """Check the declared fragment and return the values and chain.

        Admission and proposal share this single rule.  A refusal names the
        missing fragment capability; neither path ever guesses a count or
        turns a boundary into a mathematical refutation.
        """
        coefficients = self.ring.coefficients
        if not isinstance(coefficients, Ordered):
            return _FragmentGap(
                "root counting needs an ordered coefficient field",
                frozenset({"ordered_coefficient_field"}),
            )
        try:
            chain = sturm_chain(self.ring, polynomial)
        except RealRootFragmentError as error:
            return _FragmentGap(error.detail, error.missing)
        if not self.ring.is_constant(lower):
            return _FragmentGap(
                "the lower endpoint must be a rational constant",
                frozenset({"rational_endpoint"}),
            )
        if not self.ring.is_constant(upper):
            return _FragmentGap(
                "the upper endpoint must be a rational constant",
                frozenset({"rational_endpoint"}),
            )
        lower_value = self.ring.coefficient(lower, (0,))
        upper_value = self.ring.coefficient(upper, (0,))
        if not coefficients.less(lower_value, upper_value):
            return _FragmentGap(
                "the root-count interval needs lower < upper",
                frozenset({"ordered_endpoints"}),
            )
        return _RootCountFragment(lower_value, upper_value, chain)

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        if len(request.inputs) != 3:
            return ProblemInvalid(
                "root_count takes the polynomial and two endpoints"
            )
        if request.target is None:
            return ProblemInvalid("root_count needs a target variable")
        if request.target != self.request.target:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                missing=frozenset({"target_view"}),
            )
        if request.region is not None:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "root_count has no restricted-region form",
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
        views: list[AlgebraView[Polynomial[E]]] = []
        for typed in problem.inputs:
            outcome = self.bridge.to_view(typed, algebra)
            if isinstance(outcome, ViewRefused):
                return ProposalUnsupported(
                    outcome.reason,
                    outcome.detail,
                    missing=outcome.missing,
                    conditions=outcome.conditions,
                )
            views.append(outcome.view)
        polynomial_view, lower_view, upper_view = views
        fragment = self._fragment(
            polynomial_view.value, lower_view.value, upper_view.value
        )
        if isinstance(fragment, _FragmentGap):
            return ProposalUnsupported(
                Reason.FRAGMENT,
                fragment.detail,
                missing=fragment.missing,
            )
        try:
            count = count_real_roots_open(
                self.ring,
                polynomial_view.value,
                fragment.lower,
                fragment.upper,
            )
        except RealRootFragmentError as error:
            return ProposalUnsupported(
                Reason.FRAGMENT,
                error.detail,
                missing=error.missing,
            )
        chain = fragment.chain
        rendered_chain: list[T.Term] = []
        for entry in chain:
            rendered = self.bridge.render(polynomial_view, entry)
            if isinstance(rendered, RenderRefused):
                return ProposalUnsupported(
                    rendered.reason,
                    rendered.detail,
                    missing=rendered.missing,
                )
            rendered_chain.append(rendered.term)
        polynomial_term = polynomial_view.source.term
        lower_term = lower_view.source.term
        upper_term = upper_view.source.term
        count_term = T.number(count)
        issued = elaborate.proposition(
            has_root_count(
                self.vocabulary,
                polynomial_term,
                lower_term,
                upper_term,
                count_term,
            ),
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the root-count specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=count_term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=RootCountCertificate(
                    polynomial_term,
                    lower_term,
                    upper_term,
                    count_term,
                    tuple(rendered_chain),
                ),
            )
        )


__all__ = ["RootCountOperation"]
