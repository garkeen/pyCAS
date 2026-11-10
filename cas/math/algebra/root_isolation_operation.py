"""Registered verification-first real-root isolation for one polynomial over Q.

The operation isolates every distinct real root of a nonzero squarefree
univariate rational polynomial into a finite set of disjoint open rational
intervals.  The result language is a finite set of structural `Interval`
values; the independent `RootIsolationChecker` verifies the Sturm chain, the
coverage bound and the interval counts.  This module is the search side and is
never imported by the checker.

Fragment: ``p`` must be a nonzero squarefree polynomial over an ordered
characteristic-zero field (the registered assembly is Q[x]).  A non-squarefree
or zero polynomial, a non-ordered coefficient structure or a restricted region
is refused as a structured fragment gap with the missing capability.  The
result is complete only for this fragment: root objects, real algebraic
numbers, multiplicity output and closed intervals are outside this batch.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.protocols import Ordered
from cas.algebra.real_roots import (
    RealRootBudgetError,
    RealRootFragmentError,
    cauchy_bound,
    isolate_real_roots_open,
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
from cas.language.sets import set_term
from cas.language.signatures import LanguageSignature
from cas.math.algebra.root_isolation_specification import (
    RootIsolationCertificate,
    RootIsolationVocabulary,
    has_root_isolation,
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
    PolynomialBridge,
    RenderRefused,
    ViewRefused,
)
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

_FRAGMENT = frozenset({"univariate_polynomial_representation"})

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.FIELD, Capability.ORDERED_FIELD, Capability.POLYNOMIAL_RING}
)

# Resource control only: the number of bisection splits and non-root probe
# steps one proposal may spend.  It is deliberately conservative and fixed;
# exhaustion is reported as BUDGET, never as a partial complete answer.
_ROOT_ISOLATION_SPLIT_BUDGET = 1 << 16


@dataclass(frozen=True, slots=True)
class _RootIsolationFragment:
    """The admitted values and Sturm chain of one in-fragment request."""

    chain: tuple[Polynomial[Fraction], ...]


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
class RootIsolationOperation:
    """Registered problem and proposal builder for real-root isolation."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: RootIsolationVocabulary
    checker_id: str
    ring: UnivariatePolynomialRing[Fraction]
    bridge: PolynomialBridge[Fraction]
    request: AlgebraRequest
    id: str = "isolate_roots"
    version: str = "1"
    problem_kind: str = "isolate_roots"
    specification_kind: str = "HasRootIsolation"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        if self.ring is not self.bridge.ring:
            raise ValueError(
                "the root-isolation ring is not the bridge's ring"
            )
        if self.ring.generators != (self.request.target,):
            raise ValueError(
                "the request target is not the root-isolation ring's generator"
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
        assert self.request.target is not None
        return self.request.target

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("isolate_roots/squarefree-q", self._admit_input)

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

    def _fragment(
        self, polynomial: Polynomial[Fraction]
    ) -> _RootIsolationFragment | _FragmentGap:
        """Check the declared fragment and build the chain once.

        Admission and proposal share this single rule.  A refusal names the
        missing fragment capability; neither path guesses an interval or turns
        a boundary into a mathematical refutation.
        """
        if not isinstance(self.ring.coefficients, Ordered):
            return _FragmentGap(
                "root isolation needs an ordered coefficient field",
                frozenset({"ordered_coefficient_field"}),
            )
        try:
            chain = sturm_chain(self.ring, polynomial)
        except RealRootFragmentError as error:
            return _FragmentGap(error.detail, error.missing)
        return _RootIsolationFragment(chain)

    def _admit_input(self, request: OperationRequest) -> InputAdmission:
        if len(request.inputs) != 1:
            return InvalidRequest(
                ("root isolation takes exactly one polynomial",)
            )
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
        fragment = self._fragment(outcome.view.value)
        if isinstance(fragment, _FragmentGap):
            return Refused(
                Reason.FRAGMENT,
                fragment.detail,
                FragmentReport(missing=fragment.missing),
            )
        return Admitted()

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        if len(request.inputs) != 1:
            return ProblemInvalid(
                "root isolation takes exactly one polynomial"
            )
        if request.target is None:
            return ProblemInvalid("root isolation needs a target variable")
        if request.target != self.request.target:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                missing=frozenset({"target_view"}),
            )
        if request.region is not None:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "root isolation has no restricted-region form",
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
            coverage=Coverage.COMPLETE_SET,
            interpretation_requirement=(
                self.request.interpretation_requirement
            ),
            domain_requirement=DomainRequirement(
                coefficient=self.request.coefficient_domain,
                values=self.request.value_domain,
            ),
        )
        admission = self.input_schema.admit(request)
        if isinstance(admission, Refused):
            return unsupported_problem(admission, problem)
        if isinstance(admission, InvalidRequest):
            return invalid_problem(admission)
        fit = fit_request(
            request,
            result_language=result_language,
            parameter_mode=self.request.parameter_mode,
            coverages=frozenset({Coverage.COMPLETE_SET}),
        )
        if isinstance(fit, RequestMismatch):
            return unsupported_request(fit, problem)
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
        polynomial = view.value
        fragment = self._fragment(polynomial)
        if isinstance(fragment, _FragmentGap):
            return ProposalUnsupported(
                Reason.FRAGMENT,
                fragment.detail,
                missing=fragment.missing,
            )
        try:
            cauchy = cauchy_bound(self.ring, polynomial)
            intervals = isolate_real_roots_open(
                self.ring,
                polynomial,
                budget=_ROOT_ISOLATION_SPLIT_BUDGET,
            )
        except RealRootBudgetError as error:
            return ProposalUnsupported(
                Reason.BUDGET,
                error.detail,
                missing=error.missing,
            )
        except RealRootFragmentError as error:
            return ProposalUnsupported(
                Reason.FRAGMENT,
                error.detail,
                missing=error.missing,
            )
        coefficients = self.ring.coefficients
        # The certificate bound strictly contains the search radius, so every
        # emitted interval endpoint lies inside (-bound, bound) even for the
        # two outer intervals.
        certificate_bound = coefficients.add(
            cauchy,
            coefficients.add(coefficients.one(), coefficients.one()),
        )
        interval_terms = tuple(
            self.vocabulary.interval(T.number(lower), T.number(upper))
            for lower, upper in intervals
        )
        result = set_term(self.signature, interval_terms)
        rendered_chain: list[T.Term] = []
        for entry in fragment.chain:
            rendered = self.bridge.render(view, entry)
            if isinstance(rendered, RenderRefused):
                return ProposalUnsupported(
                    rendered.reason,
                    rendered.detail,
                    missing=rendered.missing,
                )
            rendered_chain.append(rendered.term)
        polynomial_term = view.source.term
        issued = elaborate.proposition(
            has_root_isolation(
                self.vocabulary,
                polynomial_term,
                result,
            ),
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the root-isolation specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=result,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=RootIsolationCertificate(
                    polynomial_term,
                    T.number(certificate_bound),
                    tuple(rendered_chain),
                ),
                answer_coverage=Coverage.COMPLETE_SET,
            )
        )


__all__ = ["RootIsolationOperation"]
