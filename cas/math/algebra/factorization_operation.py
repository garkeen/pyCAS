"""Registered ``Q[x]`` factorization for the fixed default polynomial view.

The operation runs the low-level Hensel/Zassenhaus search
(``cas.algebra.factorization``), builds the canonical encoded factor set and
the visible product, and proposes a `HasFactorization(source, x, unit, factors)`
claim together with a `FactorizationCertificate`.  The independent
`FactorizationChecker` re-proves the unit, the product, the radical and the
irreducibility witness; this module is the search side and is never imported by
the checker.

Fragment: the source must be a polynomial in the request's univariate ``Q[x]``
ring.  Zero is refused because it has no factorization; a nonzero constant is
in-fragment and yields the constant as unit with no factors and the radical
``1``.  Non-monic, negative-leading, rational-coefficient, repeated-factor and
non-squarefree inputs are all in-fragment.  The result is the complete
irreducible factorization over Q, with the search record's unit (the source
leading coefficient) and multiplicities.

The structured result is exactly the certificate's unit and factor set under
the names ``unit`` and ``factors``; the visible result is the product built by
`factorization_product_term`.  Budget exhaustion or a fragment gap is a
structured `ProposalUnsupported` and never a partial factorization.  The
budget bounds prime trials, Hensel precision, Zassenhaus subset visits,
candidate division tests and the nested Berlekamp work; the independent
checker has matching default enumeration and precision bounds, so the default
assembly never accepts a certificate beyond the resource envelope that
produced it.

This slice fixes the default ``Q[x]`` view only.  It publishes no multivariate
factorization, no public ``Z[x]`` entry with unit/multiplicity output and no
algebraic-extension factorization; ``A2`` is not complete.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction

from cas.algebra.factorization import (
    FactorizationBudget,
    FactorizationBudgetError,
    FactorizationFragmentError,
    factor_polynomial_over_q,
    hensel_witness_for_radical,
)
from cas.algebra.integer_polynomial import rational_polynomial_form
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
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
    FactorizationVocabulary,
    HenselIrreducibilityWitness,
    factorization_factor_set,
    factorization_product_term,
    factorization_radical_term,
    has_factorization,
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
    StructuredResult,
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
_NONZERO = frozenset({"nonzero_polynomial"})

_CAPABILITY_REQUIREMENTS: CapabilityRequirements = frozenset(
    {Capability.FIELD, Capability.POLYNOMIAL_RING}
)


@dataclass(frozen=True, slots=True)
class FactorizationOperation:
    """Registered problem and proposal builder for ``Q[x]`` factorization."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: FactorizationVocabulary
    checker_id: str
    ring: UnivariatePolynomialRing[Fraction]
    bridge: PolynomialBridge[Fraction]
    name_of: Callable[[SymbolId], str]
    request: AlgebraRequest
    budget: FactorizationBudget = FactorizationBudget()
    id: str = "factor_polynomial"
    version: str = "1"
    problem_kind: str = "factor_polynomial"
    specification_kind: str = "HasFactorization"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        if self.ring is not self.bridge.ring:
            raise ValueError(
                "the factorization ring is not the bridge's ring"
            )
        if self.ring.generators != (self.request.target,):
            raise ValueError(
                "the request target is not the factorization ring's "
                "generator"
            )
        if (
            self.request.roles.parameters
            or self.request.parameter_ring is not None
        ):
            raise ValueError(
                "a factorization operation cannot take formal parameters"
            )
        if not isinstance(self.budget, FactorizationBudget):
            raise TypeError(
                "the factorization budget must be a FactorizationBudget"
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
        return InputSchema(
            "factor_polynomial/univariate-q", self._admit_input
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
                ("factor_polynomial takes exactly one polynomial",)
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
        if outcome.view.value.is_zero():
            return Refused(
                Reason.FRAGMENT,
                "the zero polynomial has no factorization",
                FragmentReport(missing=_NONZERO),
            )
        return Admitted()

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        parameters = self.parameter_schema.parse(request.parameters)
        if isinstance(parameters, InvalidRequest):
            return invalid_problem(parameters)
        if len(request.inputs) != 1:
            return ProblemInvalid(
                "factor_polynomial takes exactly one polynomial"
            )
        if request.target is None:
            return ProblemInvalid(
                "factor_polynomial needs a target variable"
            )
        if request.target != self.request.target:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "the request names a target variable outside this runtime",
                missing=frozenset({"target_view"}),
            )
        if request.region is not None:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "factor_polynomial has no restricted-region form",
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
        if algebra is not self.request:
            return ProposalInvalid(
                "the execution does not use this operation's algebra request"
            )
        if problem.operation != self.problem_kind:
            return ProposalInvalid(
                "the execution problem is not a factorization problem"
            )
        if len(problem.inputs) != 1:
            return ProposalInvalid(
                "a factorization problem needs exactly one input"
            )
        converted = self.bridge.to_view(problem.inputs[0], algebra)
        if isinstance(converted, ViewRefused):
            return ProposalUnsupported(
                converted.reason,
                converted.detail,
                missing=converted.missing,
                conditions=converted.conditions,
            )
        source_view = converted.view
        if source_view.value.is_zero():
            return ProposalUnsupported(
                Reason.FRAGMENT,
                "the zero polynomial has no factorization",
                missing=_NONZERO,
            )
        try:
            result = factor_polynomial_over_q(
                self.ring, source_view.value, self.budget
            )
        except FactorizationBudgetError as error:
            return ProposalUnsupported(
                Reason.BUDGET, error.detail, missing=error.missing
            )
        except FactorizationFragmentError as error:
            return ProposalUnsupported(
                Reason.FRAGMENT, error.detail, missing=error.missing
            )
        unit_term = T.number(result.unit)
        entries: list[tuple[T.Term, int]] = []
        for factor, multiplicity in result.factors:
            rendered = self.bridge.render(source_view, factor)
            if isinstance(rendered, RenderRefused):
                return ProposalUnsupported(
                    rendered.reason,
                    rendered.detail,
                    missing=rendered.missing,
                )
            entries.append((rendered.term, multiplicity))
        factors_term = factorization_factor_set(
            self.signature, tuple(entries)
        )
        radical_term = factorization_radical_term(
            self.signature, tuple(entries)
        )
        product_term = factorization_product_term(
            self.signature, unit_term, factors_term
        )
        if product_term is None:
            return ProposalInvalid(
                "the factorization search returned a malformed factor set"
            )
        witness: HenselIrreducibilityWitness | None = None
        if any(
            self.ring.degree(factor, 0) >= 2
            for factor, _ in result.factors
        ):
            radical_value = self.ring.one()
            for factor, _ in result.factors:
                radical_value = self.ring.mul(radical_value, factor)
            try:
                lift = hensel_witness_for_radical(
                    self.ring, radical_value, self.budget
                )
                lifted_terms: list[T.Term] = []
                for lifted in lift.lifted:
                    rendered = self.bridge.render(
                        source_view,
                        rational_polynomial_form(self.ring, lifted),
                    )
                    if isinstance(rendered, RenderRefused):
                        return ProposalUnsupported(
                            rendered.reason,
                            rendered.detail,
                            missing=rendered.missing,
                        )
                    lifted_terms.append(rendered.term)
            except FactorizationBudgetError as error:
                return ProposalUnsupported(
                    Reason.BUDGET, error.detail, missing=error.missing
                )
            except FactorizationFragmentError as error:
                return ProposalUnsupported(
                    Reason.FRAGMENT, error.detail, missing=error.missing
                )
            witness = HenselIrreducibilityWitness(
                lift.prime, lift.precision, tuple(lifted_terms)
            )
        source_term = source_view.source.term
        variable_term = T.symbol(
            self.target, self.name_of(self.target)
        )
        issued = elaborate.proposition(
            has_factorization(
                self.vocabulary,
                source_term,
                variable_term,
                unit_term,
                factors_term,
            ),
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return ProposalInvalid(
                "the factorization specification is not a proposition"
            )
        return Proposed(
            MathematicalProposal(
                result=product_term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=FactorizationCertificate(
                    source_term,
                    self.target,
                    unit_term,
                    factors_term,
                    radical_term,
                    witness,
                ),
                structured=StructuredResult(
                    "factorization",
                    (
                        ("unit", unit_term),
                        ("factors", factors_term),
                    ),
                ),
            )
        )


__all__ = ["FactorizationOperation"]
