"""The registered differentiation operation.

The workflow does not know `HasDerivative`, the derivative certificate or the
shape of a differentiability region. This module owns all of that and returns a
`MathematicalProposal`, which the workflow commits through the declared checker
binding.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.language import propositions as Pr
from cas.language.problems import ParameterMode, ProblemSpec
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.problem import (
    derivative_specification,
    expression_problem,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
)
from cas.operations.protocols import (
    CheckerBinding,
    MathematicalProposal,
    OperationRequest,
    ProblemOutcome,
    ProposalInvalid,
    ProposalOutcome,
    ProposalUnsupported,
    Proposed,
)
from cas.semantics import elaborate
from cas.semantics.frames import FrameStore
from cas.semantics.request import AlgebraRequest
from cas.semantics.services import (
    DerivationInvalid,
    DerivationUnsupported,
    DerivativeService,
    Derived,
)
from cas.semantics.specialization import coverage_claim
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class DifferentiationOperation:
    """Registered problem and proposal builders for derivative claims."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: DerivativeVocabulary
    algebra: AlgebraRequest
    name_of: Callable[[SymbolId], str]
    service: DerivativeService
    id: str = "differentiate"
    version: str = "1"
    problem_kind: str = "differentiate"
    specification_kind: str = "HasDerivative"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    @property
    def variable(self) -> SymbolId:
        """The target role fixed by the algebra request."""
        return self.algebra.target

    @property
    def parameter_mode(self) -> ParameterMode:
        """The parameter promise fixed by the algebra request."""
        return self.algebra.parameter_mode

    def __post_init__(self) -> None:
        if self.service.specification_kind != self.specification_kind:
            raise ValueError(
                "the derivative service reports another specification kind"
            )
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    self.service.checker_id,
                ),
            ),
        )

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        return expression_problem(
            request,
            operation=self.problem_kind,
            variable=self.variable,
            frames=self.frames,
            signature=self.signature,
            parameter_mode=self.parameter_mode,
        )

    def propose(
        self,
        request: OperationRequest,
        problem: ProblemSpec,
    ) -> ProposalOutcome:
        del problem
        source = request.inputs[0]
        derivation = self.service.candidate(source)
        if isinstance(derivation, DerivationUnsupported):
            return ProposalUnsupported(derivation.reason, derivation.detail)
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
        region = T.TRUE if condition is None else condition.term

        issued = derivative_specification(
            self.vocabulary,
            region,
            source,
            self.variable,
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
        if self.parameter_mode is not ParameterMode.SPECIFIED_VALUES:
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
            coverage = coverage_claim(self.parameter_mode, valid_on, ())

        return Proposed(
            MathematicalProposal(
                result=derivation.term,
                specifications=(issued,),
                specification_kind=self.specification_kind,
                certificate=self.service.certificate(
                    region,
                    source,
                    self.variable,
                    derivation,
                ),
                result_region=condition,
                coverage=coverage,
                valid_on=valid_on,
            )
        )


__all__ = ["DifferentiationOperation"]
