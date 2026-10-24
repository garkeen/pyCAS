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
from cas.language import typing as Ty
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
    has_derivative,
)
from cas.operations.protocols import (
    CheckerBinding,
    MathematicalProposal,
    OperationRequest,
    ProblemBuilt,
    ProblemInvalid,
    ProblemOutcome,
    ProblemUnsupported,
    ProposalInvalid,
    ProposalOutcome,
    ProposalUnsupported,
    Proposed,
)
from cas.semantics import elaborate
from cas.semantics.frames import FrameStore
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
    variable: SymbolId
    name_of: Callable[[SymbolId], str]
    service: DerivativeService
    parameter_mode: ParameterMode
    id: str = "differentiate"
    version: str = "1"
    problem_kind: str = "differentiate"
    specification_kind: str = "HasDerivative"
    checker_bindings: tuple[CheckerBinding, ...] = ()

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
        if len(request.inputs) != 1:
            return ProblemInvalid("differentiation takes one input")
        if request.target is None:
            return ProblemInvalid("differentiation needs a target variable")
        if request.target != self.variable:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "this runtime differentiates with respect to x only",
            )
        source = request.inputs[0]
        typing = elaborate.typing(
            source, self.frames, request.frame, self.signature
        )
        if isinstance(typing, Ty.NeedsDeclaration):
            return ProblemInvalid(
                "the source contains an undeclared symbol"
            )
        if isinstance(typing, Ty.Unsupported):
            return ProblemInvalid(typing.detail)
        if isinstance(typing, Ty.IllTyped):
            return ProblemInvalid(typing.detail)
        if not isinstance(typing, Ty.Typed):
            return ProblemInvalid("the source cannot be typed")
        return ProblemBuilt(
            ProblemSpec(
                operation=self.problem_kind,
                inputs=(source,),
                target=self.variable,
                target_sort=typing.sort,
                region=request.region,
                result_language=ResultLanguage.EXPRESSION,
                parameter_mode=self.parameter_mode,
                coverage=Coverage.ONE_VERIFIED,
            )
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
            issued = elaborate.proposition(
                derivation.condition,
                self.frames,
                request.frame,
                self.signature,
            )
            if not isinstance(issued, Pr.Proposition):
                return ProposalInvalid(
                    "the differentiability region is not a proposition"
                )
            condition = issued
        region = T.TRUE if condition is None else condition.term

        variable = T.symbol(self.variable, self.name_of(self.variable))
        specification_term = has_derivative(
            self.vocabulary,
            region,
            source,
            variable,
            derivation.term,
        )
        issued = elaborate.proposition(
            specification_term,
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
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
                    derivation.term,
                ),
                result_region=condition,
                coverage=coverage,
                valid_on=valid_on,
            )
        )


__all__ = ["DifferentiationOperation"]
