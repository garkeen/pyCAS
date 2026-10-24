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
from cas.language import propositions as Pr
from cas.language import typing as Ty
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.specification import (
    DerivativeVocabulary,
    has_derivative,
)
from cas.math.calculus.differentiation.view import SpecializationView
from cas.operations.protocols import (
    CheckerBinding,
    GenericResultInput,
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
    ValueMappingInput,
)
from cas.semantics import elaborate
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


@dataclass(frozen=True, slots=True)
class SpecializationOperation:
    """Problem and proposal builders for exact point specialisation."""

    signature: LanguageSignature
    frames: FrameStore
    vocabulary: DerivativeVocabulary
    variable: SymbolId
    name_of: Callable[[SymbolId], str]
    view: SpecializationView
    parameter_request: AlgebraRequest
    id: str = "specialize"
    version: str = "1"
    problem_kind: str = "specialize"
    specification_kind: str = "HasDerivative"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    self.specification_kind,
                    self.problem_kind,
                    self.view.checker.id,
                ),
            ),
        )

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        if len(request.inputs) != 1:
            return ProblemInvalid("specialisation takes one input")
        if request.target is None:
            return ProblemInvalid("specialisation needs a target variable")
        if request.target != self.variable:
            return ProblemUnsupported(
                Reason.FRAGMENT,
                "this runtime specialises with respect to x only",
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
                parameter_mode=self.view.request.parameter_mode,
                coverage=Coverage.ONE_VERIFIED,
            )
        )

    def propose(
        self,
        request: OperationRequest,
        problem: ProblemSpec,
    ) -> ProposalOutcome:
        del problem
        family_input = request.parameter("family")
        values_input = request.parameter("values")
        if not isinstance(family_input, GenericResultInput):
            return ProposalInvalid(
                "specialisation needs a verified generic result"
            )
        if not isinstance(values_input, ValueMappingInput):
            return ProposalInvalid(
                "specialisation needs exact rational values"
            )
        source = request.inputs[0]
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
        substituted_source = B.substitute_free(source, mapping)
        source_value = self.view.bridge.to_value(substituted_source)
        if source_value is None:
            return ProposalUnsupported(
                Reason.FRAGMENT,
                "the specialized source is outside the polynomial fragment",
            )
        specialized_source = self.view.bridge.to_term(source_value)
        if specialized_source is None:
            return ProposalInvalid(
                "the specialized source cannot be rendered"
            )

        if isinstance(outcome, Applied):
            candidate_value = self.view.bridge.to_value(outcome.result)
            trace = ("generic_formula",)
        elif isinstance(outcome, (NeedsRecomputation, OutsideValidity)):
            candidate_value = None
            trace = ("recomputed",)
        else:
            raise TypeError(
                f"unknown specialization outcome: {type(outcome).__name__}"
            )
        if candidate_value is None:
            candidate_value = self.view.differential.deriv(source_value)
            trace = ("recomputed",)
        candidate_term = self.view.bridge.to_term(candidate_value)
        if candidate_term is None:
            return ProposalInvalid(
                "the specialized derivative cannot be rendered"
            )

        variable = T.symbol(self.variable, self.name_of(self.variable))
        specification_term = has_derivative(
            self.vocabulary,
            T.TRUE,
            specialized_source,
            variable,
            candidate_term,
        )
        issued = elaborate.proposition(
            specification_term,
            self.frames,
            request.frame,
            self.signature,
        )
        if not isinstance(issued, Pr.Proposition):
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
                ),
                trace=trace,
            )
        )


__all__ = ["SpecializationOperation"]
