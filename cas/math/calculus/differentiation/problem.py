"""Shared problem construction for one-input expression operations.

Differentiation and specialisation both fix the same kind of problem: one typed
expression, the operation's target variable, the request region and one verified
result. The helper keeps that admission rule in one place; it does not choose a
mathematical candidate.
"""

from __future__ import annotations

from collections.abc import Callable

from cas.foundation.ids import FrameId, SymbolId
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
    OperationRequest,
    ProblemBuilt,
    ProblemInvalid,
    ProblemOutcome,
    ProblemUnsupported,
)
from cas.semantics import elaborate
from cas.semantics.frames import FrameStore
from cas.syntax import term as T


def expression_problem(
    request: OperationRequest,
    *,
    operation: str,
    variable: SymbolId,
    frames: FrameStore,
    signature: LanguageSignature,
    parameter_mode: ParameterMode,
) -> ProblemOutcome:
    """Admit one typed expression and fix its problem statement."""
    if len(request.inputs) != 1:
        return ProblemInvalid(f"{operation} takes one input")
    if request.target is None:
        return ProblemInvalid(f"{operation} needs a target variable")
    if request.target != variable:
        return ProblemUnsupported(
            Reason.FRAGMENT,
            "the request names a target variable outside this runtime",
        )
    source = request.inputs[0]
    typing = elaborate.typing(
        source, frames, request.frame, signature
    )
    if isinstance(typing, Ty.NeedsDeclaration):
        return ProblemInvalid("the source contains an undeclared symbol")
    if isinstance(typing, Ty.Unsupported):
        return ProblemInvalid(typing.detail)
    if isinstance(typing, Ty.IllTyped):
        return ProblemInvalid(typing.detail)
    if not isinstance(typing, Ty.Typed):
        return ProblemInvalid("the source cannot be typed")
    return ProblemBuilt(
        ProblemSpec(
            operation=operation,
            inputs=(source,),
            target=variable,
            region=request.region,
            result_language=ResultLanguage.EXPRESSION,
            parameter_mode=parameter_mode,
            coverage=Coverage.ONE_VERIFIED,
        )
    )


def derivative_specification(
    vocabulary: DerivativeVocabulary,
    region: T.Term,
    source: T.Term,
    variable: SymbolId,
    candidate: T.Term,
    *,
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    name_of: Callable[[SymbolId], str],
) -> Pr.Proposition | None:
    """Issue the `HasDerivative` specification shared by both operations."""
    variable_term = T.symbol(variable, name_of(variable))
    issued = elaborate.proposition(
        has_derivative(
            vocabulary,
            region,
            source,
            variable_term,
            candidate,
        ),
        frames,
        frame,
        signature,
    )
    return issued if isinstance(issued, Pr.Proposition) else None


__all__ = ["derivative_specification", "expression_problem"]
