"""Shared problem construction for one-input expression operations.

Differentiation, integration, Hermite reduction and specialisation all fix the
same kind of problem: one typed expression, the operation's target role, the
request region, one result language and one coverage. The helper keeps that
admission rule in one place; it does not choose a mathematical candidate.

The roles come from the operation's pre-assembled `AlgebraRequest`; this helper
never invents a target or parameter mode of its own.
"""

from __future__ import annotations

from collections.abc import Callable

from cas.foundation.ids import FrameId, SymbolId
from cas.language import propositions as Pr
from cas.language import typing as Ty
from cas.language.decisions import Reason
from cas.language.problems import (
    Coverage,
    DomainRequirement,
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
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T


def expression_problem(
    request: OperationRequest,
    *,
    operation: str,
    algebra: AlgebraRequest,
    frames: FrameStore,
    signature: LanguageSignature,
    result_language: ResultLanguage,
    coverage: Coverage = Coverage.ONE_VERIFIED,
) -> ProblemOutcome:
    """Admit one typed expression and fix its problem statement."""
    roles = algebra.roles
    if len(request.inputs) != 1:
        return ProblemInvalid(f"{operation} takes one input")
    if request.target is None:
        return ProblemInvalid(f"{operation} needs a target variable")
    if roles.target is None:
        return ProblemInvalid(f"{operation} has no target role")
    if request.target != roles.target:
        return ProblemUnsupported(
            Reason.FRAGMENT,
            "the request names a target variable outside this runtime",
        )
    source = elaborate.typed(
        request.inputs[0], frames, request.frame, signature
    )
    if not isinstance(source, Ty.TypedExpr):
        return ProblemInvalid(source.detail)
    return ProblemBuilt(
        ProblemSpec(
            operation=operation,
            inputs=(source,),
            roles=roles,
            region=request.region,
            result_language=result_language,
            coverage=coverage,
            interpretation_requirement=algebra.interpretation_requirement,
            domain_requirement=DomainRequirement(
                coefficient=algebra.coefficient_domain,
                values=algebra.value_domain,
            ),
        ),
        algebra=algebra,
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
