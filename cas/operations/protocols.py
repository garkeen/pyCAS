"""Open operation protocol: problems, proposals and checker bindings.

An operation is registered data, not a branch in the workflow. Its problem
builder turns a fixed request into a `ProblemSpec`; its proposal builder turns
the same request into a mathematical proposal. The workflow commits proposals
through the checker binding and never imports the operation's implementation.

The request contains resolved terms, not workbook objects. The workflow keeps
object-version binding, events and revisions; mathematics sees only the fixed
snapshot.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass, replace
from enum import StrEnum
from fractions import Fraction
from typing import Any, Generic, Protocol, TypeAlias, TypeVar

from cas.foundation.ids import FrameId, SymbolId
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.execution import ConditionPolicy, ExecutionBudget
from cas.language.functions import FunctionValue
from cas.language.problems import (
    Coverage,
    InterpretationRequirement,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
    ValueDomain,
)
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.language.typing import TypedExpr
from cas.operations.capabilities import Capability
from cas.semantics.regions import region_from_proposition
from cas.semantics.request import AlgebraRequest
from cas.semantics.specialization import (
    CoverageClaim,
    GenericResult,
    exact_values,
    validate_coverage_claim,
)
from cas.syntax import term as T

# --- operation inputs ---


@dataclass(frozen=True, slots=True)
class ValueMappingInput:
    """An exact assignment of symbols to rational values."""

    values: Mapping[SymbolId, Fraction]

    def __post_init__(self) -> None:
        object.__setattr__(self, "values", exact_values(self.values))


@dataclass(frozen=True, slots=True)
class GenericResultInput:
    """A verified generic result that another operation may refine."""

    result: GenericResult


@dataclass(frozen=True, slots=True)
class FunctionExtensionInput:
    """The data needed to extend one explicit partial function.

    `value` is the current function value; `domain` is the new intrinsic
    domain and `valid_on` is the region on which the new representation is
    valid.  The operation proves agreement with the old value on the old
    domain before the workspace records the extension.  A partial condition is
    admitted as an input draft but refused by the operation: `FunctionValue`
    records total domain and representation conditions in this batch.
    """

    value: FunctionValue
    domain: Proposition
    valid_on: Proposition

    def __post_init__(self) -> None:
        if not isinstance(self.value, FunctionValue):
            raise TypeError("a function extension needs a FunctionValue")
        if not isinstance(self.domain, Proposition):
            raise TypeError("a function extension needs a domain proposition")
        if not isinstance(self.valid_on, Proposition):
            raise TypeError(
                "a function extension needs a representation region"
            )


@dataclass(frozen=True, slots=True)
class FunctionComparisonInput:
    """Two explicit function values and the representations to compare."""

    left: FunctionValue
    right: FunctionValue
    left_index: int
    right_index: int

    def __post_init__(self) -> None:
        if not isinstance(self.left, FunctionValue):
            raise TypeError("a function comparison needs a left value")
        if not isinstance(self.right, FunctionValue):
            raise TypeError("a function comparison needs a right value")
        if not 0 <= self.left_index < len(self.left.representations):
            raise ValueError("the left representation index is out of range")
        if not 0 <= self.right_index < len(self.right.representations):
            raise ValueError("the right representation index is out of range")


# --- operation parameters ---

P = TypeVar("P")


@dataclass(frozen=True, slots=True)
class Parsed(Generic[P]):
    """A parameter payload accepted by an operation-owned schema."""

    value: P


@dataclass(frozen=True, slots=True)
class InvalidRequest:
    """The request shape or parameter kind is not the operation's contract."""

    issues: tuple[str, ...]

    def __post_init__(self) -> None:
        issues = tuple(self.issues)
        if not issues:
            raise ValueError("an invalid request needs at least one issue")
        if any(not isinstance(issue, str) or not issue for issue in issues):
            raise TypeError("request issues must be non-empty strings")
        object.__setattr__(self, "issues", issues)


ParameterOutcome: TypeAlias = Parsed[P] | InvalidRequest


@dataclass(frozen=True, slots=True)
class ParameterSchema(Generic[P]):
    """The operation-owned parser for its named auxiliary parameters.

    `parse` receives the request's `(name, value)` tuple and returns either the
    operation's concrete parameter payload or a structural `InvalidRequest`.
    Semantic refusals stay in `InputSchema`; this schema only decides whether
    the parameter shape and payload kinds match the operation's contract.
    """

    id: str
    parse: Callable[
        [tuple[tuple[str, object], ...]], ParameterOutcome[P]
    ]

    def __post_init__(self) -> None:
        if not isinstance(self.id, str) or not self.id:
            raise ValueError("a parameter schema needs an identifier")
        if not callable(self.parse):
            raise TypeError("a parameter schema needs a parse callable")


@dataclass(frozen=True, slots=True)
class OperationRequest:
    """One resolved request for a registered operation.

    `inputs` are the primary mathematical inputs. `parameters` are named
    auxiliary values whose meaning is fixed by the operation's own contract.
    Names are data, not dispatch: the workflow never branches on them.  The
    values are opaque here; each operation's `ParameterSchema` decides their
    shape and payload kinds.
    """

    frame: FrameId
    inputs: tuple[T.Term, ...]
    target: SymbolId | None = None
    region: Proposition | None = None
    coverage: Coverage = Coverage.ONE_VERIFIED
    result_language: ResultLanguage | None = None
    parameter_mode: ParameterMode | None = None
    parameters: tuple[tuple[str, object], ...] = ()

    def __post_init__(self) -> None:
        if not self.inputs:
            raise ValueError("an operation request needs at least one input")
        if any(not isinstance(item, T.Term) for item in self.inputs):
            raise TypeError("operation inputs must be terms")
        if self.region is not None:
            if not isinstance(self.region, Proposition):
                raise TypeError("an operation region must be a proposition")
            if self.region.definedness:
                raise ValueError(
                    "an operation region must be a total condition; this "
                    "batch's region consumers compare condition terms and do "
                    "not account for definedness premises"
                )
        if not isinstance(self.coverage, Coverage):
            raise TypeError("an operation request needs a coverage")
        if self.result_language is not None and not isinstance(
            self.result_language, ResultLanguage
        ):
            raise TypeError(
                "an operation result language must be a ResultLanguage or None"
            )
        if self.parameter_mode is not None and not isinstance(
            self.parameter_mode, ParameterMode
        ):
            raise TypeError(
                "an operation parameter mode must be a ParameterMode or None"
            )
        if not isinstance(self.parameters, tuple):
            raise TypeError("operation parameters must be a tuple")
        names = [name for name, _ in self.parameters]
        if any(not isinstance(name, str) or not name for name in names):
            raise ValueError("an operation parameter needs a name")
        if len(set(names)) != len(names):
            raise ValueError("an operation parameter is assigned twice")


# --- operation input and result schemas ---


@dataclass(frozen=True, slots=True)
class FragmentReport:
    """What an operation would need to admit an input it currently refuses."""

    missing: frozenset[str] = frozenset()
    conditions: tuple[Proposition, ...] = ()
    attempted: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError("fragment capabilities must be non-empty strings")
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError("fragment conditions must be propositions")
        attempted = tuple(self.attempted)
        if any(not isinstance(item, str) or not item for item in attempted):
            raise TypeError("fragment attempts must be non-empty strings")
        object.__setattr__(self, "missing", missing)
        object.__setattr__(self, "conditions", conditions)
        object.__setattr__(self, "attempted", attempted)


@dataclass(frozen=True, slots=True)
class Admitted:
    """The request's input representation is inside the operation's fragment."""


@dataclass(frozen=True, slots=True)
class Refused:
    """The input is well formed but outside the operation's implemented fragment."""

    reason: Reason
    detail: str
    report: FragmentReport = FragmentReport()

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("a refusal needs a Reason")
        if not isinstance(self.detail, str) or not self.detail:
            raise ValueError("a refusal needs a detail")
        if not isinstance(self.report, FragmentReport):
            raise TypeError("a refusal needs a FragmentReport")


InputAdmission: TypeAlias = Admitted | Refused | InvalidRequest


@dataclass(frozen=True, slots=True)
class InputSchema:
    """The operation-owned adapter that admits its input representation.

    The callable is the operation's own structural classifier.  It is not a
    central union of payloads and not a second workflow branch: `build_problem`
    calls it before fixing a problem, and the refusal carries the same
    `FragmentReport` the workspace records.
    """

    id: str
    admit: Callable[[OperationRequest], InputAdmission]

    def __post_init__(self) -> None:
        if not isinstance(self.id, str) or not self.id:
            raise ValueError("an input schema needs an identifier")
        if not callable(self.admit):
            raise TypeError("an input schema needs an admission callable")


class ResultShape(StrEnum):
    """The visible representation form fixed by a result schema.

    A shape is declared, never inferred from a candidate term.  The proposition
    and set shapes are distinct from a scalar expression even when their terms
    happen to have a similar surface form.
    """

    EXPRESSION = "expression"
    PROPOSITION = "proposition"
    SET = "set"
    DECOMPOSITION = "decomposition"


_SHAPE_LANGUAGE = {
    ResultShape.EXPRESSION: ResultLanguage.EXPRESSION,
    ResultShape.PROPOSITION: ResultLanguage.PROPOSITION,
    ResultShape.SET: ResultLanguage.SET,
    ResultShape.DECOMPOSITION: ResultLanguage.DECOMPOSITION,
}


@dataclass(frozen=True, slots=True)
class ResultSchema:
    """The result language and representation shape one operation produces.

    `shape` is the operation's explicit declaration; it is never derived from a
    candidate or from the request.  `validate` checks only the visible
    representation.  The caller supplies the elaborated view for the shapes that
    need one, because operations do not own frames or elaboration.
    """

    languages: frozenset[ResultLanguage]
    shape: ResultShape

    def __post_init__(self) -> None:
        languages = frozenset(self.languages)
        if not languages:
            raise ValueError("a result schema declares no language")
        if any(not isinstance(item, ResultLanguage) for item in languages):
            raise TypeError("result languages must be ResultLanguage values")
        if not isinstance(self.shape, ResultShape):
            raise TypeError("a result schema needs a ResultShape")
        expected = _SHAPE_LANGUAGE[self.shape]
        if any(language != expected for language in languages):
            declared = ", ".join(
                sorted(language.value for language in languages)
            )
            raise ValueError(
                f"result shape {self.shape.value} requires "
                f"{expected.value} results, not {declared}"
            )
        object.__setattr__(self, "languages", languages)

    def accepts(self, language: ResultLanguage) -> bool:
        return language in self.languages

    def single_language(self) -> ResultLanguage:
        """The one result language this schema fixes.

        An operation that fixes a single result language in `build_problem`
        takes it from here, so the schema remains the only declaration.  A
        schema declaring several languages has no fixed language; deriving one
        would silently narrow the operation, so this is refused instead.
        """
        if len(self.languages) != 1:
            raise ValueError(
                "the result schema declares "
                f"{len(self.languages)} languages; a fixed single result "
                "language cannot be derived from it"
            )
        return next(iter(self.languages))

    def validate(
        self,
        *,
        result: T.Term,
        structured: StructuredResult | None,
        typed: TypedExpr | None,
        set_term: bool | None = None,
    ) -> str | None:
        """Why `result` does not fit this shape, or None when it fits.

        `typed` is the caller's elaborated view.  Only the proposition and set
        shapes consume it; an expression or decomposition result does not need
        one.  `set_term` is the caller's structural check that the result is a
        `Set` application; the schema owns the rule, the workspace owns the
        signature needed to recognise it.  A SET result must supply that check
        explicitly: `None` is not "unknown, so accept", because that would let
        a caller bypass the structural requirement.  The method deliberately
        does not elaborate: it must stay free of frames, meanings and the
        workflow.
        """
        if not isinstance(result, T.Term):
            raise TypeError("a result schema needs a term")
        if set_term is not None and not isinstance(set_term, bool):
            raise TypeError(
                "a result schema set_term must be a bool or None"
            )
        if self.shape is ResultShape.EXPRESSION:
            if structured is not None:
                return "an expression problem cannot carry a decomposition"
            return None
        if self.shape is ResultShape.PROPOSITION:
            if structured is not None:
                return "a proposition problem cannot carry a decomposition"
            if typed is None or typed.sort != S.PROPOSITION:
                return "a proposition result must be a proposition"
            return None
        if self.shape is ResultShape.SET:
            if structured is not None:
                return "a set problem cannot carry a decomposition"
            if set_term is None:
                return (
                    "a Set result needs an explicit structural Set check"
                )
            if set_term is False:
                return "a set problem needs a Set result"
            if typed is None:
                return "a Set result must be a Set term with a set sort"
            if not isinstance(typed.sort, S.SetSort):
                return "a Set result must have a set sort"
            return None
        if structured is None:
            return "a decomposition problem needs a structured result"
        return None


# --- problem construction ---


def _interpretation_binding_mismatch(
    problem: ProblemSpec,
    algebra: AlgebraRequest | None,
) -> str | None:
    """The single problem/algebra interpretation binding rule.

    A problem with an algebra view must fix the language-owned interpretation
    requirement and it must equal the resolved request's requirement.  A problem
    without an algebra view (a function problem) must not pretend to have one.
    """
    requirement: InterpretationRequirement | None = (
        problem.interpretation_requirement
    )
    if algebra is None:
        if requirement is not None:
            return (
                "a problem without an algebra view cannot require an algebra "
                "interpretation"
            )
        return None
    if requirement is None:
        return "an algebra problem must fix its interpretation requirement"
    if requirement != algebra.interpretation_requirement:
        return (
            "the algebra view and the problem must share one interpretation "
            "requirement"
        )
    return None


def _domain_binding_mismatch(
    problem: ProblemSpec,
    algebra: AlgebraRequest | None,
) -> str | None:
    """The single problem/algebra domain binding rule.

    A problem with an algebra view fixes the language-level coefficient range
    and value domain, and both must equal the resolved request's declared
    values.  A function problem has no coefficient structure and fixes real
    values.  A problem without an algebra view and without function inputs
    cannot carry a domain requirement at all.
    """
    requirement = problem.domain_requirement
    if algebra is not None:
        if requirement is None:
            return "an algebra problem must fix a domain requirement"
        if requirement.coefficient != algebra.coefficient_domain:
            return (
                "the algebra view and the problem must share one coefficient "
                "domain"
            )
        if requirement.values != algebra.value_domain:
            return (
                "the algebra view and the problem must share one value domain"
            )
        return None
    if problem.function_inputs:
        if requirement is None:
            return "a function problem must fix a domain requirement"
        if requirement.coefficient is not None:
            return "a function problem has no coefficient domain"
        if requirement.values is not ValueDomain.REAL:
            return "function equality is stated for real values"
        return None
    if requirement is not None:
        return (
            "a problem without an algebra view cannot carry a domain "
            "requirement"
        )
    return None


@dataclass(frozen=True, slots=True)
class ProblemBuilt:
    problem: ProblemSpec
    algebra: AlgebraRequest | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.problem, ProblemSpec):
            raise TypeError("a built problem must be a ProblemSpec")
        if self.algebra is not None:
            if not isinstance(self.algebra, AlgebraRequest):
                raise TypeError(
                    "a built problem's algebra view must be an "
                    "AlgebraRequest or None"
                )
            if self.algebra.roles != self.problem.roles:
                raise ValueError(
                    "the algebra view and the problem must share one role "
                    "value"
                )
            if self.algebra.target != self.problem.target:
                raise ValueError(
                    "the algebra view and the problem must share one target"
                )
        interpretation = _interpretation_binding_mismatch(
            self.problem, self.algebra
        )
        if interpretation is not None:
            raise ValueError(interpretation)
        domain = _domain_binding_mismatch(self.problem, self.algebra)
        if domain is not None:
            raise ValueError(domain)


@dataclass(frozen=True, slots=True)
class ExecutionRequest:
    """One attempt at a fixed problem under an explicit execution strategy.

    `request` is the original draft with parameters, target and region;
    `problem` is the fixed specification that was admitted from it.  `algebra`
    is the pre-assembled algebra view selected by the problem builder, or
    `None` for an operation without an algebra view.  `frame`, `policy` and
    `budget` fix the attempt's scope and limits.

    The algebra view is bound to the problem, never to the draft: the proposal
    and the checker must see the same roles and target even when the draft has
    been elaborated into typed inputs.
    """

    request: OperationRequest
    problem: ProblemSpec
    algebra: AlgebraRequest | None
    frame: FrameId
    policy: ConditionPolicy
    budget: ExecutionBudget

    def __post_init__(self) -> None:
        if not isinstance(self.request, OperationRequest):
            raise TypeError("an execution request needs an OperationRequest")
        if not isinstance(self.problem, ProblemSpec):
            raise TypeError("an execution request needs a ProblemSpec")
        if self.algebra is not None and not isinstance(
            self.algebra, AlgebraRequest
        ):
            raise TypeError(
                "an execution algebra view must be an AlgebraRequest or None"
            )
        if self.frame != self.request.frame:
            raise ValueError(
                "the execution frame must be the request frame"
            )
        if not isinstance(self.policy, ConditionPolicy):
            raise TypeError(
                "an execution policy must be a ConditionPolicy"
            )
        if not isinstance(self.budget, ExecutionBudget):
            raise TypeError(
                "an execution budget must be an ExecutionBudget"
            )
        if self.algebra is not None:
            if self.problem.roles != self.algebra.roles:
                raise ValueError(
                    "the execution problem and algebra view must share one "
                    "role value"
                )
            if self.problem.target != self.algebra.target:
                raise ValueError(
                    "the execution problem and algebra view must share one "
                    "target"
                )
        interpretation = _interpretation_binding_mismatch(
            self.problem, self.algebra
        )
        if interpretation is not None:
            raise ValueError(interpretation)
        domain = _domain_binding_mismatch(self.problem, self.algebra)
        if domain is not None:
            raise ValueError(domain)


@dataclass(frozen=True, slots=True)
class ProblemUnsupported:
    """The request is well formed but the current implementation has no clause.

    `missing` names the capabilities the operation lacks; `conditions` are the
    obligations that prevent the problem from being fixed.  The workspace turns
    this into a structured `Blocker` instead of discarding the reason.
    """

    reason: Reason
    detail: str
    missing: frozenset[str] = frozenset()
    conditions: tuple[Proposition, ...] = ()
    attempted: tuple[str, ...] = ()
    problem: ProblemSpec | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("an unsupported problem needs a Reason")
        if not isinstance(self.detail, str):
            raise TypeError("an unsupported problem detail must be a string")
        if not self.detail:
            raise ValueError("an unsupported problem needs a detail")
        if self.problem is not None and not isinstance(
            self.problem, ProblemSpec
        ):
            raise TypeError("an unsupported problem may carry a fixed problem")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError(
                "unsupported-problem capabilities must be non-empty strings"
            )
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError(
                "unsupported-problem conditions must be propositions"
            )
        attempted = tuple(self.attempted)
        if any(not isinstance(item, str) or not item for item in attempted):
            raise TypeError(
                "unsupported-problem attempts must be non-empty strings"
            )
        object.__setattr__(self, "missing", missing)
        object.__setattr__(self, "conditions", conditions)
        object.__setattr__(self, "attempted", attempted)


@dataclass(frozen=True, slots=True)
class ProblemInvalid:
    detail: str


ProblemOutcome: TypeAlias = ProblemBuilt | ProblemUnsupported | ProblemInvalid


def unsupported_problem(
    admission: Refused,
    problem: ProblemSpec | None = None,
) -> ProblemUnsupported:
    """The single conversion from an input refusal to a problem outcome.

    `problem` is supplied when the request is well formed enough to fix a
    problem but its input representation is outside the operation's fragment.
    The workspace then records a blocked task with that fixed problem instead
    of losing the refusal.
    """
    return ProblemUnsupported(
        admission.reason,
        admission.detail,
        missing=admission.report.missing,
        conditions=admission.report.conditions,
        attempted=admission.report.attempted,
        problem=problem,
    )


def invalid_problem(admission: InvalidRequest) -> ProblemInvalid:
    """The single conversion from an invalid request to a problem outcome."""
    return ProblemInvalid("; ".join(admission.issues))


@dataclass(frozen=True, slots=True)
class RequestMismatch:
    """An explicit request dimension outside the operation's fixed contract."""

    detail: str
    missing: frozenset[str] = frozenset()
    reason: Reason = Reason.FRAGMENT

    def __post_init__(self) -> None:
        if not isinstance(self.detail, str) or not self.detail:
            raise ValueError("a request mismatch needs a detail")
        object.__setattr__(self, "missing", frozenset(self.missing))


def fit_request(
    request: OperationRequest,
    *,
    result_language: ResultLanguage,
    parameter_mode: ParameterMode,
    coverages: frozenset[Coverage],
) -> RequestMismatch | None:
    """Compare explicit request dimensions with the operation's fixed ones.

    `None` means the caller left the dimension to the operation's pre-assembled
    view or result schema; it is not rewritten into a concrete user request.
    An explicit value that differs is refused here, before any problem is
    claimed to be fixed.  Coverage is always concrete, so it is compared against
    the set the operation actually supports.
    """
    if (
        request.result_language is not None
        and request.result_language != result_language
    ):
        return RequestMismatch(
            "the operation fixes "
            f"{result_language.value} results, not "
            f"{request.result_language.value}",
            frozenset({f"result_language:{request.result_language.value}"}),
        )
    if (
        request.parameter_mode is not None
        and request.parameter_mode != parameter_mode
    ):
        return RequestMismatch(
            "the operation's algebra view fixes parameter mode "
            f"{parameter_mode.value}, not {request.parameter_mode.value}",
            frozenset({f"parameter_mode:{request.parameter_mode.value}"}),
        )
    if request.coverage not in coverages:
        supported = ", ".join(
            sorted(coverage.value for coverage in coverages)
        )
        return RequestMismatch(
            "the operation supports coverage "
            f"{supported}, not {request.coverage.value}",
            frozenset({f"coverage:{request.coverage.value}"}),
        )
    return None


def unsupported_request(
    mismatch: RequestMismatch,
    problem: ProblemSpec | None = None,
) -> ProblemUnsupported:
    """The single conversion from a dimension mismatch to a problem outcome."""
    return ProblemUnsupported(
        mismatch.reason,
        mismatch.detail,
        missing=mismatch.missing,
        problem=problem,
    )


def blocked_problem(
    request: OperationRequest,
    problem: ProblemSpec,
) -> ProblemSpec:
    """The problem a blocked task records for a refused request.

    An operation fixes the problem it could admit, which may carry fallback
    dimensions.  A blocked task still has to show the problem the user asked
    for, so the explicit result language and coverage replace those fallbacks.
    The parameter mode is kept only when rebuilding the roles with the requested
    mode stays legal; a generic mode without declared parameters cannot be
    represented, and the blocker reports that missing dimension instead.
    """
    roles = problem.roles
    if (
        request.parameter_mode is not None
        and request.parameter_mode != roles.parameter_mode
    ):
        try:
            roles = replace(roles, parameter_mode=request.parameter_mode)
        except ValueError:
            # The requested mode needs parameters this request does not have;
            # keep the operation's valid roles and let the blocker explain the
            # missing dimension instead of constructing invalid VariableRoles.
            roles = problem.roles
    return replace(
        problem,
        roles=roles,
        result_language=(
            problem.result_language
            if request.result_language is None
            else request.result_language
        ),
        coverage=request.coverage,
    )


# --- mathematical proposals ---


@dataclass(frozen=True, slots=True)
class StructuredResult:
    """A named decomposition of a proposal's visible result.

    Components are neutral terms.  They do not carry trust by themselves; the
    proposal's specifications and certificate are what the checker verifies.
    """

    kind: str
    components: tuple[tuple[str, T.Term], ...]

    def __post_init__(self) -> None:
        if not self.kind:
            raise ValueError("a structured result needs a kind")
        if not self.components:
            raise ValueError("a structured result needs at least one component")
        names = [name for name, _ in self.components]
        if any(not name for name in names):
            raise ValueError("a structured result component needs a name")
        if len(set(names)) != len(names):
            raise ValueError("a structured result repeats a component name")
        if any(not isinstance(term, T.Term) for _, term in self.components):
            raise TypeError("structured result components must be terms")


@dataclass(frozen=True, slots=True)
class MathematicalProposal:
    """What an operation proposes to the workflow.

    The proposal is not a judgment. It names the exact specifications it asks
    to verify, the certificate bytes its checker interprets, and the region on
    which the result is stated. `coverage`/`valid_on` describe the parameter
    family; `answer_coverage` describes the answer-set completeness the proposal
    claims, and must meet the fixed problem's requested coverage.

    `result_region`, `valid_on` and every excluded case are total conditions in
    this batch.  The workspace, the result-region display and the generic-result
    bridge read their terms; a partial condition would have its definedness
    premises silently ignored.  They move to `RegionSpec` only together with
    those consumers.
    """

    result: T.Term
    specifications: tuple[Proposition, ...]
    specification_kind: str
    certificate: object
    result_region: Proposition | None = None
    coverage: CoverageClaim | None = None
    valid_on: Proposition | None = None
    excluded_cases: tuple[Proposition, ...] = ()
    trace: tuple[str, ...] = ()
    answer_coverage: Coverage = Coverage.ONE_VERIFIED
    structured: StructuredResult | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.result, T.Term):
            raise TypeError("a proposal result must be a term")
        if not self.specifications:
            raise ValueError("a proposal needs at least one specification")
        if not self.specification_kind:
            raise ValueError("a proposal needs a specification kind")
        if any(
            not isinstance(item, Proposition) for item in self.specifications
        ):
            raise TypeError("proposal specifications are propositions")
        if self.result_region is not None:
            if not isinstance(self.result_region, Proposition):
                raise TypeError("a result region must be a proposition")
            if self.result_region.definedness:
                raise ValueError(
                    "a result region must be a total condition; this batch's "
                    "region consumers compare condition terms and do not "
                    "account for definedness premises"
                )
        if self.valid_on is not None:
            if not isinstance(self.valid_on, Proposition):
                raise TypeError("a validity region must be a proposition")
            if self.valid_on.definedness:
                raise ValueError(
                    "a validity region must be a total condition; this "
                    "batch's region consumers compare condition terms and do "
                    "not account for definedness premises"
                )
        excluded = tuple(self.excluded_cases)
        if any(not isinstance(item, Proposition) for item in excluded):
            raise TypeError("excluded cases must be propositions")
        if any(case.definedness for case in excluded):
            raise ValueError(
                "an excluded case must be a total condition; this batch's "
                "region consumers compare condition terms and do not account "
                "for definedness premises"
            )
        validate_coverage_claim(
            self.coverage,
            (
                None
                if self.valid_on is None
                else region_from_proposition(self.valid_on)
            ),
            tuple(region_from_proposition(case) for case in excluded),
        )
        if not isinstance(self.answer_coverage, Coverage):
            raise TypeError(
                "answer_coverage must be a requested-coverage value"
            )
        if self.structured is not None and not isinstance(
            self.structured, StructuredResult
        ):
            raise TypeError("a structured proposal needs a StructuredResult")
        object.__setattr__(self, "excluded_cases", excluded)
        object.__setattr__(self, "trace", tuple(self.trace))


@dataclass(frozen=True, slots=True)
class Proposed:
    proposal: MathematicalProposal


@dataclass(frozen=True, slots=True)
class ProposalUnsupported:
    """The operation cannot produce a candidate for this request.

    This is not a mathematical refutation.  The reason, missing capabilities,
    open conditions and attempted fragments are preserved for the workspace and
    the front end.
    """

    reason: Reason
    detail: str
    missing: frozenset[str] = frozenset()
    conditions: tuple[Proposition, ...] = ()
    attempted: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("an unsupported proposal needs a Reason")
        if not isinstance(self.detail, str):
            raise TypeError("an unsupported proposal detail must be a string")
        if not self.detail:
            raise ValueError("an unsupported proposal needs a detail")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError(
                "unsupported-proposal capabilities must be non-empty strings"
            )
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError(
                "unsupported-proposal conditions must be propositions"
            )
        attempted = tuple(self.attempted)
        if any(not isinstance(item, str) or not item for item in attempted):
            raise TypeError(
                "unsupported-proposal attempts must be non-empty strings"
            )
        object.__setattr__(self, "missing", missing)
        object.__setattr__(self, "conditions", conditions)
        object.__setattr__(self, "attempted", attempted)


@dataclass(frozen=True, slots=True)
class ProposalInvalid:
    detail: str


ProposalOutcome: TypeAlias = Proposed | ProposalUnsupported | ProposalInvalid


# --- registration ---


@dataclass(frozen=True, slots=True)
class CheckerBinding:
    """The exact checker admitted for one specification family and target role.

    `target` is the request-local role the binding serves.  A multi-target
    operation declares one binding per target; the workflow selects the binding
    by both the specification kind and the request target, so two views cannot
    silently share one checker.

    `candidate_role` is the side of the claim the operation publishes.  A
    mathematical binding declares it explicitly; a core-logic binding has no
    candidate and leaves it `None`.
    """

    specification_kind: str
    problem_kind: str
    checker_id: str
    target: SymbolId | None = None
    candidate_role: CandidateRole | None = None

    def __post_init__(self) -> None:
        if not self.specification_kind:
            raise ValueError("a checker binding needs a specification kind")
        if not self.problem_kind:
            raise ValueError("a checker binding needs a problem kind")
        if not self.checker_id:
            raise ValueError("a checker binding needs a checker id")
        if self.target is not None and (
            isinstance(self.target, bool) or not isinstance(self.target, int)
        ):
            raise TypeError("a checker binding target must be a SymbolId")
        if self.candidate_role is not None and not isinstance(
            self.candidate_role, CandidateRole
        ):
            raise TypeError(
                "a checker binding candidate role must be a CandidateRole "
                "or None"
            )


class OperationSpec(Protocol):
    """A registered operation; implementations live in `math`, not workflow.

    Architecture §16.1 also names an ``explanation_schema``.  It is
    deliberately absent here: no workflow consumer records or renders an
    explanation recipe yet, so adding a protocol property would create an
    unused contract.  The field becomes part of this protocol only together
    with the event/explanation consumer that reads it.
    """

    @property
    def id(self) -> str: ...

    @property
    def version(self) -> str: ...

    @property
    def checker_bindings(self) -> tuple[CheckerBinding, ...]: ...

    @property
    def input_schema(self) -> InputSchema:
        """The operation-owned admission adapter for its input representation."""

    @property
    def parameter_schema(self) -> ParameterSchema[Any]:
        """The operation-owned parser for its named auxiliary parameters."""

    @property
    def result_schema(self) -> ResultSchema:
        """The result language and visible shape this operation produces."""

    @property
    def capability_requirements(self) -> frozenset[Capability]:
        """The assembly structures this operation actually consumes."""

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        """Fix the problem statement for `request`."""

    def propose(self, execution: ExecutionRequest) -> ProposalOutcome:
        """Produce a mathematical proposal for the fixed problem."""


__all__ = [
    "Admitted",
    "CheckerBinding",
    "ExecutionRequest",
    "FragmentReport",
    "FunctionComparisonInput",
    "FunctionExtensionInput",
    "GenericResultInput",
    "InputAdmission",
    "InputSchema",
    "InvalidRequest",
    "MathematicalProposal",
    "OperationRequest",
    "OperationSpec",
    "ParameterOutcome",
    "ParameterSchema",
    "Parsed",
    "ProblemBuilt",
    "ProblemInvalid",
    "ProblemOutcome",
    "ProblemUnsupported",
    "ProposalInvalid",
    "ProposalOutcome",
    "ProposalUnsupported",
    "Proposed",
    "Refused",
    "RequestMismatch",
    "ResultSchema",
    "ResultShape",
    "StructuredResult",
    "ValueMappingInput",
    "blocked_problem",
    "fit_request",
    "invalid_problem",
    "unsupported_problem",
    "unsupported_request",
]
