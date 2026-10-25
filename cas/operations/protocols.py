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

from collections.abc import Mapping
from dataclasses import dataclass
from fractions import Fraction
from typing import Protocol, TypeAlias

from cas.foundation.ids import FrameId, SymbolId
from cas.language.decisions import Reason
from cas.language.problems import Coverage, ProblemSpec
from cas.language.propositions import Proposition
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


OperationInput: TypeAlias = ValueMappingInput | GenericResultInput


@dataclass(frozen=True, slots=True)
class OperationRequest:
    """One resolved request for a registered operation.

    `inputs` are the primary mathematical inputs. `parameters` are named
    auxiliary values whose meaning is fixed by the operation's own contract.
    Names are data, not dispatch: the workflow never branches on them.
    """

    frame: FrameId
    inputs: tuple[T.Term, ...]
    target: SymbolId | None = None
    region: Proposition | None = None
    parameters: tuple[tuple[str, OperationInput], ...] = ()

    def __post_init__(self) -> None:
        if not self.inputs:
            raise ValueError("an operation request needs at least one input")
        if any(not isinstance(item, T.Term) for item in self.inputs):
            raise TypeError("operation inputs must be terms")
        if self.region is not None and not isinstance(
            self.region, Proposition
        ):
            raise TypeError("an operation region must be a proposition")
        for _, value in self.parameters:
            if not isinstance(
                value, (ValueMappingInput, GenericResultInput)
            ):
                raise TypeError("unknown operation input kind")
        names = [name for name, _ in self.parameters]
        if any(not name for name in names):
            raise ValueError("an operation parameter needs a name")
        if len(set(names)) != len(names):
            raise ValueError("an operation parameter is assigned twice")
        object.__setattr__(self, "parameters", tuple(self.parameters))

    def parameter(self, name: str) -> OperationInput | None:
        for known, value in self.parameters:
            if known == name:
                return value
        return None


# --- problem construction ---


class ProblemOutcome:
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class ProblemBuilt(ProblemOutcome):
    problem: ProblemSpec


@dataclass(frozen=True, slots=True)
class ProblemUnsupported(ProblemOutcome):
    reason: Reason
    detail: str


@dataclass(frozen=True, slots=True)
class ProblemInvalid(ProblemOutcome):
    detail: str


# --- mathematical proposals ---


@dataclass(frozen=True, slots=True)
class MathematicalProposal:
    """What an operation proposes to the workflow.

    The proposal is not a judgment. It names the exact specifications it asks
    to verify, the certificate bytes its checker interprets, and the region on
    which the result is stated. `coverage`/`valid_on` describe the parameter
    family; `answer_coverage` describes the answer-set completeness the proposal
    claims, and must meet the fixed problem's requested coverage.
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
        if self.result_region is not None and not isinstance(
            self.result_region, Proposition
        ):
            raise TypeError("a result region must be a proposition")
        if self.valid_on is not None and not isinstance(
            self.valid_on, Proposition
        ):
            raise TypeError("a validity region must be a proposition")
        excluded = tuple(self.excluded_cases)
        if any(not isinstance(item, Proposition) for item in excluded):
            raise TypeError("excluded cases must be propositions")
        validate_coverage_claim(self.coverage, self.valid_on, excluded)
        if not isinstance(self.answer_coverage, Coverage):
            raise TypeError(
                "answer_coverage must be a requested-coverage value"
            )
        object.__setattr__(self, "excluded_cases", excluded)
        object.__setattr__(self, "trace", tuple(self.trace))


class ProposalOutcome:
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Proposed(ProposalOutcome):
    proposal: MathematicalProposal


@dataclass(frozen=True, slots=True)
class ProposalUnsupported(ProposalOutcome):
    reason: Reason
    detail: str


@dataclass(frozen=True, slots=True)
class ProposalInvalid(ProposalOutcome):
    detail: str


# --- registration ---


@dataclass(frozen=True, slots=True)
class CheckerBinding:
    """The exact checker admitted for one specification family."""

    specification_kind: str
    problem_kind: str
    checker_id: str

    def __post_init__(self) -> None:
        if not self.specification_kind:
            raise ValueError("a checker binding needs a specification kind")
        if not self.problem_kind:
            raise ValueError("a checker binding needs a problem kind")
        if not self.checker_id:
            raise ValueError("a checker binding needs a checker id")


class OperationSpec(Protocol):
    """A registered operation; implementations live in `math`, not workflow."""

    @property
    def id(self) -> str: ...

    @property
    def version(self) -> str: ...

    @property
    def checker_bindings(self) -> tuple[CheckerBinding, ...]: ...

    def build_problem(self, request: OperationRequest) -> ProblemOutcome:
        """Fix the problem statement for `request`."""

    def propose(
        self,
        request: OperationRequest,
        problem: ProblemSpec,
    ) -> ProposalOutcome:
        """Produce a mathematical proposal for the fixed problem."""


__all__ = [
    "CheckerBinding",
    "GenericResultInput",
    "MathematicalProposal",
    "OperationInput",
    "OperationRequest",
    "OperationSpec",
    "ProblemBuilt",
    "ProblemInvalid",
    "ProblemOutcome",
    "ProblemUnsupported",
    "ProposalInvalid",
    "ProposalOutcome",
    "ProposalUnsupported",
    "Proposed",
    "ValueMappingInput",
]
