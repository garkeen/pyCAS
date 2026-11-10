"""Workflow records: expression objects, candidates, verification and history.

An expression object is data. A candidate is a proposed answer. A verification
link records what a checker did with that candidate against an exact
specification. A revision is an immutable snapshot of what the workspace shows.

None of these carry mathematical truth; only the kernel does.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import StrEnum
from typing import TypeAlias

from cas.foundation.ids import (
    CandidateId,
    CaseSplitId,
    EventId,
    ExecutionAttemptId,
    FrameId,
    JudgmentId,
    ObjectId,
    ObjectVersionId,
    RevisionId,
    TaskId,
    WorldId,
)
from cas.kernel.model import FrameConsistency, Unassessed
from cas.language.decisions import Blocker
from cas.language.functions import FunctionValue
from cas.language.problems import Coverage, ParameterMode, ProblemSpec
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.operations.protocols import StructuredResult
from cas.semantics.frames import Declaration, Definition
from cas.semantics.request import AlgebraRequest
from cas.semantics.specialization import GenericResult
from cas.syntax import term as T
from cas.syntax.occurrences import Occurrence


class OperationStatus(StrEnum):
    """What happened to one proposed answer."""

    VERIFIED = "verified"
    CONDITIONAL = "conditional"
    REFUTED = "refuted"
    UNSUPPORTED = "unsupported"
    UNKNOWN = "unknown"
    INVALID = "invalid"
    EDITED = "edited"
    APPLIED = "applied"


class CandidateState(StrEnum):
    """The verification state of one candidate, derived at recording time."""

    UNCHECKED = "unchecked"
    VERIFIED = "verified"
    REFUTED = "refuted"
    UNVERIFIED = "unverified"


class CandidateApplicability(StrEnum):
    """Whether one candidate may be used under the conditions it carries."""

    APPLICABLE = "applicable"
    CONDITIONAL = "conditional"
    BLOCKED = "blocked"
    OUT_OF_SCOPE = "out_of_scope"


class CandidateCoverage(StrEnum):
    """How much of the requested answer set one candidate claims."""

    UNCLAIMED = "unclaimed"
    GENERIC = "generic"
    PARTIAL = "partial"
    COMPLETE = "complete"


class ResultLanguageFit(StrEnum):
    """Whether a candidate representation has the requested result shape."""

    SATISFIES = "satisfies"
    DOES_NOT_SATISFY = "does_not_satisfy"


class TaskState(StrEnum):
    """The user-visible state of one fixed problem."""

    DRAFT = "draft"
    READY = "ready"
    RUNNING = "running"
    WAITING_FOR_SUBTASKS = "waiting_for_subtasks"
    BLOCKED = "blocked"
    PARTIALLY_SOLVED = "partially_solved"
    COMPLETED = "completed"
    COMPLETED_CONDITIONAL = "completed_conditional"
    CANCELLED = "cancelled"


class TaskOrigin(StrEnum):
    """Whether a task was defined by the user or created by an execution."""

    MANUAL = "manual"
    EXECUTION = "execution"


class ExecutionState(StrEnum):
    """The lifecycle state of one execution attempt."""

    READY = "ready"
    RUNNING = "running"
    WAITING_FOR_SUBTASKS = "waiting_for_subtasks"
    BLOCKED = "blocked"
    FINISHED = "finished"
    CANCELLED = "cancelled"


class RewriteRelation(StrEnum):
    """The direction a manual rewrite claims."""

    EQUIVALENT = "equivalent"
    IMPLIES = "implies"
    IMPLIED_BY = "implied_by"
    SUBSTITUTION = "substitution"


def _check_presentation(
    presentation: tuple[tuple[str, str], ...],
) -> None:
    if any(
        not isinstance(pair, tuple)
        or len(pair) != 2
        or not isinstance(pair[0], str)
        or not pair[0]
        or not isinstance(pair[1], str)
        for pair in presentation
    ):
        raise TypeError("presentation metadata is a tuple of string pairs")
    keys = [key for key, _ in presentation]
    if len(set(keys)) != len(keys):
        raise ValueError("presentation metadata repeats a key")


def _check_optional_identifier(value: object, description: str) -> None:
    if value is None:
        return
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{description} must be an identifier or None")


def _check_identifier(value: object, description: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{description} must be an identifier")


def _check_frame_digest(value: object, description: str) -> None:
    """A content digest is empty or 64 lowercase hexadecimal characters.

    The empty string is allowed only for records created before a frame exists
    (the workspace start revision).  Every newly recorded event or revision
    carries the SHA-256 frame digest, so a forged or truncated value is refused
    at construction instead of entering history.
    """
    if not isinstance(value, str):
        raise TypeError(f"{description} must be a string")
    if not value:
        return
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise ValueError(
            f"{description} must be 64 lowercase hexadecimal characters"
        )


def _check_context_extension(
    status: OperationStatus,
    frame: FrameId,
    payload: Declaration | Definition | None,
    detail: str,
    *,
    description: str,
) -> None:
    """Validate the status/payload agreement of one context extension.

    A verified extension carries its declaration or definition and the child
    frame it created.  A refused extension carries no payload and keeps the
    original frame, so a caller cannot mistake a refusal for a published
    binding.
    """
    if not isinstance(status, OperationStatus):
        raise TypeError(f"{description} needs an OperationStatus")
    _check_identifier(frame, f"{description} frame")
    if not isinstance(detail, str):
        raise TypeError(f"{description} detail must be text")
    if status is OperationStatus.VERIFIED:
        if payload is None:
            raise ValueError(f"a verified {description} needs its payload")
    elif payload is not None:
        raise ValueError(f"a refused {description} carries no payload")


@dataclass(frozen=True, slots=True)
class Artifact:
    """A typed view of the neutral value held by one object version.

    An artifact is not a second mutable authority.  It references the exact
    immutable term or `FunctionValue` already stored by the workspace record;
    it never owns a copy that could diverge from that record.  Exactly one
    payload is present: a neutral expression term or an explicit function
    value.
    """

    term: T.Term | None = None
    function: FunctionValue | None = None

    def __post_init__(self) -> None:
        if (self.term is None) == (self.function is None):
            raise ValueError(
                "an artifact holds exactly one term or function value"
            )
        if self.term is not None and not isinstance(self.term, T.Term):
            raise TypeError("an artifact term must be a Term")
        if self.function is not None and not isinstance(
            self.function, FunctionValue
        ):
            raise TypeError("an artifact function must be a FunctionValue")


@dataclass(frozen=True, slots=True)
class ObjectVersion:
    """A typed, read-only view of one immutable object version.

    The workspace stores `Expression` and `FunctionObject` records.  This view
    exposes their common identity, frame, source operation and presentation
    metadata without owning or copying the payload; the record remains the
    only stored authority.
    """

    object_id: ObjectId
    version_id: ObjectVersionId
    artifact: Artifact
    created_in_frame: FrameId
    source_operation: str
    presentation: tuple[tuple[str, str], ...] = ()

    def __post_init__(self) -> None:
        _check_identifier(self.object_id, "an object version object id")
        _check_identifier(self.version_id, "an object version id")
        if not isinstance(self.artifact, Artifact):
            raise TypeError("an object version needs an Artifact")
        _check_identifier(
            self.created_in_frame, "an object version frame"
        )
        if not isinstance(self.source_operation, str):
            raise TypeError(
                "an object version source operation must be a string"
            )
        if not isinstance(self.presentation, tuple):
            raise TypeError(
                "object version presentation metadata must be a tuple"
            )
        _check_presentation(self.presentation)


@dataclass(frozen=True, slots=True, eq=False)
class Expression:
    """One immutable version of an expression object."""

    id: ObjectId
    version: ObjectVersionId
    term: T.Term
    frame: FrameId
    label: str = ""
    source_operation: str = ""
    presentation: tuple[tuple[str, str], ...] = ()

    def __post_init__(self) -> None:
        _check_presentation(self.presentation)

    @property
    def artifact(self) -> Artifact:
        """The stored term as a typed artifact view; no copy is kept."""
        return Artifact(term=self.term)

    @property
    def object_version(self) -> ObjectVersion:
        """This record's identity and metadata as an immutable view."""
        return ObjectVersion(
            self.id,
            self.version,
            self.artifact,
            self.frame,
            self.source_operation,
            self.presentation,
        )


@dataclass(frozen=True, slots=True, eq=False)
class FunctionObject:
    """One immutable version of an explicit partial-function object.

    `representation` names the expression object that currently represents the
    function.  The function value owns the intrinsic domain and the
    representation's validity region; the expression remains a neutral formula.
    """

    id: ObjectId
    version: ObjectVersionId
    value: FunctionValue
    representation: ObjectVersionId
    representation_index: int
    frame: FrameId
    label: str = ""
    source_operation: str = ""
    presentation: tuple[tuple[str, str], ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.value, FunctionValue):
            raise TypeError("a function object needs a FunctionValue")
        if not 0 <= self.representation_index < len(
            self.value.representations
        ):
            raise ValueError(
                "the function representation index is outside the value"
            )
        _check_presentation(self.presentation)

    @property
    def artifact(self) -> Artifact:
        """The stored function value as a typed artifact view; no copy."""
        return Artifact(function=self.value)

    @property
    def object_version(self) -> ObjectVersion:
        """This record's identity and metadata as an immutable view."""
        return ObjectVersion(
            self.id,
            self.version,
            self.artifact,
            self.frame,
            self.source_operation,
            self.presentation,
        )


@dataclass(frozen=True, slots=True)
class FunctionDefined:
    """The function object was recorded in the current revision."""

    function: FunctionObject


@dataclass(frozen=True, slots=True)
class FunctionRefused:
    """The function object was not recorded; nothing was written."""

    detail: str


FunctionDefinitionOutcome: TypeAlias = FunctionDefined | FunctionRefused


@dataclass(frozen=True, slots=True)
class TaskRecord:
    """A fixed problem and the candidates proposed for it.

    The state is a snapshot derived from the current verification links, not a
    search flag.  A task with a candidate but no verified specification is
    `PARTIALLY_SOLVED`; refuting a candidate eliminates that candidate, not the
    task's partial-result status.

    The state and payload must agree: `COMPLETED`, `COMPLETED_CONDITIONAL` and
    `PARTIALLY_SOLVED` carry at least one candidate, `BLOCKED` carries a
    structured blocker, and `READY` has no candidate, attempt or blocker yet.
    """

    id: TaskId
    problem: ProblemSpec
    frame: FrameId
    state: TaskState = TaskState.READY
    candidates: tuple[CandidateId, ...] = ()
    detail: str = ""
    origin: TaskOrigin = TaskOrigin.EXECUTION
    parent: TaskId | None = None
    depends_on: tuple[TaskId, ...] = ()
    inputs: tuple[ObjectVersionId, ...] = ()
    attempts: tuple[ExecutionAttemptId, ...] = ()
    blocker: Blocker | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.problem, ProblemSpec):
            raise TypeError("a task needs a ProblemSpec")
        if not isinstance(self.state, TaskState):
            raise TypeError("a task needs a TaskState")
        if not isinstance(self.origin, TaskOrigin):
            raise TypeError("a task needs a TaskOrigin")
        if self.blocker is not None and not isinstance(self.blocker, Blocker):
            raise TypeError("a task blocker must be a Blocker")
        if len(set(self.candidates)) != len(self.candidates):
            raise ValueError("a task repeats a candidate")
        if len(set(self.depends_on)) != len(self.depends_on):
            raise ValueError("a task repeats a dependency")
        if self.id in self.depends_on:
            raise ValueError("a task cannot depend on itself")
        if self.parent is not None and self.parent == self.id:
            raise ValueError("a task cannot be its own parent")
        if len(set(self.attempts)) != len(self.attempts):
            raise ValueError("a task repeats an execution attempt")
        if self.state in (
            TaskState.COMPLETED,
            TaskState.COMPLETED_CONDITIONAL,
            TaskState.PARTIALLY_SOLVED,
        ) and not self.candidates:
            raise ValueError(
                f"a {self.state.value} task needs at least one candidate"
            )
        if (
            self.state
            in (TaskState.COMPLETED, TaskState.COMPLETED_CONDITIONAL)
            and self.blocker is not None
        ):
            raise ValueError("a completed task cannot carry a blocker")
        if self.state is TaskState.BLOCKED and self.blocker is None:
            raise ValueError("a blocked task needs a blocker")
        if self.state is TaskState.READY and (
            self.candidates or self.attempts or self.blocker is not None
        ):
            raise ValueError(
                "a ready task has no candidates, attempts or blocker"
            )


@dataclass(frozen=True, slots=True)
class Candidate:
    """A proposed answer, with no trust attached.

    The four dimensions are separate (§18.2): verification (`state`),
    applicability, answer coverage, and whether the representation fits the
    requested result language.  They are derived by the workflow from the
    verification links and the fixed request; a searcher cannot promote a
    candidate by setting a single success flag.  `checked` is the only
    in-place transition and it requires all three derived dimensions.

    `candidate_role` is the part of the claim this candidate names.  It is
    copied from the checker binding so a manual re-check asks the checker for
    the same term the original proposal published.  A binding without a
    published candidate side leaves it `None`; a mathematical checker refuses
    a missing role when the candidate is re-checked.

    `certificate_required` records whether the registered checker declared a
    certificate type.  A core scope rule may declare that the empty certificate
    is valid; a mathematical checker requires an actual certificate, so a
    verified candidate without one is an invalid record.

    `algebra` is the exact pre-assembled `AlgebraRequest` the candidate was
    proposed under, or `None` when the problem has no algebra view (a function
    problem).  It is a snapshot, not a second role registry: a manual re-check
    submits this same request to the kernel so the checker verifies the same
    target, parameters, interpretation and differential instead of resolving a
    different pre-assembled view.  The value is data only; the workflow never
    branches on its coefficient structure.
    """

    id: CandidateId
    task: TaskId
    problem: ProblemSpec
    term: T.Term
    frame: FrameId
    state: CandidateState = CandidateState.UNCHECKED
    specifications: tuple[Proposition, ...] = ()
    certificate: object | None = None
    checker_id: str = ""
    specification_kind: str = ""
    result_region: Proposition | None = None
    applicability: CandidateApplicability = CandidateApplicability.APPLICABLE
    coverage: CandidateCoverage = CandidateCoverage.UNCLAIMED
    language_fit: ResultLanguageFit = ResultLanguageFit.SATISFIES
    candidate_role: CandidateRole | None = None
    certificate_required: bool = True
    structured: tuple[tuple[str, T.Term], ...] | None = None
    algebra: AlgebraRequest | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.problem, ProblemSpec):
            raise TypeError("a candidate needs a ProblemSpec")
        if not isinstance(self.term, T.Term):
            raise TypeError("a candidate needs a term")
        if self.algebra is not None and not isinstance(
            self.algebra, AlgebraRequest
        ):
            raise TypeError(
                "a candidate algebra request must be an AlgebraRequest or None"
            )
        if self.algebra is not None:
            if self.problem.function_inputs:
                raise ValueError(
                    "a function candidate has no algebra request"
                )
            if self.algebra.roles != self.problem.roles:
                raise ValueError(
                    "the candidate algebra roles do not match its problem"
                )
            if self.algebra.target != self.problem.target:
                raise ValueError(
                    "the candidate algebra target does not match its problem"
                )
        if not isinstance(self.state, CandidateState):
            raise TypeError("a candidate needs a CandidateState")
        if not isinstance(self.applicability, CandidateApplicability):
            raise TypeError(
                "a candidate needs a CandidateApplicability"
            )
        if not isinstance(self.coverage, CandidateCoverage):
            raise TypeError("a candidate needs a CandidateCoverage")
        if not isinstance(self.language_fit, ResultLanguageFit):
            raise TypeError("a candidate needs a ResultLanguageFit")
        if self.candidate_role is not None and not isinstance(
            self.candidate_role, CandidateRole
        ):
            raise TypeError(
                "a candidate role must be a CandidateRole or None"
            )
        if not isinstance(self.certificate_required, bool):
            raise TypeError("candidate certificate_required must be a bool")
        if self.structured is not None:
            names = [name for name, _ in self.structured]
            if any(not name for name in names):
                raise ValueError(
                    "a structured candidate needs a component name"
                )
            if len(set(names)) != len(names):
                raise ValueError(
                    "a structured candidate repeats a component name"
                )
            if any(
                not isinstance(term, T.Term) for _, term in self.structured
            ):
                raise TypeError("a structured candidate holds terms")
        if any(
            not isinstance(item, Proposition)
            for item in self.specifications
        ):
            raise TypeError("candidate specifications are propositions")
        if self.state is CandidateState.VERIFIED:
            if not self.specifications:
                raise ValueError(
                    "a verified candidate needs at least one specification"
                )
            if not self.checker_id:
                raise ValueError("a verified candidate needs a checker id")
            if self.certificate_required and self.certificate is None:
                raise ValueError("a verified candidate needs a certificate")

    def checked(
        self,
        state: CandidateState,
        *,
        applicability: CandidateApplicability,
        coverage: CandidateCoverage,
        language_fit: ResultLanguageFit,
    ) -> Candidate:
        """Return the same candidate with its derived dimensions."""
        return replace(
            self,
            state=state,
            applicability=applicability,
            coverage=coverage,
            language_fit=language_fit,
        )


@dataclass(frozen=True, slots=True)
class VerificationLink:
    """The result of checking one candidate against one specification.

    The link is scoped to the frame in which the check was issued, records the
    exact specification kind the checker accepted, and states the answer-set
    coverage the link establishes.  A condition is the open premise under which
    the link holds; it is not part of the candidate's identity.
    """

    candidate: CandidateId
    specification: Proposition
    judgment: JudgmentId | None
    status: OperationStatus
    specification_kind: str
    frame: FrameId
    coverage: Coverage
    condition: Proposition | None = None
    obligations: tuple[Proposition, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.specification, Proposition):
            raise TypeError("a verification link needs a specification")
        if self.judgment is not None and (
            isinstance(self.judgment, bool)
            or not isinstance(self.judgment, int)
        ):
            raise TypeError("a verification judgment must be a JudgmentId")
        if not isinstance(self.status, OperationStatus):
            raise TypeError("a verification link needs an OperationStatus")
        if (
            self.status
            in (OperationStatus.VERIFIED, OperationStatus.CONDITIONAL)
            and self.judgment is None
        ):
            raise ValueError(
                "a verified or conditional verification link needs a judgment"
            )
        if (
            not isinstance(self.specification_kind, str)
            or not self.specification_kind
        ):
            raise ValueError("a verification link needs a specification kind")
        if isinstance(self.frame, bool) or not isinstance(self.frame, int):
            raise TypeError("a verification link needs a FrameId")
        if not isinstance(self.coverage, Coverage):
            raise TypeError("a verification link needs a Coverage")
        if self.condition is not None and not isinstance(
            self.condition, Proposition
        ):
            raise TypeError("a verification condition is a proposition")
        obligations = tuple(self.obligations)
        if any(not isinstance(item, Proposition) for item in obligations):
            raise TypeError(
                "verification-link obligations must be propositions"
            )
        object.__setattr__(self, "obligations", obligations)


@dataclass(frozen=True, slots=True)
class ExecutionAttempt:
    """One execution attempt of a fixed task.

    The attempt is separate from the task's main state: a later cancelled
    attempt does not remove an earlier verified result.
    """

    id: ExecutionAttemptId
    task: TaskId
    state: ExecutionState
    outcome: OperationStatus | None = None
    detail: str = ""
    blocker: Blocker | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.state, ExecutionState):
            raise TypeError("an execution attempt needs an ExecutionState")
        if self.outcome is not None and not isinstance(
            self.outcome, OperationStatus
        ):
            raise TypeError("an execution outcome must be an OperationStatus")
        if self.blocker is not None and not isinstance(self.blocker, Blocker):
            raise TypeError("an attempt blocker must be a Blocker")


def _verified_links(
    links: tuple[VerificationLink, ...],
) -> tuple[VerificationLink, ...]:
    return tuple(
        link
        for link in links
        if link.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        )
    )


def _coverage_support(
    coverage: Coverage,
    links: tuple[VerificationLink, ...],
) -> tuple[VerificationLink, ...]:
    """The verified links that can support the requested coverage."""
    if coverage is Coverage.ONE_VERIFIED:
        return links
    if coverage is Coverage.SOUND_SET:
        return tuple(
            link
            for link in links
            if link.coverage in (Coverage.SOUND_SET, Coverage.COMPLETE_SET)
        )
    if coverage is Coverage.COMPLETE_SET:
        return tuple(
            link for link in links if link.coverage is Coverage.COMPLETE_SET
        )
    raise TypeError(f"unknown coverage requirement: {coverage!r}")


def _candidate_supports_completion(
    candidate: Candidate,
    problem: ProblemSpec,
) -> bool:
    """Whether one verified candidate may support a completed task.

    Coverage and parameter mode are separate promises.  A sound set satisfies a
    sound-set request, a complete set satisfies a complete-set request, and a
    generic parameter answer only satisfies a generic-parameter request.  The
    architecture states explicitly that a generic answer to an all-parameter
    request remains `PARTIALLY_SOLVED` (§18.1).

    A candidate outside the requested result language/scope cannot support
    completion even when an earlier link was verified.  `BLOCKED` is different:
    it describes the latest attempt, so it does not erase an earlier verified
    link.
    """
    if candidate.language_fit is not ResultLanguageFit.SATISFIES:
        return False
    if candidate.applicability is CandidateApplicability.OUT_OF_SCOPE:
        return False
    if candidate.coverage is CandidateCoverage.UNCLAIMED:
        return False
    if candidate.coverage is CandidateCoverage.GENERIC:
        return problem.parameter_mode is ParameterMode.GENERIC_PARAMETERS
    if problem.coverage is Coverage.COMPLETE_SET:
        return candidate.coverage is CandidateCoverage.COMPLETE
    if problem.coverage is Coverage.SOUND_SET:
        return candidate.coverage in (
            CandidateCoverage.PARTIAL,
            CandidateCoverage.COMPLETE,
        )
    return candidate.coverage is CandidateCoverage.COMPLETE


def derive_task_state(
    problem: ProblemSpec,
    candidates: tuple[Candidate, ...],
    links: tuple[VerificationLink, ...],
    blocker: Blocker | None,
    attempts: tuple[ExecutionAttempt, ...],
    *,
    cancelled: bool = False,
) -> TaskState:
    """Derive the user-visible task state from records and the fixed request.

    The table is the one in architecture §18.1:

    - a cancelled execution is `CANCELLED`, keeping any earlier candidates;
    - no candidates, attempts or blocker yet is `READY`;
    - with no verified or conditional link, a blocker is `BLOCKED` and a
      candidate without one is `PARTIALLY_SOLVED`;
    - `ONE_VERIFIED` is met by any verified link, `SOUND_SET` by a link whose
      coverage is sound or complete, and `COMPLETE_SET` by a complete link;
    - a supporting candidate must also satisfy the request's parameter promise:
      a generic answer does not complete an all-parameter request, and a
      partial answer does not complete a complete-set request;
    - met coverage with only unconditional supporting links is `COMPLETED`;
    - met coverage with an open condition is `COMPLETED_CONDITIONAL` only when
      the problem allows unresolved premises and every open condition is one
      of its explicit externalizable premises; otherwise it is
      `PARTIALLY_SOLVED`;
    - unmet coverage is `PARTIALLY_SOLVED`.

    The function only consumes the values passed in; it does not read the
    workspace or trust a state stored by the searcher.
    """
    if cancelled or any(
        attempt.state is ExecutionState.CANCELLED for attempt in attempts
    ):
        return TaskState.CANCELLED
    supporting = _verified_links(links)
    if not candidates and not attempts and blocker is None:
        return TaskState.READY
    if not supporting:
        if blocker is not None:
            return TaskState.BLOCKED
        if candidates:
            return TaskState.PARTIALLY_SOLVED
        raise ValueError(
            "an execution attempt needs a candidate or a blocker"
        )
    coverage_support = _coverage_support(problem.coverage, supporting)
    by_id = {candidate.id: candidate for candidate in candidates}
    coverage_support = tuple(
        link
        for link in coverage_support
        if link.candidate in by_id
        and _candidate_supports_completion(by_id[link.candidate], problem)
    )
    if not coverage_support:
        return TaskState.PARTIALLY_SOLVED
    open_conditions = tuple(
        condition
        for link in coverage_support
        for condition in (
            (() if link.condition is None else (link.condition,))
            + link.obligations
        )
    )
    if not open_conditions:
        return TaskState.COMPLETED
    if problem.allows_unresolved() and all(
        condition in problem.externalizable
        for condition in open_conditions
    ):
        return TaskState.COMPLETED_CONDITIONAL
    return TaskState.PARTIALLY_SOLVED


@dataclass(frozen=True, slots=True)
class RewriteRecord:
    """One manual rewrite or substitution, with its claimed direction."""

    source: ObjectVersionId
    result: ObjectVersionId
    occurrence: Occurrence | None
    relation: RewriteRelation
    justification: Proposition | None = None
    detail: str = ""

    def __post_init__(self) -> None:
        if not isinstance(self.relation, RewriteRelation):
            raise TypeError("a rewrite needs a RewriteRelation")
        if self.relation is RewriteRelation.SUBSTITUTION:
            if self.occurrence is not None:
                raise ValueError("a substitution has no single occurrence")
        elif self.occurrence is None:
            raise ValueError("a structural rewrite needs an occurrence")
        if self.justification is not None and not isinstance(
            self.justification, Proposition
        ):
            raise TypeError("a rewrite justification is a proposition")


@dataclass(frozen=True, slots=True)
class ConstructionRelation:
    """A typed relation between two constructed result versions.

    A construction relation is not a hypothesis or a theorem.  It records that
    one constructed version was related to another by a specification that an
    independent checker accepted, and the frame in which that construction was
    issued.  The relation is part of the revision snapshot, so undo hides it
    with the result it describes.
    """

    source: ObjectVersionId
    target: ObjectVersionId
    kind: str
    specification: Proposition
    frame: FrameId

    def __post_init__(self) -> None:
        _check_identifier(self.source, "a construction relation source")
        _check_identifier(self.target, "a construction relation target")
        if not isinstance(self.kind, str):
            raise TypeError("a construction relation kind must be a string")
        if not self.kind:
            raise ValueError("a construction relation needs a kind")
        if not isinstance(self.specification, Proposition):
            raise TypeError(
                "a construction relation needs a specification proposition"
            )
        _check_identifier(self.frame, "a construction relation frame")
        if self.kind == "function_extension" and self.source == self.target:
            raise ValueError(
                "a function extension relates two different versions"
            )


@dataclass(frozen=True, slots=True)
class CaseSplit:
    """A two-case split whose assumptions are exact complements."""

    id: CaseSplitId
    assumption: Proposition
    positive_frame: FrameId
    negative_frame: FrameId
    positive_revision: RevisionId
    negative_revision: RevisionId

    def __post_init__(self) -> None:
        if not isinstance(self.assumption, Proposition):
            raise TypeError("a case split needs an assumption proposition")
        if self.positive_frame == self.negative_frame:
            raise ValueError("a case split needs two distinct frames")


@dataclass(frozen=True, slots=True)
class ObjectFocus:
    """The UI points at one expression object version."""

    version: ObjectVersionId

    def __post_init__(self) -> None:
        _check_identifier(self.version, "an object focus version")


@dataclass(frozen=True, slots=True)
class TaskFocus:
    """The UI points at one task, not at a generated expression."""

    task: TaskId

    def __post_init__(self) -> None:
        _check_identifier(self.task, "a task focus task")


@dataclass(frozen=True, slots=True)
class CandidateFocus:
    """The UI points at one candidate, not at a verified expression."""

    candidate: CandidateId

    def __post_init__(self) -> None:
        _check_identifier(self.candidate, "a candidate focus candidate")


@dataclass(frozen=True, slots=True)
class OccurrenceFocus:
    """The UI points at one occurrence inside an expression version."""

    version: ObjectVersionId
    occurrence: Occurrence

    def __post_init__(self) -> None:
        _check_identifier(self.version, "an occurrence focus version")
        if not isinstance(self.occurrence, Occurrence):
            raise TypeError("an occurrence focus needs an Occurrence")


Focus: TypeAlias = (
    ObjectFocus | TaskFocus | CandidateFocus | OccurrenceFocus
)


def _check_focus(value: object, description: str) -> None:
    """A revision focus is one closed variant or no focus at all."""
    if value is None:
        return
    if not isinstance(
        value, (ObjectFocus, TaskFocus, CandidateFocus, OccurrenceFocus)
    ):
        raise TypeError(f"{description} must be a Focus or None")


class ActorKind(StrEnum):
    """Who initiated a user-level workspace action."""

    USER = "user"
    SCRIPT = "script"
    STRATEGY = "strategy"


@dataclass(frozen=True, slots=True)
class Event:
    """One recorded operation, fixed against the revision it changed.

    The event names the revision it started from and the revision it produced,
    the frame in which it was recorded, the object versions it read, and the
    request parameter snapshot.  `execution_report` is the observed outcome of
    the operation or attempt; it carries no mathematical truth.  `frame_digest`
    is the content identity of the recording frame, separate from its
    process-local `FrameId`.
    """

    id: EventId
    operation: str
    objects: tuple[ObjectVersionId, ...] = ()
    functions: tuple[ObjectVersionId, ...] = ()
    tasks: tuple[TaskId, ...] = ()
    attempts: tuple[ExecutionAttemptId, ...] = ()
    candidates: tuple[CandidateId, ...] = ()
    judgments: tuple[JudgmentId, ...] = ()
    input_revision: RevisionId | None = None
    frame: FrameId | None = None
    inputs: tuple[ObjectVersionId, ...] = ()
    parameters: tuple[tuple[str, object], ...] = ()
    output_revision: RevisionId | None = None
    execution_report: OperationStatus | None = None
    actor_kind: ActorKind = ActorKind.USER
    operation_version: str = ""
    frame_digest: str = ""

    def __post_init__(self) -> None:
        if not isinstance(self.actor_kind, ActorKind):
            raise TypeError("an event needs an ActorKind")
        if not isinstance(self.operation_version, str):
            raise TypeError("an event operation version must be a string")
        _check_frame_digest(self.frame_digest, "event frame digest")
        _check_optional_identifier(self.input_revision, "event input revision")
        _check_optional_identifier(self.frame, "event frame")
        _check_optional_identifier(self.output_revision, "event output revision")
        inputs = tuple(self.inputs)
        if any(
            isinstance(version, bool) or not isinstance(version, int)
            for version in inputs
        ):
            raise TypeError("event inputs must be object version ids")
        object.__setattr__(self, "inputs", inputs)
        parameters = tuple(self.parameters)
        for pair in parameters:
            if not isinstance(pair, tuple) or len(pair) != 2:
                raise TypeError(
                    "event parameters are a tuple of name/value pairs"
                )
            name, _ = pair
            if not isinstance(name, str) or not name:
                raise ValueError("an event parameter needs a non-empty name")
        object.__setattr__(self, "parameters", parameters)
        if self.execution_report is not None and not isinstance(
            self.execution_report, OperationStatus
        ):
            raise TypeError(
                "an event execution report must be an OperationStatus or None"
            )


@dataclass(frozen=True, slots=True)
class Revision:
    """One immutable snapshot of what the workspace shows.

    `generic_results` is part of the snapshot: a parameter family recorded in a
    later revision must not be visible after undo.  Keeping it here, rather
    than in a workspace-wide side table, makes visibility follow the same rule
    as objects and verification links.  One source version can carry several
    families (for example a derivative family and an antiderivative family
    computed from the same expression); the tuple keeps every recorded family
    in recording order, so a selector can distinguish their orientations.

    `focus` is a UI pointer only.  It names an object version, task, candidate
    or occurrence, or is `None` when the revision sets no focus; it never
    changes the mathematical context or the inputs an operation resolves.
    Keeping it in the snapshot makes undo/redo restore the same focus as the
    rest of the visible records.

    `task_records` and `candidate_records` are the exact task and candidate
    versions visible in this revision.  The workspace keeps a global version
    store, but visibility must follow the revision snapshot: a later check or
    edit must not leak into an older view after undo.

    `construction_relations` are the typed relations between constructed
    result versions visible in this revision.  They follow the same snapshot
    rule as objects and links: a relation recorded later is hidden by undo.

    `frame_digest` is the content identity of the revision's frame, not its
    process-local `FrameId`.  The start revision may leave it empty.
    """

    id: RevisionId
    frame: FrameId
    objects: tuple[ObjectVersionId, ...]
    links: tuple[VerificationLink, ...]
    events: tuple[EventId, ...]
    label: str
    world: WorldId
    parents: tuple[RevisionId, ...] = ()
    functions: tuple[ObjectVersionId, ...] = ()
    tasks: tuple[TaskId, ...] = ()
    attempts: tuple[ExecutionAttemptId, ...] = ()
    candidates: tuple[CandidateId, ...] = ()
    rewrites: tuple[RewriteRecord, ...] = ()
    case_splits: tuple[CaseSplit, ...] = ()
    construction_relations: tuple[ConstructionRelation, ...] = ()
    generic_results: tuple[
        tuple[ObjectVersionId, GenericResult], ...
    ] = ()
    structured_results: tuple[
        tuple[ObjectVersionId, StructuredResult], ...
    ] = ()
    producing_event: EventId | None = None
    focus: Focus | None = None
    task_records: tuple[TaskRecord, ...] = ()
    candidate_records: tuple[Candidate, ...] = ()
    object_names: tuple[tuple[ObjectVersionId, str], ...] = ()
    frame_digest: str = ""

    def __post_init__(self) -> None:
        _check_identifier(self.world, "revision world")
        _check_frame_digest(self.frame_digest, "revision frame digest")
        _check_optional_identifier(
            self.producing_event, "revision producing event"
        )
        _check_focus(self.focus, "revision focus")
        if len(set(self.parents)) != len(self.parents):
            raise ValueError("a revision repeats a parent")
        if len(set(self.functions)) != len(self.functions):
            raise ValueError("a revision repeats a function object")
        if len(set(self.tasks)) != len(self.tasks):
            raise ValueError("a revision repeats a task")
        if len(set(self.attempts)) != len(self.attempts):
            raise ValueError("a revision repeats an execution attempt")
        if len(set(self.candidates)) != len(self.candidates):
            raise ValueError("a revision repeats a candidate")
        if any(
            not isinstance(record, TaskRecord)
            for record in self.task_records
        ):
            raise TypeError(
                "revision task records must be TaskRecord values"
            )
        if len({record.id for record in self.task_records}) != len(
            self.task_records
        ):
            raise ValueError("a revision repeats a task record")
        if any(
            not isinstance(record, Candidate)
            for record in self.candidate_records
        ):
            raise TypeError(
                "revision candidate records must be Candidate values"
            )
        if len({record.id for record in self.candidate_records}) != len(
            self.candidate_records
        ):
            raise ValueError("a revision repeats a candidate record")
        name_versions = [version for version, _ in self.object_names]
        if len(set(name_versions)) != len(name_versions):
            raise ValueError("a revision repeats an object name")
        if any(
            not isinstance(name, str) or not name
            for _, name in self.object_names
        ):
            raise ValueError("a revision object name must be non-empty")
        if any(
            not isinstance(record, RewriteRecord) for record in self.rewrites
        ):
            raise TypeError("revision rewrites must be RewriteRecord values")
        if any(
            not isinstance(split, CaseSplit) for split in self.case_splits
        ):
            raise TypeError("revision case splits must be CaseSplit values")
        if any(
            not isinstance(relation, ConstructionRelation)
            for relation in self.construction_relations
        ):
            raise TypeError(
                "revision construction relations must be "
                "ConstructionRelation values"
            )
        relation_keys = [
            (relation.source, relation.target, relation.kind)
            for relation in self.construction_relations
        ]
        if len(set(relation_keys)) != len(relation_keys):
            raise ValueError("a revision repeats a construction relation")
        if any(
            not isinstance(family, GenericResult)
            for _, family in self.generic_results
        ):
            raise TypeError(
                "revision generic results must be GenericResult values"
            )
        structured_versions = [
            version for version, _ in self.structured_results
        ]
        if len(set(structured_versions)) != len(structured_versions):
            raise ValueError("a revision repeats a structured result")
        if any(
            not isinstance(result, StructuredResult)
            for _, result in self.structured_results
        ):
            raise TypeError(
                "revision structured results must be StructuredResult values"
            )


@dataclass(frozen=True, slots=True)
class FunctionApplicationResult:
    """The neutral expressions produced by applying one function value."""

    status: OperationStatus
    applications: tuple[Expression, ...] = ()
    conditions: tuple[T.Term, ...] = ()
    detail: str = ""


@dataclass(frozen=True, slots=True)
class CandidateEditResult:
    """The outcome of editing a candidate into a new unchecked version."""

    status: OperationStatus
    candidate: Candidate | None = None
    detail: str = ""


@dataclass(frozen=True, slots=True)
class OperationResult:
    """The generic outcome of one registered operation.

    `verifications` has one link per proposed specification; a candidate may be
    verified against more than one exact specification. `region` is the region
    on which the result is stated, and `trace` carries operation diagnostics
    such as whether a generic formula or a recomputation produced the result.

    A verified or conditional result carries its candidate and at least one
    verification link; a refuted result carries the refuted candidate.  Other
    statuses may legitimately carry an unverified candidate or no candidate.
    """

    operation: str
    status: OperationStatus
    candidate: Candidate | None
    verifications: tuple[VerificationLink, ...]
    result: Expression | None
    detail: str = ""
    region: Proposition | None = None
    generic: GenericResult | None = None
    trace: tuple[str, ...] = ()
    task: TaskRecord | None = None
    structured: StructuredResult | None = None
    blocker: Blocker | None = None

    def __post_init__(self) -> None:
        if self.blocker is not None and not isinstance(self.blocker, Blocker):
            raise TypeError("an operation blocker must be a Blocker")
        if self.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            if self.candidate is None:
                raise ValueError(
                    f"a {self.status.value} result needs a candidate"
                )
            if not self.verifications:
                raise ValueError(
                    f"a {self.status.value} result needs a verification"
                )
        if (
            self.status is OperationStatus.REFUTED
            and self.candidate is None
        ):
            raise ValueError("a refuted result needs a candidate")


@dataclass(frozen=True, slots=True)
class AssumptionResult:
    """The outcome of introducing one hypothesis in a child frame."""

    status: OperationStatus
    frame: FrameId
    proposition: Proposition | None
    judgment: JudgmentId | None
    detail: str = ""
    consistency: FrameConsistency = Unassessed()


@dataclass(frozen=True, slots=True)
class DeclarationResult:
    """The outcome of declaring one symbol in a child frame.

    A declaration is a context extension, not a proposition, so a successful
    result carries the declaration and the child frame but no judgment.
    """

    status: OperationStatus
    frame: FrameId
    declaration: Declaration | None
    detail: str = ""

    def __post_init__(self) -> None:
        if self.declaration is not None and not isinstance(
            self.declaration, Declaration
        ):
            raise TypeError("a declaration result carries a Declaration")
        _check_context_extension(
            self.status,
            self.frame,
            self.declaration,
            self.detail,
            description="declaration",
        )


@dataclass(frozen=True, slots=True)
class DefinitionResult:
    """The outcome of defining one alias in a child frame.

    A definition is a context extension, not a proposition, so a successful
    result carries the definition and the child frame but no judgment.
    """

    status: OperationStatus
    frame: FrameId
    definition: Definition | None
    detail: str = ""

    def __post_init__(self) -> None:
        if self.definition is not None and not isinstance(
            self.definition, Definition
        ):
            raise TypeError("a definition result carries a Definition")
        _check_context_extension(
            self.status,
            self.frame,
            self.definition,
            self.detail,
            description="definition",
        )


@dataclass(frozen=True, slots=True)
class RewriteResult:
    """The outcome of one manual rewrite or substitution."""

    status: OperationStatus
    source: Expression | None = None
    result: Expression | None = None
    record: RewriteRecord | None = None
    detail: str = ""


@dataclass(frozen=True, slots=True)
class CaseSplitResult:
    """The outcome of creating a two-case revision split."""

    status: OperationStatus
    split: CaseSplit | None = None
    detail: str = ""


@dataclass(frozen=True, slots=True)
class CaseMergeResult:
    """The outcome of merging the two branches of a trusted case split."""

    status: OperationStatus
    split: CaseSplit | None = None
    revision: Revision | None = None
    detail: str = ""


@dataclass(frozen=True, slots=True)
class CaseConclusionResult:
    """The outcome of issuing a conclusion by two-case analysis."""

    status: OperationStatus
    judgment: JudgmentId | None = None
    proposition: Proposition | None = None
    detail: str = ""


__all__ = [
    "ActorKind",
    "Artifact",
    "AssumptionResult",
    "Candidate",
    "CandidateApplicability",
    "CandidateCoverage",
    "CandidateEditResult",
    "CandidateFocus",
    "CandidateState",
    "CaseConclusionResult",
    "CaseMergeResult",
    "CaseSplit",
    "CaseSplitResult",
    "ConstructionRelation",
    "DeclarationResult",
    "DefinitionResult",
    "Event",
    "ExecutionAttempt",
    "ExecutionState",
    "Expression",
    "Focus",
    "FunctionApplicationResult",
    "FunctionDefined",
    "FunctionDefinitionOutcome",
    "FunctionObject",
    "FunctionRefused",
    "ObjectFocus",
    "ObjectVersion",
    "OccurrenceFocus",
    "OperationResult",
    "OperationStatus",
    "ResultLanguageFit",
    "Revision",
    "RewriteRecord",
    "RewriteRelation",
    "RewriteResult",
    "TaskFocus",
    "TaskOrigin",
    "TaskRecord",
    "TaskState",
    "VerificationLink",
    "derive_task_state",
]
