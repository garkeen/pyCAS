"""Workspace: generic operation application, records and history.

The workspace owns presentation and history, never mathematics. It resolves
current object versions, asks the registered operation for a problem and a
proposal, commits the proposal through the declared checker binding, and records
the resulting expression, verification links, event and revision.

Differentiation and specialisation are registered operations, not branches in
this module. Adding another operation does not change this file. The
`differentiate` and `specialize` methods below are client conveniences over
`apply`: they assemble a request and contain no mathematical rule. They are not
a dispatch table and do not need to grow when an operation is registered.

Declarations and definitions extend the frame only through `FrameStore.create`.
They record context, not a judgment, and never pass through `_commit`.
"""

from __future__ import annotations

import re
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from dataclasses import replace
from fractions import Fraction
from typing import TYPE_CHECKING, Any

from cas.foundation.ids import (
    CandidateId,
    CaseSplitId,
    EventId,
    ExecutionAttemptId,
    FrameId,
    IdIssuer,
    JudgmentId,
    ObjectId,
    ObjectVersionId,
    RevisionId,
    SymbolId,
    TaskId,
)
from cas.kernel.case_merge import CaseMergeCertificate
from cas.kernel.commit import (
    CommitProposal,
    Committed,
    Deferred,
    Rejected,
    RejectedKind,
    ValidatedCommitBatch,
    publish_commit,
    validate_commit,
)
from cas.kernel.consistency import assess_consistency
from cas.kernel.context_rules import HypothesisChecker
from cas.kernel.model import Applicability, Inconsistent
from cas.kernel.verdict import Verdict, decide
from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.decisions import Blocker, Reason
from cas.language.execution import ConditionPolicy, ExecutionBudget
from cas.language.functions import (
    FunctionParameter,
    FunctionRepresentation,
    FunctionValue,
)
from cas.language.problems import (
    Coverage,
    ParameterMode,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.sets import set_members
from cas.language.signatures import StructuralHead
from cas.language.sorts import Sort
from cas.operations.protocols import (
    ExecutionRequest,
    FunctionComparisonInput,
    FunctionExtensionInput,
    GenericResultInput,
    OperationRequest,
    OperationSpec,
    ProblemBuilt,
    ProblemInvalid,
    ProblemUnsupported,
    ProposalInvalid,
    ProposalUnsupported,
    Proposed,
    ResultShape,
    StructuredResult,
    ValueMappingInput,
    blocked_problem,
)
from cas.semantics import elaborate
from cas.semantics.frames import Declaration, Definition, Hypothesis
from cas.semantics.regions import proved_subregion, region_from_proposition
from cas.semantics.specialization import CoverageClaim, GenericResult
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.syntax.occurrences import (
    Occurrence,
    replace_at,
    subterm_at,
)
from cas.syntax.occurrences import (
    occurrences as structural_occurrences,
)
from cas.workflow.records import (
    AssumptionResult,
    Candidate,
    CandidateApplicability,
    CandidateCoverage,
    CandidateEditResult,
    CandidateFocus,
    CandidateState,
    CaseConclusionResult,
    CaseMergeResult,
    CaseSplit,
    CaseSplitResult,
    ConstructionRelation,
    DeclarationResult,
    DefinitionResult,
    Event,
    ExecutionAttempt,
    ExecutionState,
    Expression,
    Focus,
    FunctionApplicationResult,
    FunctionDefined,
    FunctionDefinitionOutcome,
    FunctionObject,
    FunctionRefused,
    ObjectFocus,
    ObjectVersion,
    OccurrenceFocus,
    OperationResult,
    OperationStatus,
    ResultLanguageFit,
    Revision,
    RewriteRecord,
    RewriteRelation,
    RewriteResult,
    TaskFocus,
    TaskOrigin,
    TaskRecord,
    TaskState,
    VerificationLink,
    derive_task_state,
)

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")


class _CaseSplitRefused(Exception):
    """A branch hypothesis was refused; the split must roll back as a whole."""


class _KeepFocus:
    """Sentinel: a revision inherits its parent's focus."""

    __slots__ = ()


_KEEP_FOCUS = _KeepFocus()


class Workspace:
    """One session over an assembled runtime."""

    def __init__(self, runtime: Runtime[Any]) -> None:
        self._runtime = runtime
        self._objects = IdIssuer()
        self._versions = IdIssuer()
        self._candidate_ids = IdIssuer()
        self._event_ids = IdIssuer()
        self._task_ids = IdIssuer()
        self._attempt_ids = IdIssuer()
        self._case_split_ids = IdIssuer()
        self._expressions: dict[ObjectVersionId, Expression] = {}
        self._functions: dict[ObjectVersionId, FunctionObject] = {}
        self._candidates: dict[CandidateId, Candidate] = {}
        self._tasks: dict[TaskId, TaskRecord] = {}
        self._attempts: dict[ExecutionAttemptId, ExecutionAttempt] = {}
        self._case_splits: dict[CaseSplitId, CaseSplit] = {}
        self._events: dict[EventId, Event] = {}
        self._revision_ids = IdIssuer()
        start = Revision(
            id=RevisionId(self._revision_ids.issue()),
            frame=runtime.frame.id,
            objects=(),
            links=(),
            events=(),
            label="start",
            world=runtime.world.id,
        )
        self._revisions: dict[RevisionId, Revision] = {start.id: start}
        self._children: dict[RevisionId, list[RevisionId]] = {}
        self._head = start.id

    def _commit(
        self, proposal: CommitProposal
    ) -> Committed | Deferred | Rejected:
        """Validate one submission and publish its batch, or return refusal."""
        validated = validate_commit(self._runtime.store, proposal)
        if isinstance(validated, ValidatedCommitBatch):
            return publish_commit(self._runtime.store, validated)
        return validated

    # --- the current view ---

    @property
    def revision(self) -> Revision:
        return self._revisions[self._head]

    def revision_at(self, identifier: RevisionId) -> Revision:
        """The recorded revision with this id, including hidden branches."""
        return self._revisions[identifier]

    @property
    def frame(self) -> FrameId:
        return self.revision.frame

    @property
    def focus(self) -> Focus | None:
        """The UI pointer recorded in the visible revision, not an input."""
        return self.revision.focus

    def expressions(self) -> tuple[Expression, ...]:
        return tuple(
            self._expressions[version] for version in self.revision.objects
        )

    def functions(self) -> tuple[FunctionObject, ...]:
        """The explicit function objects visible in the current revision."""
        return tuple(
            self._functions[version] for version in self.revision.functions
        )

    def object_version(
        self, version: ObjectVersionId
    ) -> ObjectVersion | None:
        """The typed view of one visible object version, or `None`.

        Visibility follows the revision snapshot, not the global version
        store: a version recorded in a later revision is not returned after
        undo, and an unknown version is `None` rather than a fabricated view.
        The returned view references the stored expression or function record;
        it is not a second authority over the object's payload.
        """
        if version in self.revision.objects:
            return self._expressions[version].object_version
        if version in self.revision.functions:
            return self._functions[version].object_version
        return None

    def links(self) -> tuple[VerificationLink, ...]:
        return self.revision.links

    def construction_relations(self) -> tuple[ConstructionRelation, ...]:
        """The typed construction relations visible in the current revision."""
        return self.revision.construction_relations

    def events(self) -> tuple[Event, ...]:
        revision = self.revision
        if (
            revision.producing_event is not None
            and revision.producing_event not in revision.events
        ):
            raise ValueError(
                "the visible revision names a producing event outside its "
                "history"
            )
        return tuple(self._events[event] for event in revision.events)

    def candidate(self, identifier: CandidateId) -> Candidate:
        """One candidate visible in the current revision, or `KeyError`.

        Candidate records are versioned.  Looking up the global store directly
        would return a later check or edit after undo, so the revision snapshot
        is the only visibility authority.
        """
        for candidate in self.revision.candidate_records:
            if candidate.id == identifier:
                return candidate
        raise KeyError(identifier)

    def candidates(self) -> tuple[Candidate, ...]:
        """The candidates visible in the current revision."""
        return self.revision.candidate_records

    def task(self, identifier: TaskId) -> TaskRecord:
        """One task visible in the current revision, or `KeyError`."""
        for task in self.revision.task_records:
            if task.id == identifier:
                return task
        raise KeyError(identifier)

    def tasks(self) -> tuple[TaskRecord, ...]:
        """The tasks visible in the current revision."""
        return self.revision.task_records

    # --- manual problems and execution attempts ---

    def define_problem(
        self,
        operation: str,
        inputs: tuple[Expression, ...],
        *,
        target: SymbolId | None = None,
        region: Pr.Proposition | None = None,
        result_language: ResultLanguage | None = None,
        coverage: Coverage = Coverage.ONE_VERIFIED,
        parameter_mode: ParameterMode | None = None,
        externalizable: tuple[Pr.Proposition, ...] = (),
        depends_on: tuple[TaskId, ...] = (),
        label: str = "",
    ) -> TaskRecord:
        """Record a fixed problem without executing it.

        Admission is the same as `apply`: the registered operation's
        `build_problem` must accept the request and fix exactly the problem the
        user described.  A structured refusal records a blocked task with the
        operation's fixed problem and its blocker; an invalid request raises
        `ValueError` without writing.  `run_task` later executes the registered
        operation and again requires it to build exactly this problem.

        `externalizable` is the explicit set of premises the answer may leave
        outside the result.  The fixed problem always carries exactly this set;
        it is not rejected here.  Whether a conditional result is complete is
        derived later by `derive_task_state` from the actual open conditions.

        The new revision focuses the defined task: the task is the object the
        user is managing, while its input expressions remain reachable by
        version.
        """
        with self._transaction():
            if self._runtime.store.consistency(
                self.frame
            ).is_inconsistent():
                raise ValueError("the current frame is inconsistent")
            registered = self._runtime.operations.get(operation)
            if registered is None:
                raise KeyError(f"operation not registered: {operation}")
            if not inputs:
                raise ValueError("a problem needs at least one input")
            for expression in inputs:
                issue = self._input_issue(expression)
                if issue is not None:
                    raise ValueError(issue[1])
            if region is not None and not self._runtime.frames.readable(
                region, self.frame
            ):
                raise ValueError("the problem region is outside the frame")
            for premise in externalizable:
                if not self._runtime.frames.readable(premise, self.frame):
                    raise ValueError(
                        "an externalizable premise is outside the frame"
                    )
            for dependency in depends_on:
                if self._visible_task(dependency) is None:
                    raise KeyError(f"unknown task dependency: {dependency}")
            request = OperationRequest(
                self.frame,
                tuple(expression.term for expression in inputs),
                target,
                region,
                coverage,
                result_language,
                parameter_mode,
            )
            input_versions = tuple(
                expression.version for expression in inputs
            )
            outcome = registered.build_problem(request)
            if isinstance(outcome, ProblemUnsupported):
                blocker = Blocker(
                    outcome.reason,
                    outcome.detail,
                    missing=outcome.missing,
                    conditions=outcome.conditions,
                    attempted=outcome.attempted,
                    target=(
                        None
                        if outcome.problem is None
                        else outcome.problem.region
                    ),
                )
                if outcome.problem is None:
                    raise ValueError(outcome.detail)
                return self._record_blocked_definition(
                    blocked_problem(
                        request,
                        replace(
                            outcome.problem,
                            externalizable=externalizable,
                        ),
                    ),
                    outcome.detail,
                    blocker,
                    depends_on,
                    input_versions,
                )
            if isinstance(outcome, ProblemInvalid):
                raise ValueError(outcome.detail)
            if not isinstance(outcome, ProblemBuilt):
                raise TypeError(
                    "an operation returned an unknown problem outcome"
                )
            # The request's explicit set is the only authority.  An operation
            # must not silently drop the task's externalizable premises, and it
            # must not inject a set the user did not request either.
            problem = replace(
                outcome.problem, externalizable=externalizable
            )
            problem_issue = self._problem_structure_issue(
                request, problem
            )
            if problem_issue is None and not any(
                binding.problem_kind == problem.operation
                for binding in registered.checker_bindings
            ):
                problem_issue = (
                    "the problem kind does not match the operation's "
                    "checker binding"
                )
            if problem_issue is None:
                problem_issue = self._problem_dimension_issue(
                    request, problem
                )
            if (
                problem_issue is None
                and not registered.result_schema.accepts(
                    problem.result_language
                )
            ):
                problem_issue = (
                    "the operation does not support "
                    f"{problem.result_language.value} results"
                )
            if (
                problem_issue is None
                and problem.coverage != request.coverage
            ):
                problem_issue = (
                    "the problem does not describe the requested coverage"
                )
            if problem_issue is not None:
                return self._record_blocked_definition(
                    problem,
                    problem_issue,
                    Blocker(
                        Reason.FRAGMENT,
                        problem_issue,
                        target=problem.region,
                    ),
                    depends_on,
                    input_versions,
                )
            task_id = TaskId(self._task_ids.issue())
            event = self._record_event(
                "DefineProblem",
                tasks=(task_id,),
                inputs=input_versions,
            )
            task = TaskRecord(
                task_id,
                problem,
                self.frame,
                derive_task_state(problem, (), (), None, ()),
                (),
                label,
                TaskOrigin.MANUAL,
                None,
                depends_on,
                input_versions,
                (),
            )
            self._tasks[task.id] = task
            self._append_revision(
                f"define problem {task.id}",
                event,
                focus=TaskFocus(task.id),
            )
            return task

    def run_task(self, identifier: TaskId) -> OperationResult:
        """Execute one visible manual task and require the same problem.

        The final revision focuses the task, not the generated result
        expression: running is a task action, and the result remains a visible
        object with its own version.
        """
        with self._transaction():
            task = self._visible_task(identifier)
            if task is None:
                return self._failure(
                    "run_task",
                    OperationStatus.INVALID,
                    "the task is not visible in the current revision",
                )
            if task.origin is not TaskOrigin.MANUAL:
                return self._failure(
                    "run_task",
                    OperationStatus.INVALID,
                    "only a manual task can be run",
                )
            if task.state is TaskState.CANCELLED:
                return self._failure(
                    "run_task",
                    OperationStatus.INVALID,
                    "the task is cancelled",
                )
            if task.state is TaskState.BLOCKED and not task.attempts:
                return self._failure(
                    "run_task",
                    OperationStatus.INVALID,
                    "the problem was refused when it was defined",
                )
            inputs: list[Expression] = []
            for version in task.inputs:
                expression = self._expressions.get(version)
                if (
                    expression is None
                    or version not in self.revision.objects
                ):
                    return self._block_manual_task(
                        task,
                        "an input object is no longer visible",
                        Blocker(
                            Reason.GUARDED,
                            "an input object is no longer visible in the "
                            "current revision",
                            missing=frozenset({"visible_input_object"}),
                            target=task.problem.region,
                        ),
                    )
                inputs.append(expression)
            result = self._apply(
                task.problem.operation,
                tuple(inputs),
                target=task.problem.target,
                region=task.problem.region,
                coverage=task.problem.coverage,
                result_language=task.problem.result_language,
                parameter_mode=task.problem.parameter_mode,
                externalizable=task.problem.externalizable,
            )
            execution = result.task
            if execution is None:
                return self._block_manual_task(
                    task,
                    result.detail or "the execution did not record a task",
                    result.blocker,
                )
            if not self._same_problem(task.problem, execution.problem):
                return self._block_manual_task(
                    task,
                    "the operation built a different problem",
                )
            execution = replace(
                execution,
                state=derive_task_state(
                    execution.problem,
                    self._task_candidates(execution.candidates),
                    self._task_links(execution.candidates),
                    execution.blocker,
                    self._task_attempts(execution.attempts),
                ),
                parent=task.id,
            )
            self._tasks[execution.id] = execution
            candidates = tuple(
                dict.fromkeys(task.candidates + execution.candidates)
            )
            attempts = tuple(
                dict.fromkeys(task.attempts + execution.attempts)
            )
            manual_state = derive_task_state(
                task.problem,
                self._task_candidates(candidates),
                self._task_links(candidates),
                execution.blocker,
                self._task_attempts(attempts),
            )
            completed = manual_state in (
                TaskState.COMPLETED,
                TaskState.COMPLETED_CONDITIONAL,
            )
            updated = replace(
                task,
                state=manual_state,
                candidates=candidates,
                detail=task.detail if completed else execution.detail,
                attempts=attempts,
                blocker=None if completed else execution.blocker,
            )
            self._tasks[updated.id] = updated
            event = self._record_event(
                "RunTask",
                tasks=(updated.id, execution.id),
                attempts=execution.attempts,
                candidates=execution.candidates,
                inputs=task.inputs,
                execution_report=result.status,
            )
            self._append_revision(
                f"run task {updated.id}",
                event,
                focus=TaskFocus(updated.id),
            )
            return replace(result, task=updated)

    def cancel_task(self, identifier: TaskId) -> OperationResult:
        """Cancel a task that has not already completed.

        Cancellation keeps the task as the visible focus.
        """
        with self._transaction():
            task = self._visible_task(identifier)
            if task is None:
                return self._failure(
                    "cancel_task",
                    OperationStatus.INVALID,
                    "the task is not visible in the current revision",
                )
            if task.state in (
                TaskState.COMPLETED,
                TaskState.COMPLETED_CONDITIONAL,
            ):
                return self._failure(
                    "cancel_task",
                    OperationStatus.INVALID,
                    "a completed task keeps its proof",
                )
            if task.state is TaskState.CANCELLED:
                return self._failure(
                    "cancel_task",
                    OperationStatus.INVALID,
                    "the task is already cancelled",
                )
            attempt = self._record_attempt(
                task.id,
                ExecutionState.CANCELLED,
                None,
                "cancelled by the user",
            )
            updated = replace(
                task,
                state=derive_task_state(
                    task.problem,
                    self._task_candidates(task.candidates),
                    self._task_links(task.candidates),
                    task.blocker,
                    self._task_attempts(task.attempts + (attempt.id,)),
                    cancelled=True,
                ),
                detail="cancelled by the user",
                attempts=task.attempts + (attempt.id,),
            )
            self._tasks[updated.id] = updated
            event = self._record_event(
                "CancelTask",
                tasks=(updated.id,),
                attempts=(attempt.id,),
                inputs=task.inputs,
                execution_report=OperationStatus.APPLIED,
            )
            self._append_revision(
                f"cancel task {updated.id}",
                event,
                focus=TaskFocus(updated.id),
            )
            return OperationResult(
                "cancel_task",
                OperationStatus.APPLIED,
                None,
                (),
                None,
                updated.detail,
                None,
                None,
                (),
                updated,
            )

    def task_graph(
        self,
    ) -> tuple[tuple[TaskId, tuple[TaskId, ...]], ...]:
        """The visible construction graph, as task-to-dependencies edges."""
        edges: list[tuple[TaskId, tuple[TaskId, ...]]] = []
        for task in self.tasks():
            dependencies = task.depends_on
            if task.parent is not None:
                dependencies = dependencies + (task.parent,)
            edges.append((task.id, tuple(dict.fromkeys(dependencies))))
        return tuple(edges)

    def _block_manual_task(
        self,
        task: TaskRecord,
        detail: str,
        blocker: Blocker | None = None,
    ) -> OperationResult:
        if blocker is None:
            blocker = Blocker(
                Reason.FRAGMENT,
                detail,
                target=task.problem.region,
            )
        elif blocker.target is None and task.problem.region is not None:
            blocker = replace(blocker, target=task.problem.region)
        attempt = self._record_attempt(
            task.id,
            ExecutionState.BLOCKED,
            OperationStatus.INVALID,
            detail,
            blocker=blocker,
        )
        attempts = task.attempts + (attempt.id,)
        derived_state = derive_task_state(
            task.problem,
            self._task_candidates(task.candidates),
            self._task_links(task.candidates),
            blocker,
            self._task_attempts(attempts),
        )
        completed = derived_state in (
            TaskState.COMPLETED,
            TaskState.COMPLETED_CONDITIONAL,
        )
        updated = replace(
            task,
            state=derived_state,
            detail=task.detail if completed else detail,
            attempts=attempts,
            blocker=None if completed else blocker,
        )
        self._tasks[updated.id] = updated
        event = self._record_event(
            "RunTask",
            tasks=(updated.id,),
            attempts=(attempt.id,),
            inputs=task.inputs,
            execution_report=OperationStatus.INVALID,
        )
        self._append_revision(
            f"block task {updated.id}",
            event,
            focus=TaskFocus(updated.id),
        )
        return self._failure(
            "run_task",
            OperationStatus.INVALID,
            detail,
            task=updated,
            blocker=blocker,
        )

    def attempt(self, identifier: ExecutionAttemptId) -> ExecutionAttempt:
        return self._attempts[identifier]

    def attempts(self) -> tuple[ExecutionAttempt, ...]:
        """The execution attempts visible in the current revision."""
        return tuple(
            self._attempts[identifier]
            for identifier in self.revision.attempts
        )

    def rewrites(self) -> tuple[RewriteRecord, ...]:
        """The manual rewrites visible in the current revision."""
        return self.revision.rewrites

    def case_splits(self) -> tuple[CaseSplit, ...]:
        """The trusted case splits visible in the current revision."""
        return self.revision.case_splits

    def applicability(self, judgment: JudgmentId) -> Applicability:
        return self._runtime.store.applicability(judgment, self.frame)

    # --- manual candidate interaction ---

    def edit_candidate(
        self,
        identifier: CandidateId,
        term: T.Term,
    ) -> CandidateEditResult:
        """Create a new unchecked candidate; the old one stays in history.

        Editing never transfers the old certificate to the new term.  A manual
        check of the edited candidate therefore refuses until a new certificate
        is produced by an operation.
        """
        with self._transaction():
            candidate = self._visible_candidate(identifier)
            if candidate is None:
                return CandidateEditResult(
                    OperationStatus.INVALID,
                    None,
                    "the candidate is not visible in the current revision",
                )
            if not isinstance(term, T.Term):
                return CandidateEditResult(
                    OperationStatus.INVALID,
                    None,
                    "an edited candidate needs a term",
                )
            task = self._visible_task(candidate.task)
            if task is None:
                return CandidateEditResult(
                    OperationStatus.INVALID,
                    None,
                    "the candidate has no visible task",
                )
            operation = self._runtime.operations.get(
                candidate.problem.operation
            )
            language_fit, _ = self._result_language_fit(
                operation, candidate.problem, term, None
            )
            applicability = (
                CandidateApplicability.OUT_OF_SCOPE
                if language_fit is ResultLanguageFit.DOES_NOT_SATISFY
                else CandidateApplicability.APPLICABLE
            )
            edited = Candidate(
                CandidateId(self._candidate_ids.issue()),
                candidate.task,
                candidate.problem,
                term,
                candidate.frame,
                CandidateState.UNCHECKED,
                applicability=applicability,
                coverage=CandidateCoverage.UNCLAIMED,
                language_fit=language_fit,
                candidate_role=candidate.candidate_role,
                certificate_required=candidate.certificate_required,
                algebra=candidate.algebra,
            )
            self._candidates[edited.id] = edited
            candidates = task.candidates + (edited.id,)
            # Editing adds a new unchecked candidate; earlier candidates and
            # their verification links remain visible.  The task state is
            # derived from all of them, so editing an already completed task
            # does not erase its existing verified answer.
            self._tasks[task.id] = replace(
                task,
                state=derive_task_state(
                    task.problem,
                    self._task_candidates(candidates, (edited,)),
                    self._task_links(candidates, extra_candidates=(edited,)),
                    task.blocker,
                    self._task_attempts(task.attempts),
                ),
                candidates=candidates,
                detail="candidate edited; certificate cleared",
            )
            event = self._record_event(
                "EditCandidate",
                tasks=(task.id,),
                candidates=(edited.id,),
                inputs=task.inputs,
                execution_report=OperationStatus.EDITED,
            )
            self._append_revision(
                f"edit candidate {edited.id}",
                event,
                focus=CandidateFocus(edited.id),
            )
            return CandidateEditResult(
                OperationStatus.EDITED, edited, "candidate edited"
            )

    def check_candidate(self, identifier: CandidateId) -> OperationResult:
        """Re-run the recorded checker for one visible candidate.

        A candidate edited by `edit_candidate` has no certificate and is refused
        honestly; it is not silently promoted to a trusted result.
        """
        with self._transaction():
            candidate = self._visible_candidate(identifier)
            if candidate is None:
                return self._failure(
                    "check",
                    OperationStatus.INVALID,
                    "the candidate is not visible in the current revision",
                )
            if (
                not candidate.specifications
                or not candidate.specification_kind
                or not candidate.checker_id
                or (
                    candidate.certificate_required
                    and candidate.certificate is None
                )
            ):
                return self._failure(
                    "check",
                    OperationStatus.INVALID,
                    "the candidate has no certificate; edit creates a new "
                    "unchecked candidate",
                )
            if not self._runtime.frames.is_visible(
                candidate.frame, self.frame
            ):
                return self._failure(
                    "check",
                    OperationStatus.INVALID,
                    "the candidate frame is outside the current view",
                )
            committed = self._commit(self._candidate_proposal(candidate))
            judgments: tuple[JudgmentId, ...] = ()
            blocker: Blocker | None = None
            open_obligations: tuple[Pr.Proposition, ...] = ()
            if isinstance(committed, Committed):
                open_obligations = self._open_obligations(committed)
                status = (
                    OperationStatus.CONDITIONAL
                    if candidate.result_region is not None
                    or open_obligations
                    else OperationStatus.VERIFIED
                )
                judgments = committed.judgments
                detail = ""
                candidate_state = CandidateState.VERIFIED
                applicability = (
                    CandidateApplicability.CONDITIONAL
                    if status is OperationStatus.CONDITIONAL
                    else CandidateApplicability.APPLICABLE
                )
                coverage = candidate.coverage
                language_fit = candidate.language_fit
            elif isinstance(committed, Rejected):
                status, candidate_state, applicability, blocker = (
                    self._rejected_projection(
                        committed,
                        target=candidate.specifications[0],
                        budget=None,
                        attempted=(candidate.checker_id,),
                    )
                )
                coverage = (
                    CandidateCoverage.UNCLAIMED
                    if status is not OperationStatus.CONDITIONAL
                    else candidate.coverage
                )
                language_fit = candidate.language_fit
                detail = committed.detail
            elif isinstance(committed, Deferred):
                status = self._status_for(committed.reason)
                blocker = Blocker(
                    committed.reason,
                    committed.detail,
                    missing=committed.missing,
                    conditions=committed.conditions,
                    target=candidate.specifications[0],
                )
                candidate_state = CandidateState.UNVERIFIED
                applicability = CandidateApplicability.BLOCKED
                coverage = candidate.coverage
                language_fit = candidate.language_fit
                detail = committed.detail
            else:
                raise TypeError("commit returned an unknown result")

            candidate = candidate.checked(
                candidate_state,
                applicability=applicability,
                coverage=coverage,
                language_fit=language_fit,
            )
            self._candidates[candidate.id] = candidate
            task = self._visible_task(candidate.task)
            if task is None:
                raise AssertionError("a checked candidate has no visible task")
            link_status = (
                OperationStatus.VERIFIED
                if status in (
                    OperationStatus.VERIFIED,
                    OperationStatus.CONDITIONAL,
                )
                else status
            )
            links = tuple(
                VerificationLink(
                    candidate=candidate.id,
                    specification=specification,
                    judgment=(
                        judgments[index] if index < len(judgments) else None
                    ),
                    status=link_status,
                    specification_kind=candidate.specification_kind,
                    frame=candidate.frame,
                    coverage=candidate.problem.coverage,
                    condition=candidate.result_region,
                    obligations=open_obligations,
                )
                for index, specification in enumerate(
                    candidate.specifications
                )
            )
            attempt_state = (
                ExecutionState.FINISHED
                if status
                in (OperationStatus.VERIFIED, OperationStatus.CONDITIONAL)
                else ExecutionState.BLOCKED
            )
            attempt = self._record_attempt(
                task.id, attempt_state, status, detail, blocker=blocker
            )
            attempts = task.attempts + (attempt.id,)
            derived_state = derive_task_state(
                task.problem,
                self._task_candidates(task.candidates, (candidate,)),
                self._task_links(
                    task.candidates,
                    links,
                    extra_candidates=(candidate,),
                ),
                blocker,
                self._task_attempts(attempts),
            )
            completed = derived_state in (
                TaskState.COMPLETED,
                TaskState.COMPLETED_CONDITIONAL,
            )
            task = replace(
                task,
                state=derived_state,
                detail=task.detail if completed else detail,
                attempts=attempts,
                blocker=None if completed else blocker,
            )
            self._tasks[task.id] = task
            result: Expression | None = None
            if status in (
                OperationStatus.VERIFIED,
                OperationStatus.CONDITIONAL,
            ):
                result = self._record_expression(
                    candidate.term,
                    f"check candidate {candidate.id}",
                    "Check",
                )
            event = self._record_event(
                "Check",
                objects=() if result is None else (result.version,),
                tasks=(task.id,),
                attempts=(attempt.id,),
                candidates=(candidate.id,),
                judgments=judgments,
                inputs=task.inputs,
                parameters=(),
                execution_report=status,
            )
            self._append_revision(
                f"check candidate {candidate.id}",
                event,
                links,
                focus=(
                    ObjectFocus(result.version)
                    if result is not None
                    else CandidateFocus(candidate.id)
                ),
            )
            return OperationResult(
                "check",
                status,
                candidate,
                links,
                result,
                detail,
                candidate.result_region,
                None,
                (),
                task,
                blocker=blocker,
            )

    def decide_candidate(self, identifier: CandidateId) -> Verdict:
        """Check one visible candidate without publishing or recording.

        The submission is exactly the one `check_candidate` would make: the
        candidate's recorded specification, certificate and problem.  `decide`
        validates it and returns a receipt or blocker; it never publishes the
        batch, updates the candidate/task, or appends an event or revision.
        A missing or hidden candidate is refused instead of being reported as
        an unknown mathematical answer.
        """
        candidate = self._visible_candidate(identifier)
        if candidate is None:
            raise ValueError(
                "the candidate is not visible in the current revision"
            )
        if (
            not candidate.specifications
            or not candidate.specification_kind
            or not candidate.checker_id
            or (
                candidate.certificate_required
                and candidate.certificate is None
            )
        ):
            raise ValueError(
                "the candidate has no certificate; edit creates a new "
                "unchecked candidate"
            )
        if not self._runtime.frames.is_visible(
            candidate.frame, self.frame
        ):
            raise ValueError("the candidate frame is outside the current view")
        return decide(
            self._runtime.store, self._candidate_proposal(candidate)
        )

    def _candidate_proposal(self, candidate: Candidate) -> CommitProposal:
        """The exact submission a manual re-check of `candidate` makes."""
        return CommitProposal(
            candidate.frame,
            candidate.specifications,
            candidate.checker_id,
            candidate.problem.operation,
            candidate.specification_kind,
            certificate=candidate.certificate,
            problem=candidate.problem,
            candidate=candidate.term,
            candidate_role=candidate.candidate_role,
            structured=candidate.structured,
            algebra=candidate.algebra,
        )

    def _visible_candidate(
        self, identifier: CandidateId
    ) -> Candidate | None:
        for candidate in self.revision.candidate_records:
            if candidate.id == identifier:
                return candidate
        return None

    def _visible_task(self, identifier: TaskId) -> TaskRecord | None:
        for task in self.revision.task_records:
            if task.id == identifier:
                return task
        return None

    def _certificate_required(self, checker_id: str) -> bool:
        """Whether the registered checker needs a certificate object.

        A core scope rule declares that the empty certificate is valid; a
        mathematical checker declares a certificate type, so `None` is not
        evidence for it.  The candidate records this declared requirement
        instead of hardcoding a checker name.
        """
        spec = self._runtime.store.checkers.spec(checker_id)
        if spec is None:
            return True
        return spec.certificate_schema.certificate_type is not type(None)

    def _elaborate_result(
        self, shape: ResultShape, result: T.Term
    ) -> Ty.TypedExpr | None:
        """The typed result a schema needs, or None when it needs none.

        Elaboration stays in the workspace: operations own their result schema
        but do not own frames, meanings or signatures.  A failed elaboration is
        passed as None so the schema itself produces the refusal detail.
        """
        if shape not in (ResultShape.PROPOSITION, ResultShape.SET):
            return None
        typing = elaborate.typed(
            result,
            self._runtime.frames,
            self.frame,
            self._runtime.signature,
        )
        return typing if isinstance(typing, Ty.TypedExpr) else None

    def _set_term(
        self, problem: ProblemSpec, result: T.Term
    ) -> bool | None:
        """Whether a SET-language result is structurally a `Set` application.

        The schema owns the shape rule; the workspace owns the signature needed
        to recognise the `Set` head.  A non-SET result language passes `None`.
        """
        if problem.result_language is not ResultLanguage.SET:
            return None
        return set_members(result, self._runtime.signature) is not None

    def _result_language_fit(
        self,
        operation: OperationSpec | None,
        problem: ProblemSpec,
        result: T.Term,
        structured: StructuredResult | None,
    ) -> tuple[ResultLanguageFit, str]:
        """Check one proposed representation against the operation's schema.

        The operation's registered `ResultSchema` owns the shape rule; this
        method only elaborates the result for the shapes that need a typed view
        and projects the outcome onto the candidate applicability vocabulary.
        """
        if operation is None:
            return (
                ResultLanguageFit.DOES_NOT_SATISFY,
                "the candidate's operation is not registered",
            )
        schema = operation.result_schema
        if not schema.accepts(problem.result_language):
            return (
                ResultLanguageFit.DOES_NOT_SATISFY,
                "the operation does not support "
                f"{problem.result_language.value} results",
            )
        typed = self._elaborate_result(schema.shape, result)
        detail = schema.validate(
            result=result,
            structured=structured,
            typed=typed,
            set_term=self._set_term(problem, result),
        )
        if detail is not None:
            return ResultLanguageFit.DOES_NOT_SATISFY, detail
        return ResultLanguageFit.SATISFIES, ""

    # --- operations ---

    def intake(self, term: T.Term, label: str = "") -> Expression:
        """Store an expression object. No judgment is created."""
        expression = self._record_expression(term, label, "Intake")
        event = self._record_event(
            "Intake",
            objects=(expression.version,),
            inputs=(),
            execution_report=None,
        )
        self._append_revision(
            f"intake {label or expression.id}",
            event,
            focus=ObjectFocus(expression.version),
        )
        return expression

    def occurrences(
        self, source: Expression, target: T.Term
    ) -> tuple[Occurrence, ...]:
        """Structural occurrences of `target` in one visible expression.

        This is a read-only query and does not move the focus.  A rewrite fixes
        exactly one occurrence and records it as the new focus.
        """
        issue = self._input_issue(source)
        if issue is not None:
            raise ValueError(issue[1])
        if not isinstance(target, T.Term):
            raise TypeError("an occurrence target must be a term")
        return structural_occurrences(source.term, target)

    def rewrite(
        self,
        source: Expression,
        occurrence: Occurrence,
        replacement: Expression,
        relation: RewriteRelation,
        justification: Pr.Proposition | None = None,
    ) -> RewriteResult:
        """Rewrite one occurrence and record the claimed relation direction.

        The workspace records the relation but does not turn it into a
        judgment.  A user who needs a proved equivalence must submit a separate
        relation to the kernel; a manual rewrite is a presentation action.

        The new revision focuses the replaced occurrence in the result version.
        """
        with self._transaction():
            for expression in (source, replacement):
                issue = self._input_issue(expression)
                if issue is not None:
                    return RewriteResult(
                        OperationStatus.INVALID, detail=issue[1]
                    )
            if not isinstance(occurrence, Occurrence):
                return RewriteResult(
                    OperationStatus.INVALID,
                    detail="a rewrite needs an occurrence",
                )
            current = subterm_at(source.term, occurrence.path)
            if current is None:
                return RewriteResult(
                    OperationStatus.INVALID,
                    detail="the occurrence path is outside the source term",
                )
            if (
                occurrence.expected is not None
                and current != occurrence.expected
            ):
                return RewriteResult(
                    OperationStatus.INVALID,
                    detail=(
                        "the occurrence does not match the expected subterm "
                        "in this source"
                    ),
                )
            if not isinstance(relation, RewriteRelation):
                return RewriteResult(
                    OperationStatus.INVALID,
                    detail="a rewrite needs a relation direction",
                )
            if justification is not None and not self._runtime.frames.readable(
                justification, self.frame
            ):
                return RewriteResult(
                    OperationStatus.INVALID,
                    detail="the justification is outside the current frame",
                )
            try:
                term = replace_at(
                    source.term, occurrence.path, replacement.term
                )
            except IndexError as error:
                return RewriteResult(
                    OperationStatus.INVALID, detail=str(error)
                )
            result = self._record_expression(
                term,
                f"rewrite {source.label or source.id}",
                "Rewrite",
                object_id=source.id,
                presentation=(("rewritten_from", str(source.version)),),
            )
            record = RewriteRecord(
                source.version,
                result.version,
                occurrence,
                relation,
                justification,
            )
            event = self._record_event(
                "Rewrite",
                objects=(result.version,),
                inputs=(source.version, replacement.version),
                execution_report=OperationStatus.APPLIED,
            )
            self._append_revision(
                f"rewrite {source.id}",
                event,
                rewrites=self.revision.rewrites + (record,),
                focus=OccurrenceFocus(result.version, occurrence),
            )
            return RewriteResult(
                OperationStatus.APPLIED,
                source,
                result,
                record,
                "rewritten",
            )

    def substitute(
        self,
        source: Expression,
        symbol: SymbolId,
        replacement: Expression,
    ) -> RewriteResult:
        """Substitute a free symbol everywhere and record the new version.

        A substitution has no single occurrence, so the new revision focuses
        the produced result object rather than an `OccurrenceFocus`.
        """
        with self._transaction():
            for expression in (source, replacement):
                issue = self._input_issue(expression)
                if issue is not None:
                    return RewriteResult(
                        OperationStatus.INVALID, detail=issue[1]
                    )
            if isinstance(symbol, bool) or not isinstance(symbol, int):
                return RewriteResult(
                    OperationStatus.INVALID,
                    detail="a substitution needs a SymbolId",
                )
            term = B.substitute_free(
                source.term, {symbol: replacement.term}
            )
            result = self._record_expression(
                term,
                f"substitute {source.label or source.id}",
                "Substitute",
                object_id=source.id,
                presentation=(("substituted_from", str(source.version)),),
            )
            record = RewriteRecord(
                source.version,
                result.version,
                None,
                RewriteRelation.SUBSTITUTION,
                None,
            )
            event = self._record_event(
                "Substitute",
                objects=(result.version,),
                inputs=(source.version, replacement.version),
                execution_report=OperationStatus.APPLIED,
            )
            self._append_revision(
                f"substitute {source.id}",
                event,
                rewrites=self.revision.rewrites + (record,),
                focus=ObjectFocus(result.version),
            )
            return RewriteResult(
                OperationStatus.APPLIED,
                source,
                result,
                record,
                "substituted",
            )

    def define_function(
        self,
        parameters: tuple[FunctionParameter, ...],
        intrinsic_domain: Pr.Proposition,
        result_sort: Sort,
        representation: T.Term,
        valid_on: Pr.Proposition,
        label: str = "",
    ) -> FunctionDefinitionOutcome:
        """Record a function object inside one workspace transaction."""
        with self._transaction():
            return self._define_function(
                parameters,
                intrinsic_domain,
                result_sort,
                representation,
                valid_on,
                label,
            )

    def _define_function(
        self,
        parameters: tuple[FunctionParameter, ...],
        intrinsic_domain: Pr.Proposition,
        result_sort: Sort,
        representation: T.Term,
        valid_on: Pr.Proposition,
        label: str = "",
    ) -> FunctionDefinitionOutcome:
        """Record an explicit partial function, or refuse without writing.

        The representation must be typed in the current frame and its validity
        region must be provably inside the intrinsic domain.  The function's
        domain is part of the object; a later relation can only use the region
        actually verified for that representation.
        """
        runtime = self._runtime
        consistency = runtime.store.consistency(self.frame)
        if consistency.is_inconsistent():
            return FunctionRefused("the current frame is inconsistent")
        for region in (intrinsic_domain, valid_on):
            if not runtime.frames.readable(region, self.frame):
                return FunctionRefused(
                    "a function region is outside the current frame"
                )
        typing = elaborate.typed(
            representation, runtime.frames, self.frame, runtime.signature
        )
        if not isinstance(typing, Ty.TypedExpr):
            return FunctionRefused(typing.detail)
        if not typing.sort.embeds_into(result_sort):
            return FunctionRefused(
                "the representation sort does not fit the function result sort"
            )
        contained = proved_subregion(
            valid_on, intrinsic_domain, runtime.signature
        )
        if contained is not True:
            return FunctionRefused(
                "the representation validity region is not inside the "
                "intrinsic domain"
            )
        try:
            value = FunctionValue(
                parameters,
                intrinsic_domain,
                result_sort,
                (FunctionRepresentation(representation, valid_on),),
            )
        except (TypeError, ValueError) as error:
            return FunctionRefused(str(error))
        expression = self._record_expression(
            representation,
            label or "function representation",
            "DefineFunction",
        )
        function = FunctionObject(
            ObjectId(self._objects.issue()),
            ObjectVersionId(self._versions.issue()),
            value,
            expression.version,
            0,
            self.frame,
            label,
            "DefineFunction",
        )
        self._functions[function.version] = function
        event = self._record_event(
            "DefineFunction",
            objects=(expression.version,),
            functions=(function.version,),
            execution_report=OperationStatus.APPLIED,
        )
        self._append_revision(f"define {label or function.id}", event)
        return FunctionDefined(function)

    def extend_function(
        self,
        function: FunctionObject,
        representation: Expression,
        domain: Pr.Proposition,
        valid_on: Pr.Proposition,
    ) -> FunctionDefinitionOutcome:
        """Add a representation and enlarge the intrinsic domain explicitly.

        The extension is a registered operation: `EqualOn(old_domain, old, new)`
        must be proved by the independent function-equality checker, and the
        new function value must carry a `CoversCertificate` showing that its
        representation regions cover its declared intrinsic domain.  The
        checker re-verifies that coverage claim.  The enlarged intrinsic domain
        itself is a user declaration, not a proved maximal domain.
        """
        with self._transaction():
            if self._functions.get(function.version) is not function:
                return FunctionRefused(
                    "the function is not an object of this workspace"
                )
            if function.version not in self.revision.functions:
                return FunctionRefused(
                    "the function is not visible in the current revision"
                )
            issue = self._input_issue(representation)
            if issue is not None:
                return FunctionRefused(issue[1])
            for region in (domain, valid_on):
                if not self._runtime.frames.readable(region, self.frame):
                    return FunctionRefused(
                        "a function region is outside the current frame"
                    )
            if not function.value.result_sort.embeds_into(S.REAL):
                return FunctionRefused(
                    "function equality is stated for real-valued functions"
                )
            if (
                proved_subregion(
                    valid_on,
                    domain,
                    self._runtime.signature,
                )
                is not True
            ):
                return FunctionRefused(
                    "the representation validity region is not inside the "
                    "new intrinsic domain"
                )
            if (
                proved_subregion(
                    function.value.intrinsic_domain,
                    domain,
                    self._runtime.signature,
                )
                is not True
            ):
                return FunctionRefused(
                    "the new intrinsic domain does not contain the old domain"
                )
            for existing in function.value.representations:
                if (
                    proved_subregion(
                        existing.valid_on,
                        domain,
                        self._runtime.signature,
                    )
                    is not True
                ):
                    return FunctionRefused(
                        "an existing representation is outside the new "
                        "intrinsic domain"
                    )
            typing = elaborate.typed(
                representation.term,
                self._runtime.frames,
                self.frame,
                self._runtime.signature,
            )
            if not isinstance(typing, Ty.TypedExpr):
                return FunctionRefused(
                    "the new representation cannot be typed"
                )
            if not typing.sort.embeds_into(function.value.result_sort):
                return FunctionRefused(
                    "the new representation sort does not fit the function "
                    "result sort"
                )
            old_expression = self._expressions.get(function.representation)
            if (
                old_expression is None
                or old_expression.version not in self.revision.objects
            ):
                return FunctionRefused(
                    "the current representation is not visible"
                )
            result = self.apply(
                "extend_function",
                (old_expression, representation),
                parameters=(
                    (
                        "extension",
                        FunctionExtensionInput(
                            function.value, domain, valid_on
                        ),
                    ),
                ),
            )
            if result.status not in (
                OperationStatus.VERIFIED,
                OperationStatus.CONDITIONAL,
            ):
                return FunctionRefused(result.detail)
            if result.result is None:
                raise AssertionError(
                    "a verified extension has no result expression"
                )
            if not result.verifications:
                raise AssertionError(
                    "a verified extension has no verification link"
                )
            specification = result.verifications[0].specification
            value = function.value.extended(
                domain, representation.term, valid_on
            )
            extended = FunctionObject(
                function.id,
                ObjectVersionId(self._versions.issue()),
                value,
                result.result.version,
                len(value.representations) - 1,
                self.frame,
                function.label,
                "ExtendFunction",
            )
            self._functions[extended.version] = extended
            relation = ConstructionRelation(
                function.version,
                extended.version,
                "function_extension",
                specification,
                self.frame,
            )
            event = self._record_event(
                "ExtendFunction",
                objects=(result.result.version,),
                functions=(extended.version,),
                inputs=(function.version, representation.version),
                execution_report=result.status,
            )
            self._append_revision(
                f"extend {function.label or function.id}",
                event,
                construction_relations=(
                    self.revision.construction_relations + (relation,)
                ),
            )
            return FunctionDefined(extended)

    def compare_functions(
        self,
        left: FunctionObject,
        right: FunctionObject,
        region: Pr.Proposition | None = None,
    ) -> OperationResult:
        """Prove `EqualOn(region, ...)` or `SamePartialFunction(...)`.

        With a region the result is a verified equality on that region; without
        one it is full partial-function equality.  The operation and the
        independent checker decide the fragment; this method only assembles the
        request from the visible function versions.
        """
        with self._transaction():
            for function in (left, right):
                if self._functions.get(function.version) is not function:
                    return self._failure(
                        "compare_functions",
                        OperationStatus.INVALID,
                        "a function is not an object of this workspace",
                    )
                if function.version not in self.revision.functions:
                    return self._failure(
                        "compare_functions",
                        OperationStatus.INVALID,
                        "a function is not visible in the current revision",
                    )
            left_expression = self._expressions.get(left.representation)
            right_expression = self._expressions.get(right.representation)
            if (
                left_expression is None
                or right_expression is None
                or left_expression.version not in self.revision.objects
                or right_expression.version not in self.revision.objects
            ):
                return self._failure(
                    "compare_functions",
                    OperationStatus.INVALID,
                    "a function representation is not visible",
                )
            return self.apply(
                "compare_functions",
                (left_expression, right_expression),
                region=region,
                parameters=(
                    (
                        "comparison",
                        FunctionComparisonInput(
                            left.value,
                            right.value,
                            left.representation_index,
                            right.representation_index,
                        ),
                    ),
                ),
            )

    def apply_function(
        self,
        function: FunctionObject,
        arguments: tuple[T.Term, ...],
    ) -> FunctionApplicationResult:
        """Apply one visible function value to neutral argument terms.

        This records expressions and their substituted representation regions.
        It creates no judgment: the arguments may still violate the intrinsic
        domain, and the caller must check the returned condition terms before
        treating the application as defined.
        """
        with self._transaction():
            if self._functions.get(function.version) is not function:
                return FunctionApplicationResult(
                    OperationStatus.INVALID,
                    detail="the function is not an object of this workspace",
                )
            if function.version not in self.revision.functions:
                return FunctionApplicationResult(
                    OperationStatus.INVALID,
                    detail="the function is not visible in the current revision",
                )
            try:
                applications = function.value.applications(arguments)
            except (TypeError, ValueError) as error:
                return FunctionApplicationResult(
                    OperationStatus.INVALID, detail=str(error)
                )
            expressions: list[Expression] = []
            conditions: list[T.Term] = []
            for application in applications:
                typing = elaborate.typed(
                    application.term,
                    self._runtime.frames,
                    self.frame,
                    self._runtime.signature,
                )
                if not isinstance(typing, Ty.TypedExpr):
                    return FunctionApplicationResult(
                        OperationStatus.INVALID,
                        detail="an applied representation cannot be typed",
                    )
                expression = self._record_expression(
                    application.term,
                    f"apply {function.label or function.id}",
                    "ApplyFunction",
                )
                expressions.append(expression)
                conditions.append(application.valid_on)
            event = self._record_event(
                "ApplyFunction",
                objects=tuple(
                    expression.version for expression in expressions
                ),
                functions=(function.version,),
                inputs=(function.version,),
                execution_report=OperationStatus.APPLIED,
            )
            self._append_revision(
                f"apply {function.label or function.id}", event
            )
            return FunctionApplicationResult(
                OperationStatus.APPLIED,
                tuple(expressions),
                tuple(conditions),
                "applied; the returned conditions are obligations",
            )

    def differentiate_function(
        self,
        function: FunctionObject,
        variable: SymbolId,
    ) -> OperationResult:
        """Differentiate the representation on its actual validity region.

        The intrinsic domain is not rewritten and the result is not silently
        promoted to a function value.  The neutral result expression and its
        verified relation are separate from the function object.
        """
        if self._functions.get(function.version) is not function:
            return self._failure(
                "differentiate",
                OperationStatus.INVALID,
                "a function is not an object of this workspace",
            )
        if function.version not in self.revision.functions:
            return self._failure(
                "differentiate",
                OperationStatus.INVALID,
                "a function is not visible in the current revision",
            )
        representation = self._expressions.get(function.representation)
        if (
            representation is None
            or representation.version not in self.revision.objects
        ):
            return self._failure(
                "differentiate",
                OperationStatus.INVALID,
                "the function representation is not visible",
            )
        entry = function.value.representations[function.representation_index]
        if representation.term != entry.term:
            return self._failure(
                "differentiate",
                OperationStatus.INVALID,
                "the function representation changed",
            )
        result = self.apply(
            "differentiate",
            (representation,),
            target=variable,
            region=entry.valid_on,
        )
        return replace(
            result, trace=result.trace + (f"function:{function.id}",)
        )

    def assume(self, term: T.Term) -> AssumptionResult:
        """Introduce one hypothesis inside one workspace transaction."""
        with self._transaction():
            return self._assume(term)

    def _assume(self, term: T.Term) -> AssumptionResult:
        """Introduce one hypothesis in a child frame and issue `H |- H`."""
        runtime = self._runtime
        current = runtime.store.consistency(self.frame)
        if current.is_inconsistent():
            return AssumptionResult(
                OperationStatus.INVALID,
                self.frame,
                None,
                None,
                "the current frame is inconsistent",
                current,
            )
        issued = elaborate.proposition(
            term,
            runtime.frames,
            self.frame,
            runtime.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return AssumptionResult(
                OperationStatus.INVALID,
                self.frame,
                None,
                None,
                "the hypothesis is not a proposition",
            )
        if issued in runtime.frames.assumptions(self.frame):
            return AssumptionResult(
                OperationStatus.INVALID,
                self.frame,
                issued,
                None,
                "the proposition is already an assumption",
            )
        child = runtime.frames.create(
            self.frame, hypotheses=(Hypothesis(issued),)
        )
        outcome = self._commit(
            CommitProposal(
                child.id,
                (issued,),
                HypothesisChecker.id,
                "assume",
                "Hypothesis",
                certificate=None,
            ),
        )
        if not isinstance(outcome, Committed):
            runtime.frames.discard(child.id)
            detail = (
                outcome.detail
                if isinstance(outcome, (Rejected, Deferred))
                else "the hypothesis could not be issued"
            )
            status = (
                OperationStatus.UNSUPPORTED
                if isinstance(outcome, Deferred)
                else OperationStatus.INVALID
            )
            return AssumptionResult(
                status, self.frame, issued, None, detail
            )
        judgment = outcome.judgments[0]
        consistency = assess_consistency(runtime.store, child.id)
        inconsistent = consistency.is_inconsistent()
        witness = (
            (consistency.witness,)
            if isinstance(consistency, Inconsistent)
            else ()
        )
        status = (
            OperationStatus.INVALID
            if inconsistent
            else OperationStatus.VERIFIED
        )
        event = self._record_event(
            "Assume",
            judgments=(judgment,) + witness,
            execution_report=status,
        )
        self._append_revision(
            f"assume {issued.term}", event, frame=child.id
        )
        return AssumptionResult(
            status,
            child.id,
            issued,
            judgment,
            (
                "the assumptions prove a contradiction"
                if inconsistent
                else ""
            ),
            consistency,
        )

    def declare(self, name: str, sort: Sort) -> DeclarationResult:
        """Declare one symbol inside one checked context extension."""
        with self._transaction():
            return self._declare(name, sort)

    def _declare(self, name: str, sort: Sort) -> DeclarationResult:
        """Declare one symbol in a child frame, or refuse without writing.

        The frame store owns freshness, language-head and escape checks; this
        method only fixes the identity of the name and records the extension.
        A declaration is not a proposition, so no kernel judgment is issued.
        """
        if not isinstance(name, str) or _IDENTIFIER.fullmatch(name) is None:
            return DeclarationResult(
                OperationStatus.INVALID,
                self.frame,
                None,
                "a declaration name must be an identifier",
            )
        if not isinstance(sort, Sort):
            return DeclarationResult(
                OperationStatus.INVALID,
                self.frame,
                None,
                "a declaration needs a sort",
            )
        runtime = self._runtime
        symbol = runtime.table.intern(name)
        declaration = Declaration(symbol, name, sort)
        try:
            child = runtime.frames.create(
                self.frame, declarations=(declaration,)
            )
        except ValueError as error:
            return DeclarationResult(
                OperationStatus.INVALID, self.frame, None, str(error)
            )
        event = self._record_event(
            "Declare", execution_report=OperationStatus.VERIFIED
        )
        self._append_revision(f"declare {name}", event, frame=child.id)
        return DeclarationResult(
            OperationStatus.VERIFIED, child.id, declaration
        )

    def define(self, name: str, body: T.Term) -> DefinitionResult:
        """Define one alias inside one checked context extension."""
        with self._transaction():
            return self._define(name, body)

    def _define(self, name: str, body: T.Term) -> DefinitionResult:
        """Define one alias in a child frame, or refuse without writing.

        The body is elaborated in the current frame before the frame store
        checks freshness, scoping and alias acyclicity.  A definition is a
        context extension, not an equation, so no kernel judgment is issued.
        """
        if not isinstance(name, str) or _IDENTIFIER.fullmatch(name) is None:
            return DefinitionResult(
                OperationStatus.INVALID,
                self.frame,
                None,
                "a definition name must be an identifier",
            )
        if not isinstance(body, T.Term):
            return DefinitionResult(
                OperationStatus.INVALID,
                self.frame,
                None,
                "a definition body must be a term",
            )
        runtime = self._runtime
        typing = elaborate.typed(
            body, runtime.frames, self.frame, runtime.signature
        )
        if not isinstance(typing, Ty.TypedExpr):
            return DefinitionResult(
                OperationStatus.INVALID, self.frame, None, typing.detail
            )
        symbol = runtime.table.intern(name)
        definition = Definition(symbol, name, body)
        try:
            child = runtime.frames.create(
                self.frame, definitions=(definition,)
            )
        except ValueError as error:
            return DefinitionResult(
                OperationStatus.INVALID, self.frame, None, str(error)
            )
        event = self._record_event(
            "Define", execution_report=OperationStatus.VERIFIED
        )
        self._append_revision(f"define {name}", event, frame=child.id)
        return DefinitionResult(
            OperationStatus.VERIFIED, child.id, definition
        )

    def apply(
        self,
        operation_id: str,
        inputs: tuple[Expression, ...],
        *,
        target: SymbolId | None = None,
        region: Pr.Proposition | None = None,
        coverage: Coverage = Coverage.ONE_VERIFIED,
        result_language: ResultLanguage | None = None,
        parameter_mode: ParameterMode | None = None,
        externalizable: tuple[Pr.Proposition, ...] = (),
        parameters: tuple[tuple[str, object], ...] = (),
        policy: ConditionPolicy = ConditionPolicy.REQUIRE_PROVED,
        budget: ExecutionBudget = ExecutionBudget(),
    ) -> OperationResult:
        """Apply one registered operation inside one workspace transaction.

        `externalizable` is the request's explicit set of premises the answer
        may leave outside the result.  It is fixed into the problem before the
        proposal and commit, so a task can become `COMPLETED_CONDITIONAL` only
        when every open condition is one of these premises.
        """
        with self._transaction():
            return self._apply(
                operation_id,
                inputs,
                target=target,
                region=region,
                coverage=coverage,
                result_language=result_language,
                parameter_mode=parameter_mode,
                externalizable=externalizable,
                parameters=parameters,
                policy=policy,
                budget=budget,
            )

    def _apply(
        self,
        operation_id: str,
        inputs: tuple[Expression, ...],
        *,
        target: SymbolId | None = None,
        region: Pr.Proposition | None = None,
        coverage: Coverage = Coverage.ONE_VERIFIED,
        result_language: ResultLanguage | None = None,
        parameter_mode: ParameterMode | None = None,
        externalizable: tuple[Pr.Proposition, ...] = (),
        parameters: tuple[tuple[str, object], ...] = (),
        policy: ConditionPolicy = ConditionPolicy.REQUIRE_PROVED,
        budget: ExecutionBudget = ExecutionBudget(),
    ) -> OperationResult:
        """Apply one registered operation to fixed current object versions.

        The explicit `externalizable` set replaces the operation-built set on
        the fixed problem.  The replaced problem is the single problem carried
        by the execution request, candidate, commit and task; it is never a
        second `ProblemSpec`.
        """
        runtime = self._runtime
        consistency = runtime.store.consistency(self.frame)
        if consistency.is_inconsistent():
            return self._failure(
                operation_id,
                OperationStatus.INVALID,
                "the current frame is inconsistent",
            )
        if not inputs:
            return self._failure(
                operation_id,
                OperationStatus.INVALID,
                "an operation needs at least one input",
            )
        for expression in inputs:
            issue = self._input_issue(expression)
            if issue is not None:
                return self._failure(
                    operation_id, *issue, budget=budget
                )

        operation = runtime.operations.get(operation_id)
        if operation is None:
            return self._failure(
                operation_id,
                OperationStatus.UNSUPPORTED,
                f"operation not registered: {operation_id}",
                budget=budget,
            )
        if region is not None and not runtime.frames.readable(
            region, self.frame
        ):
            return self._failure(
                operation_id,
                OperationStatus.INVALID,
                "the requested region is outside the current frame",
            )
        for premise in externalizable:
            if not runtime.frames.readable(premise, self.frame):
                return self._failure(
                    operation_id,
                    OperationStatus.INVALID,
                    "an externalizable premise is outside the current frame",
                )
        for _, value in parameters:
            if not isinstance(value, GenericResultInput):
                continue
            family = value.result
            for proposition in (
                family.valid_on.condition,
                family.correctness_specification,
                *(case.condition for case in family.excluded_cases),
            ):
                if not runtime.frames.readable(proposition, self.frame):
                    return self._failure(
                        operation_id,
                        OperationStatus.INVALID,
                        "a generic result is outside the current frame",
                    )
            if not any(
                self._generic_family_visible(family, expression)
                for expression in inputs
            ):
                return self._failure(
                    operation_id,
                    OperationStatus.INVALID,
                    "a generic result is not visible for the inputs",
                )
        input_versions = tuple(expression.version for expression in inputs)
        request = OperationRequest(
            self.frame,
            tuple(expression.term for expression in inputs),
            target,
            region,
            coverage,
            result_language,
            parameter_mode,
            tuple(parameters),
        )
        problem_outcome = operation.build_problem(request)
        if isinstance(problem_outcome, ProblemUnsupported):
            blocker = Blocker(
                problem_outcome.reason,
                problem_outcome.detail,
                missing=problem_outcome.missing,
                conditions=problem_outcome.conditions,
                attempted=problem_outcome.attempted,
                target=(
                    None
                    if problem_outcome.problem is None
                    else problem_outcome.problem.region
                ),
                budget=budget,
            )
            if problem_outcome.problem is not None:
                fixed_problem = replace(
                    problem_outcome.problem,
                    externalizable=externalizable,
                )
                return self._record_blocked_task(
                    operation_id,
                    blocked_problem(request, fixed_problem),
                    problem_outcome.detail,
                    self._status_for(problem_outcome.reason),
                    inputs=input_versions,
                    parameters=request.parameters,
                    blocker=blocker,
                    target=fixed_problem.region,
                    budget=budget,
                )
            return self._failure(
                operation_id,
                self._status_for(problem_outcome.reason),
                problem_outcome.detail,
                blocker=blocker,
            )
        if isinstance(problem_outcome, ProblemInvalid):
            return self._failure(
                operation_id,
                OperationStatus.INVALID,
                problem_outcome.detail,
            )
        if not isinstance(problem_outcome, ProblemBuilt):
            raise TypeError(
                "an operation returned an unknown problem outcome"
            )
        problem = replace(
            problem_outcome.problem, externalizable=externalizable
        )
        execution = ExecutionRequest(
            request,
            problem,
            problem_outcome.algebra,
            request.frame,
            policy,
            budget,
        )
        structure_issue = self._problem_structure_issue(request, problem)
        if structure_issue is not None:
            return self._failure(
                operation_id,
                OperationStatus.INVALID,
                structure_issue,
            )
        dimension_issue = self._problem_dimension_issue(request, problem)
        if dimension_issue is not None:
            return self._record_blocked_task(
                operation_id,
                problem,
                dimension_issue,
                OperationStatus.UNSUPPORTED,
                inputs=input_versions,
                parameters=request.parameters,
                blocker=Blocker(
                    Reason.FRAGMENT,
                    dimension_issue,
                    target=problem.region,
                    budget=budget,
                ),
                target=problem.region,
                budget=budget,
            )
        if not operation.result_schema.accepts(problem.result_language):
            detail = (
                "the operation does not support "
                f"{problem.result_language.value} results"
            )
            return self._record_blocked_task(
                operation_id,
                problem,
                detail,
                inputs=input_versions,
                parameters=request.parameters,
                blocker=Blocker(
                    Reason.FRAGMENT,
                    detail,
                    missing=frozenset(
                        {
                            "result_language:"
                            f"{problem.result_language.value}"
                        }
                    ),
                    target=problem.region,
                    budget=budget,
                ),
                target=problem.region,
                budget=budget,
            )

        proposal_outcome = operation.propose(execution)
        if isinstance(proposal_outcome, ProposalUnsupported):
            blocker = Blocker(
                proposal_outcome.reason,
                proposal_outcome.detail,
                missing=proposal_outcome.missing,
                conditions=proposal_outcome.conditions,
                attempted=proposal_outcome.attempted,
                target=problem.region,
                budget=budget,
            )
            return self._record_blocked_task(
                operation_id,
                problem,
                proposal_outcome.detail,
                self._status_for(proposal_outcome.reason),
                inputs=input_versions,
                parameters=request.parameters,
                blocker=blocker,
                target=problem.region,
                budget=budget,
            )
        if isinstance(proposal_outcome, ProposalInvalid):
            return self._record_blocked_task(
                operation_id,
                problem,
                proposal_outcome.detail,
                OperationStatus.INVALID,
                inputs=input_versions,
                parameters=request.parameters,
                blocker=Blocker(
                    Reason.FRAGMENT,
                    proposal_outcome.detail,
                    target=problem.region,
                    budget=budget,
                ),
                target=problem.region,
                budget=budget,
            )
        if not isinstance(proposal_outcome, Proposed):
            raise TypeError(
                "an operation returned an unknown proposal outcome"
            )
        proposal = proposal_outcome.proposal
        if proposal.answer_coverage is not problem.coverage:
            return self._record_blocked_task(
                operation_id,
                problem,
                "the proposal does not meet the requested coverage",
                OperationStatus.INVALID,
                inputs=input_versions,
                parameters=request.parameters,
                target=problem.region,
                budget=budget,
            )
        if problem.result_language is ResultLanguage.SET:
            if problem.coverage not in (
                Coverage.SOUND_SET,
                Coverage.COMPLETE_SET,
            ):
                return self._record_blocked_task(
                    operation_id,
                    problem,
                    "a set result needs sound or complete coverage",
                    OperationStatus.INVALID,
                    inputs=input_versions,
                    parameters=request.parameters,
                    target=problem.region,
                    budget=budget,
                )
        else:
            # Only SET results have implemented answer-set coverage.  An
            # expression, proposition or decomposition result is one verified
            # answer; a sound/complete request cannot be met by this result
            # language, and the operation must not quietly downgrade it.
            if (
                problem.coverage is not Coverage.ONE_VERIFIED
                or request.coverage is not Coverage.ONE_VERIFIED
            ):
                return self._record_blocked_task(
                    operation_id,
                    problem,
                    "only one-verified coverage is implemented for this "
                    "result language",
                    inputs=input_versions,
                    parameters=request.parameters,
                    target=problem.region,
                    budget=budget,
                )
        typed_result = self._elaborate_result(
            operation.result_schema.shape, proposal.result
        )
        shape_detail = operation.result_schema.validate(
            result=proposal.result,
            structured=proposal.structured,
            typed=typed_result,
            set_term=self._set_term(problem, proposal.result),
        )
        if shape_detail is not None:
            return self._record_blocked_task(
                operation_id,
                problem,
                shape_detail,
                OperationStatus.INVALID,
                inputs=input_versions,
                parameters=request.parameters,
                target=problem.region,
                budget=budget,
            )
        language_fit = ResultLanguageFit.SATISFIES
        if (
            problem.result_language is ResultLanguage.SET
            and problem.coverage != request.coverage
        ):
            return self._record_blocked_task(
                operation_id,
                problem,
                "the problem does not describe the requested coverage",
                OperationStatus.INVALID,
                inputs=input_versions,
                parameters=request.parameters,
                target=problem.region,
                budget=budget,
            )
        for region in (
            proposal.result_region,
            proposal.valid_on,
            *proposal.excluded_cases,
        ):
            if region is not None and not runtime.frames.readable(
                region, self.frame
            ):
                return self._failure(
                    operation_id,
                    OperationStatus.INVALID,
                    "the proposal states a region outside the current frame",
                )
        binding = next(
            (
                item
                for item in operation.checker_bindings
                if item.specification_kind == proposal.specification_kind
                and (item.target is None or item.target == request.target)
            ),
            None,
        )
        if binding is None:
            return self._record_blocked_task(
                operation_id,
                problem,
                "the operation has no checker for the proposed specification",
                OperationStatus.INVALID,
                inputs=input_versions,
                parameters=request.parameters,
                target=problem.region,
                budget=budget,
            )
        if problem.operation != binding.problem_kind:
            return self._record_blocked_task(
                operation_id,
                problem,
                "the problem kind does not match the checker binding",
                OperationStatus.INVALID,
                inputs=input_versions,
                parameters=request.parameters,
                target=problem.region,
                budget=budget,
            )

        # The candidate is relative to the original request.  The achieved
        # region belongs to the verification link and the operation result,
        # never to a rewritten copy of the problem.
        task_id = TaskId(self._task_ids.issue())
        candidate = Candidate(
            CandidateId(self._candidate_ids.issue()),
            task_id,
            problem,
            proposal.result,
            self.frame,
            CandidateState.UNCHECKED,
            proposal.specifications,
            proposal.certificate,
            binding.checker_id,
            proposal.specification_kind,
            proposal.result_region,
            applicability=CandidateApplicability.APPLICABLE,
            coverage=CandidateCoverage.UNCLAIMED,
            language_fit=language_fit,
            candidate_role=binding.candidate_role,
            certificate_required=self._certificate_required(
                binding.checker_id
            ),
            structured=(
                None
                if proposal.structured is None
                else proposal.structured.components
            ),
            algebra=execution.algebra,
        )
        self._candidates[candidate.id] = candidate

        committed = self._commit(
            CommitProposal(
                execution.frame,
                proposal.specifications,
                binding.checker_id,
                binding.problem_kind,
                proposal.specification_kind,
                certificate=proposal.certificate,
                problem=problem,
                policy=execution.policy,
                budget=execution.budget,
                candidate=proposal.result,
                candidate_role=binding.candidate_role,
                structured=(
                    None
                    if proposal.structured is None
                    else proposal.structured.components
                ),
                algebra=execution.algebra,
            ),
        )
        judgments: tuple[JudgmentId, ...] = ()
        commit_blocker: Blocker | None = None
        open_obligations: tuple[Pr.Proposition, ...] = ()
        if isinstance(committed, Committed):
            open_obligations = self._open_obligations(committed)
            status = (
                OperationStatus.CONDITIONAL
                if proposal.result_region is not None or open_obligations
                else OperationStatus.VERIFIED
            )
            judgments = committed.judgments
            detail = ""
            candidate_state = CandidateState.VERIFIED
            applicability = (
                CandidateApplicability.CONDITIONAL
                if status is OperationStatus.CONDITIONAL
                else CandidateApplicability.APPLICABLE
            )
        elif isinstance(committed, Rejected):
            status, candidate_state, applicability, commit_blocker = (
                self._rejected_projection(
                    committed,
                    target=proposal.specifications[0],
                    budget=execution.budget,
                    attempted=(binding.checker_id,),
                )
            )
            detail = committed.detail
        elif isinstance(committed, Deferred):
            status = self._status_for(committed.reason)
            detail = committed.detail
            commit_blocker = Blocker(
                committed.reason,
                committed.detail,
                missing=committed.missing,
                conditions=committed.conditions,
                target=proposal.specifications[0],
                budget=execution.budget,
            )
            candidate_state = CandidateState.UNVERIFIED
            applicability = CandidateApplicability.BLOCKED
        else:
            raise TypeError("commit returned an unknown result")

        if status not in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ):
            candidate_coverage = CandidateCoverage.UNCLAIMED
        elif proposal.coverage is not None:
            candidate_coverage = {
                CoverageClaim.SPECIFIED: CandidateCoverage.COMPLETE,
                CoverageClaim.GENERIC: CandidateCoverage.GENERIC,
                CoverageClaim.PARTIAL: CandidateCoverage.PARTIAL,
                CoverageClaim.ALL_VALUES: CandidateCoverage.COMPLETE,
            }[proposal.coverage]
        elif problem.coverage is Coverage.COMPLETE_SET:
            candidate_coverage = CandidateCoverage.COMPLETE
        elif problem.coverage is Coverage.SOUND_SET:
            candidate_coverage = CandidateCoverage.PARTIAL
        else:
            candidate_coverage = CandidateCoverage.COMPLETE
        candidate = candidate.checked(
            candidate_state,
            applicability=applicability,
            coverage=candidate_coverage,
            language_fit=language_fit,
        )
        self._candidates[candidate.id] = candidate

        result: Expression | None = None
        generic: GenericResult | None = None
        if status in (OperationStatus.VERIFIED, OperationStatus.CONDITIONAL):
            result = self._record_expression(
                proposal.result,
                f"{operation_id} {inputs[0].label or inputs[0].id}",
                operation_id,
            )
            if proposal.coverage is not None:
                if proposal.valid_on is None:
                    raise AssertionError(
                        "a coverage claim without a validity region"
                    )
                generic = GenericResult(
                    result=proposal.result,
                    valid_on=region_from_proposition(proposal.valid_on),
                    excluded_cases=tuple(
                        region_from_proposition(case)
                        for case in proposal.excluded_cases
                    ),
                    correctness_specification=proposal.specifications[0],
                    coverage_claim=proposal.coverage,
                )

        link_status = (
            OperationStatus.VERIFIED
            if status in (
                OperationStatus.VERIFIED,
                OperationStatus.CONDITIONAL,
            )
            else status
        )
        links = tuple(
            VerificationLink(
                candidate=candidate.id,
                specification=specification,
                judgment=(
                    judgments[index] if index < len(judgments) else None
                ),
                status=link_status,
                specification_kind=proposal.specification_kind,
                frame=candidate.frame,
                coverage=problem.coverage,
                condition=proposal.result_region,
                obligations=open_obligations,
            )
            for index, specification in enumerate(proposal.specifications)
        )
        attempt_state = (
            ExecutionState.FINISHED
            if status
            in (OperationStatus.VERIFIED, OperationStatus.CONDITIONAL)
            else ExecutionState.BLOCKED
        )
        attempt = self._record_attempt(
            task_id, attempt_state, status, detail, blocker=commit_blocker
        )
        event = self._record_event(
            operation_id,
            objects=() if result is None else (result.version,),
            tasks=(task_id,),
            attempts=(attempt.id,),
            candidates=(candidate.id,),
            judgments=judgments,
            inputs=tuple(expression.version for expression in inputs),
            parameters=request.parameters,
            execution_report=status,
        )
        task = TaskRecord(
            task_id,
            problem,
            self.frame,
            derive_task_state(
                problem,
                (candidate,),
                links,
                commit_blocker,
                (attempt,),
            ),
            (candidate.id,),
            detail,
            TaskOrigin.EXECUTION,
            None,
            (),
            tuple(expression.version for expression in inputs),
            (attempt.id,),
            blocker=commit_blocker,
        )
        self._tasks[task.id] = task
        generic_results = self.revision.generic_results
        if generic is not None:
            # A source can carry several families with different orientations
            # (for example a derivative family and an antiderivative family).
            # Recording a new family must not erase an earlier one; selection
            # belongs to the consumer that knows which relation it needs.
            generic_results = generic_results + (
                (inputs[0].version, generic),
            )
        structured_results = self.revision.structured_results
        if proposal.structured is not None and result is not None:
            structured_results = tuple(
                (version, structured)
                for version, structured in structured_results
                if version != result.version
            ) + ((result.version, proposal.structured),)
        self._append_revision(
            f"{operation_id} {inputs[0].id}",
            event,
            links,
            generic_results=generic_results,
            structured_results=structured_results,
            focus=(
                _KEEP_FOCUS
                if result is None
                else ObjectFocus(result.version)
            ),
        )
        return OperationResult(
            operation_id,
            status,
            candidate,
            links,
            result,
            detail,
            proposal.result_region,
            generic,
            proposal.trace,
            task,
            proposal.structured,
            commit_blocker,
        )

    def differentiate(
        self,
        source: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Client helper: assemble and apply one derivative request."""
        return self.apply("differentiate", (source,), target=variable)

    def integrate(
        self,
        source: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Client helper: assemble and apply one polynomial antiderivative request."""
        return self.apply("integrate", (source,), target=variable)

    def hermite_reduce(
        self,
        source: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Client helper: assemble one rational Hermite-reduction request."""
        return self.apply("hermite_reduce", (source,), target=variable)

    def solve_linear(
        self,
        source: Expression,
        variable: SymbolId,
        coverage: Coverage = Coverage.COMPLETE_SET,
    ) -> OperationResult:
        """Client helper: solve one linear polynomial as a finite set."""
        return self.apply(
            "solve_linear",
            (source,),
            target=variable,
            coverage=coverage,
        )

    def gcd(
        self,
        left: Expression,
        right: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Client helper: compute the monic polynomial gcd."""
        return self.apply(
            "polynomial_gcd", (left, right), target=variable
        )

    def resultant(
        self,
        left: Expression,
        right: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Client helper: compute the univariate resultant."""
        return self.apply("resultant", (left, right), target=variable)

    def root_count(
        self,
        source: Expression,
        lower: Expression,
        upper: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Client helper: count distinct real roots in an open interval."""
        return self.apply(
            "root_count", (source, lower, upper), target=variable
        )

    def isolate_roots(
        self,
        source: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Client helper: isolate every distinct real root as open intervals."""
        return self.apply(
            "isolate_roots",
            (source,),
            target=variable,
            coverage=Coverage.COMPLETE_SET,
        )

    def structured_result(
        self, source: Expression
    ) -> StructuredResult | None:
        """The structured decomposition visible for one result expression."""
        if self._expressions.get(source.version) is not source:
            return None
        if source.version not in self.revision.objects:
            return None
        for version, structured in self.revision.structured_results:
            if version == source.version:
                return structured
        return None

    def generic_results(self, source: Expression) -> tuple[GenericResult, ...]:
        """All verified parameter families visible for `source`, oldest first.

        The source must be this workspace's exact handle and visible in the
        revision.  Several families can belong to one source version (for
        example a derivative family and an antiderivative family); the revision
        snapshot preserves their recording order.
        """
        if self._expressions.get(source.version) is not source:
            return ()
        if source.version not in self.revision.objects:
            return ()
        return tuple(
            family
            for version, family in self.revision.generic_results
            if version == source.version
        )

    def generic_result(self, source: Expression) -> GenericResult | None:
        """The latest verified parameter family visible for `source`.

        The family is part of the revision snapshot, so undo hides a family
        recorded later and redo restores it.  The source must also be this
        workspace's exact handle, not merely a matching version id.  This
        reader returns the latest recorded family regardless of orientation;
        consumers that need a particular relation use `derivative_family` or a
        relation-specific selector of their own.
        """
        families = self.generic_results(source)
        return families[-1] if families else None

    def derivative_family(self, source: Expression) -> GenericResult | None:
        """The latest family whose result is the derivative of `source`.

        Orientation is read from the family's correctness specification: it
        must be this runtime's `HasDerivative` claim with
        `claim.source == source.term`, `claim.candidate == family.result` and
        `claim.variable.symbol_id == self._runtime.variable`.  The variable
        check keeps specialization on its declared target: a family derived
        from the same source with respect to a formal parameter is a different
        relation and is not selected.  An antiderivative family records the
        opposite orientation and is not selected.  The workflow uses the
        vocabulary object assembled by the runtime; it does not import the
        derivative module or hardcode the predicate name and argument
        positions.
        """
        selected: GenericResult | None = None
        for family in self.generic_results(source):
            claim = self._runtime.vocabulary.parse_claim(
                family.correctness_specification.term
            )
            if claim is None:
                continue
            if claim.source != source.term:
                continue
            if claim.candidate != family.result:
                continue
            if claim.variable.symbol_id != self._runtime.variable:
                continue
            selected = family
        return selected

    def _generic_family_visible(
        self, family: GenericResult, source: Expression
    ) -> bool:
        """Whether `family` is recorded for `source` in this revision."""
        return any(
            version == source.version and recorded == family
            for version, recorded in self.revision.generic_results
        )

    def specialize(
        self,
        source: Expression,
        values: Mapping[SymbolId, Fraction],
    ) -> OperationResult:
        """Client helper: resolve a visible derivative family and specialize it.

        This method only assembles the operation's declared parameters; the
        semantics of specialisation live in the registered operation.  The
        family is taken from the current revision, never from a caller-supplied
        snapshot, so undo/redo and future associations cannot be bypassed.

        Current scope: only a family whose correctness specification states
        that its result is the derivative of `source` is selected.  An
        antiderivative family (or any other relation) is refused with a
        structured fragment gap rather than being handed to the derivative
        checker, which would report a spurious mathematical refutation.
        General integral-family specialisation is not implemented.
        """
        if not self._runtime.request.parameters:
            return self._failure(
                "specialize",
                OperationStatus.UNSUPPORTED,
                "this runtime has no formal parameters",
            )
        issue = self._input_issue(source)
        if issue is not None:
            return self._failure("specialize", *issue)
        family = self.derivative_family(source)
        if family is None:
            if self.generic_results(source):
                detail = (
                    "specialization currently supports derivative families; "
                    "the visible family states another relation"
                )
                return self._failure(
                    "specialize",
                    OperationStatus.UNSUPPORTED,
                    detail,
                    blocker=Blocker(
                        Reason.FRAGMENT,
                        detail,
                        missing=frozenset({"derivative_family"}),
                    ),
                )
            detail = (
                "specialization currently supports derivative families; "
                "differentiate the source first so a verified derivative "
                "family exists"
            )
            return self._failure(
                "specialize",
                OperationStatus.UNSUPPORTED,
                detail,
                blocker=Blocker(
                    Reason.FRAGMENT,
                    detail,
                    missing=frozenset({"derivative_family"}),
                ),
            )
        try:
            mapping = ValueMappingInput(values)
        except (TypeError, ValueError) as error:
            return self._failure(
                "specialize",
                OperationStatus.INVALID,
                f"invalid specialization: {error}",
            )
        return self.apply(
            "specialize",
            (source,),
            target=self._runtime.variable,
            parameters=(
                ("family", GenericResultInput(family)),
                ("values", mapping),
            ),
        )

    # --- history ---

    def undo(self) -> bool:
        """Move to the first parent of the current revision."""
        current = self.revision
        if not current.parents:
            return False
        self._head = current.parents[0]
        return True

    def redo(self) -> bool:
        """Move to the most recently created child of the current revision."""
        children = self._children.get(self._head, ())
        if not children:
            return False
        self._head = children[-1]
        return True

    def branch(self, label: str = "branch") -> Revision:
        """Create a checkpoint child of the current revision.

        The new revision has the same visible snapshot as its parent.  Actions
        performed on it become children of this branch; the old branch remains
        in the revision DAG and can be selected again with `switch_to`.  The
        branch inherits the parent's focus.
        """
        event = self._record_event("Branch")
        return self._append_revision(label, event)

    def switch_to(self, revision: RevisionId) -> None:
        """Select any revision in the DAG as the current view."""
        if revision not in self._revisions:
            raise KeyError(f"unknown revision: {revision}")
        self._head = revision

    def merge(self, other: RevisionId, label: str = "merge") -> Revision:
        """Merge another revision's visible records into a new revision.

        This is a history-view merge, not a mathematical branch merge.  Objects
        from another frame keep their original frame and become visible in the
        merged revision, but they are not automatically usable in the current
        frame.  Generic families from both sides are preserved (identical
        recordings are deduplicated), because one source can carry several
        relations; conflicting structured results for the same object version
        are still refused.  The merged revision keeps the target revision's
        focus; the other revision's focus is not invented as a new pointer.
        """
        if other not in self._revisions:
            raise KeyError(f"unknown revision: {other}")
        current = self.revision
        other_revision = self._revisions[other]
        merged_generic = self._merge_generic_results(
            current.generic_results, other_revision.generic_results
        )
        merged_structured: dict[
            ObjectVersionId, StructuredResult
        ] = dict(current.structured_results)
        for version, structured in other_revision.structured_results:
            existing_structured = merged_structured.get(version)
            if (
                existing_structured is not None
                and existing_structured != structured
            ):
                raise ValueError(
                    "the revisions contain conflicting structured results"
                )
            merged_structured[version] = structured
        merged_tasks = self._merge_task_records(
            current.task_records, other_revision.task_records
        )
        merged_candidates = self._merge_candidate_records(
            current.candidate_records, other_revision.candidate_records
        )
        merged_names = dict(current.object_names)
        for version, name in other_revision.object_names:
            existing_name = merged_names.get(version)
            if existing_name is not None and existing_name != name:
                raise ValueError(
                    "the revisions contain conflicting object names"
                )
            merged_names[version] = name
        merged_relations = self._merge_construction_relations(
            current.construction_relations,
            other_revision.construction_relations,
        )
        event = self._record_event("Merge")
        revision = Revision(
            id=RevisionId(self._revision_ids.issue()),
            frame=current.frame,
            objects=tuple(
                dict.fromkeys(current.objects + other_revision.objects)
            ),
            links=tuple(
                dict.fromkeys(current.links + other_revision.links)
            ),
            events=tuple(
                dict.fromkeys(
                    current.events
                    + other_revision.events
                    + (event.id,)
                )
            ),
            label=label,
            parents=(current.id, other_revision.id),
            functions=tuple(
                dict.fromkeys(
                    current.functions + other_revision.functions
                )
            ),
            tasks=tuple(record.id for record in merged_tasks),
            attempts=tuple(
                dict.fromkeys(
                    current.attempts + other_revision.attempts
                )
            ),
            candidates=tuple(
                record.id for record in merged_candidates
            ),
            rewrites=tuple(
                dict.fromkeys(
                    current.rewrites + other_revision.rewrites
                )
            ),
            case_splits=tuple(
                dict.fromkeys(
                    current.case_splits + other_revision.case_splits
                )
            ),
            construction_relations=merged_relations,
            generic_results=merged_generic,
            structured_results=tuple(merged_structured.items()),
            world=self._runtime.world.id,
            producing_event=event.id,
            focus=current.focus,
            task_records=merged_tasks,
            candidate_records=merged_candidates,
            object_names=tuple(merged_names.items()),
            frame_digest=self._runtime.frames.digest(current.frame),
        )
        self._revisions[revision.id] = revision
        for parent in revision.parents:
            self._children.setdefault(parent, []).append(revision.id)
        self._head = revision.id
        self._events[event.id] = replace(
            event, output_revision=revision.id
        )
        return revision

    # --- case splits ---

    def case_split(self, term: T.Term) -> CaseSplitResult:
        """Create two child frames for `P` and `not P` and record the split.

        The two hypotheses are issued by the kernel.  The split is stored in
        both branch revisions; `merge_cases` can then merge the two histories
        while preserving the branch frames.

        A refusal from either branch commit aborts the whole split: the private
        exception rolls back both frames, the first judgment and every
        workspace record, so a failed split leaves no half case analysis.
        """
        try:
            return self._case_split(term)
        except _CaseSplitRefused as refused:
            return CaseSplitResult(
                OperationStatus.INVALID, detail=str(refused)
            )

    def _case_split(self, term: T.Term) -> CaseSplitResult:
        with self._transaction():
            runtime = self._runtime
            issued = elaborate.proposition(
                term, runtime.frames, self.frame, runtime.signature
            )
            if not isinstance(issued, Pr.Proposition):
                return CaseSplitResult(
                    OperationStatus.INVALID,
                    detail="the case assumption is not a proposition",
                )
            negated_term = T.app(
                runtime.signature.head_term(StructuralHead.NOT),
                issued.term,
            )
            negated = elaborate.proposition(
                negated_term,
                runtime.frames,
                self.frame,
                runtime.signature,
            )
            if not isinstance(negated, Pr.Proposition):
                return CaseSplitResult(
                    OperationStatus.INVALID,
                    detail="the negated assumption is not a proposition",
                )
            assumptions = runtime.frames.assumptions(self.frame)
            if any(
                existing.term in (issued.term, negated.term)
                for existing in assumptions
            ):
                return CaseSplitResult(
                    OperationStatus.INVALID,
                    detail="the case is already assumed",
                )
            positive_frame = runtime.frames.create(
                self.frame, hypotheses=(Hypothesis(issued),)
            )
            negative_frame = runtime.frames.create(
                self.frame, hypotheses=(Hypothesis(negated),)
            )
            positive = self._commit(
                CommitProposal(
                    positive_frame.id,
                    (issued,),
                    HypothesisChecker.id,
                    "assume",
                    "Hypothesis",
                    certificate=None,
                ),
            )
            if not isinstance(positive, Committed):
                raise _CaseSplitRefused(
                    "the positive case hypothesis was not issued: "
                    f"{positive.detail}"
                )
            negative = self._commit(
                CommitProposal(
                    negative_frame.id,
                    (negated,),
                    HypothesisChecker.id,
                    "assume",
                    "Hypothesis",
                    certificate=None,
                ),
            )
            if not isinstance(negative, Committed):
                raise _CaseSplitRefused(
                    "the negative case hypothesis was not issued: "
                    f"{negative.detail}"
                )
            positive_id = RevisionId(self._revision_ids.issue())
            negative_id = RevisionId(self._revision_ids.issue())
            split = CaseSplit(
                CaseSplitId(self._case_split_ids.issue()),
                issued,
                positive_frame.id,
                negative_frame.id,
                positive_id,
                negative_id,
            )
            self._case_splits[split.id] = split
            base = self.revision
            positive_event = self._record_event(
                "CaseSplit",
                judgments=positive.judgments + negative.judgments,
                execution_report=OperationStatus.VERIFIED,
            )
            self._append_revision(
                f"case {issued.term}",
                positive_event,
                frame=positive_frame.id,
                case_splits=base.case_splits + (split,),
                identifier=positive_id,
            )
            self.switch_to(base.id)
            negative_event = self._record_event(
                "CaseSplit",
                judgments=positive.judgments + negative.judgments,
                execution_report=OperationStatus.VERIFIED,
            )
            self._append_revision(
                f"case not {issued.term}",
                negative_event,
                frame=negative_frame.id,
                case_splits=base.case_splits + (split,),
                identifier=negative_id,
            )
            return CaseSplitResult(OperationStatus.VERIFIED, split, "")

    def _branch_head(self, identifier: RevisionId) -> Revision | None:
        """The latest revision reached by single-parent descendants.

        A case branch grows by ordinary single-parent revisions.  Following
        them includes work added after the split.  A merge (several parents) or
        a branch point (several children) ends the walk: choosing one of them
        would silently drop the other history.
        """
        current = self._revisions.get(identifier)
        if current is None:
            return None
        seen = {current.id}
        while True:
            children = self._children.get(current.id, ())
            if len(children) != 1:
                return current
            child = self._revisions.get(children[0])
            if child is None or child.parents != (current.id,):
                return current
            if child.id in seen:
                raise ValueError("the revision graph contains a cycle")
            current = child
            seen.add(current.id)

    def _ancestors(self, identifier: RevisionId) -> set[RevisionId]:
        found: set[RevisionId] = set()
        pending = [identifier]
        while pending:
            current = pending.pop()
            if current in found:
                continue
            found.add(current)
            pending.extend(self._revisions[current].parents)
        return found

    def _common_ancestor(
        self, first: RevisionId, second: RevisionId
    ) -> Revision | None:
        first_ancestors = self._ancestors(first)
        seen: set[RevisionId] = set()
        pending = [second]
        while pending:
            current = pending.pop(0)
            if current in seen:
                continue
            seen.add(current)
            if current in first_ancestors:
                return self._revisions[current]
            pending.extend(self._revisions[current].parents)
        return None

    def _is_ancestor_or_same(
        self, ancestor: RevisionId, descendant: RevisionId
    ) -> bool:
        return ancestor in self._ancestors(descendant)

    def merge_cases(
        self, split: CaseSplit, label: str = "merge cases"
    ) -> CaseMergeResult:
        """Merge the two branch histories of one trusted case split.

        The two frames are exact complements, so the split covers the base
        frame.  Branch results keep their original frames; this is a history
        merge with a recorded coverage split, not a promotion of branch
        judgments into the base frame.  Each branch contributes its latest
        single-parent descendant, so work added after the split is included.
        The split must be the recorded one and visible in the current view.
        The merged revision keeps the base revision's focus.
        """
        with self._transaction():
            recorded = self._case_splits.get(split.id)
            if recorded is None:
                return CaseMergeResult(
                    OperationStatus.INVALID,
                    split,
                    detail="the case split is not recorded",
                )
            if recorded != split:
                return CaseMergeResult(
                    OperationStatus.INVALID,
                    split,
                    detail="the case split does not match the recorded split",
                )
            if split not in self.revision.case_splits:
                return CaseMergeResult(
                    OperationStatus.INVALID,
                    split,
                    detail=(
                        "the case split is not visible in the current "
                        "revision"
                    ),
                )
            positive = self._branch_head(split.positive_revision)
            negative = self._branch_head(split.negative_revision)
            if positive is None or negative is None:
                return CaseMergeResult(
                    OperationStatus.INVALID,
                    split,
                    detail="a case branch revision is missing",
                )
            current = self.revision
            if not (
                self._is_ancestor_or_same(current.id, positive.id)
                or self._is_ancestor_or_same(current.id, negative.id)
            ):
                return CaseMergeResult(
                    OperationStatus.INVALID,
                    split,
                    detail="the current revision is not on a case branch",
                )
            base = self._common_ancestor(positive.id, negative.id)
            if base is None or base.id in (positive.id, negative.id):
                return CaseMergeResult(
                    OperationStatus.INVALID,
                    split,
                    detail="the case branches have no common base",
                )
            merged_generic = self._merge_generic_results(
                positive.generic_results, negative.generic_results
            )
            merged_structured: dict[
                ObjectVersionId, StructuredResult
            ] = dict(positive.structured_results)
            for version, structured in negative.structured_results:
                existing_structured = merged_structured.get(version)
                if (
                    existing_structured is not None
                    and existing_structured != structured
                ):
                    return CaseMergeResult(
                        OperationStatus.INVALID,
                        split,
                        detail="the branches contain conflicting structured "
                        "results",
                    )
                merged_structured[version] = structured
            try:
                merged_tasks = self._merge_task_records(
                    positive.task_records, negative.task_records
                )
                merged_candidates = self._merge_candidate_records(
                    positive.candidate_records, negative.candidate_records
                )
                merged_relations = self._merge_construction_relations(
                    positive.construction_relations,
                    negative.construction_relations,
                )
            except ValueError as error:
                return CaseMergeResult(
                    OperationStatus.INVALID,
                    split,
                    detail=str(error),
                )
            merged_names = dict(positive.object_names)
            for version, name in negative.object_names:
                existing_name = merged_names.get(version)
                if existing_name is not None and existing_name != name:
                    return CaseMergeResult(
                        OperationStatus.INVALID,
                        split,
                        detail="the branches contain conflicting object names",
                    )
                merged_names[version] = name
            event = self._record_event(
                "MergeCases",
                execution_report=OperationStatus.VERIFIED,
            )
            revision = Revision(
                id=RevisionId(self._revision_ids.issue()),
                frame=base.frame,
                objects=tuple(
                    dict.fromkeys(positive.objects + negative.objects)
                ),
                links=tuple(
                    dict.fromkeys(positive.links + negative.links)
                ),
                events=tuple(
                    dict.fromkeys(
                        positive.events
                        + negative.events
                        + (event.id,)
                    )
                ),
                label=label,
                parents=(base.id, positive.id, negative.id),
                functions=tuple(
                    dict.fromkeys(
                        positive.functions + negative.functions
                    )
                ),
                tasks=tuple(record.id for record in merged_tasks),
                attempts=tuple(
                    dict.fromkeys(
                        positive.attempts + negative.attempts
                    )
                ),
                candidates=tuple(
                    record.id for record in merged_candidates
                ),
                rewrites=tuple(
                    dict.fromkeys(
                        positive.rewrites + negative.rewrites
                    )
                ),
                case_splits=tuple(
                    dict.fromkeys(
                        positive.case_splits
                        + negative.case_splits
                        + (split,)
                    )
                ),
                construction_relations=merged_relations,
                generic_results=merged_generic,
                structured_results=tuple(merged_structured.items()),
                world=self._runtime.world.id,
                producing_event=event.id,
                focus=base.focus,
                task_records=merged_tasks,
                candidate_records=merged_candidates,
                object_names=tuple(merged_names.items()),
                frame_digest=self._runtime.frames.digest(base.frame),
            )
            self._revisions[revision.id] = revision
            for parent in revision.parents:
                self._children.setdefault(parent, []).append(revision.id)
            self._head = revision.id
            self._events[event.id] = replace(
                event, output_revision=revision.id
            )
            return CaseMergeResult(
                OperationStatus.VERIFIED, split, revision, ""
            )

    def merge_case_conclusion(
        self,
        split: CaseSplit,
        positive_judgment: JudgmentId,
        negative_judgment: JudgmentId,
    ) -> CaseConclusionResult:
        """Issue one conclusion from the two branches of a case split.

        The branch judgments must state the same formula, live in the two
        complementary frames, and have no open conditions.  The conclusion is
        not allowed to be assumed in either branch.
        """
        with self._transaction():
            runtime = self._runtime
            recorded = self._case_splits.get(split.id)
            if recorded is None:
                return CaseConclusionResult(
                    OperationStatus.INVALID,
                    detail="the case split is not recorded",
                )
            if recorded != split:
                return CaseConclusionResult(
                    OperationStatus.INVALID,
                    detail="the case split does not match the recorded split",
                )
            try:
                positive = runtime.store.get_judgment(positive_judgment)
                runtime.store.get_judgment(negative_judgment)
            except KeyError:
                return CaseConclusionResult(
                    OperationStatus.INVALID,
                    detail="a branch judgment does not exist",
                )
            issued = elaborate.proposition(
                positive.proposition.term,
                runtime.frames,
                self.frame,
                runtime.signature,
            )
            if not isinstance(issued, Pr.Proposition):
                return CaseConclusionResult(
                    OperationStatus.INVALID,
                    detail="the conclusion is not readable in the base frame",
                )
            committed = self._commit(
                CommitProposal(
                    self.frame,
                    (issued,),
                    "kernel.case_merge",
                    "case_merge",
                    "CaseAnalysis",
                    premises=(positive_judgment, negative_judgment),
                    certificate=CaseMergeCertificate(
                        split.assumption,
                        split.positive_frame,
                        split.negative_frame,
                        positive_judgment,
                        negative_judgment,
                    ),
                ),
            )
            if isinstance(committed, Committed):
                judgment = committed.judgments[0]
                event = self._record_event(
                    "MergeCaseConclusion",
                    judgments=(
                        judgment,
                        positive_judgment,
                        negative_judgment,
                    ),
                    execution_report=OperationStatus.VERIFIED,
                )
                self._append_revision(
                    f"case conclusion {issued.term}",
                    event,
                    case_splits=tuple(
                        dict.fromkeys(
                            self.revision.case_splits + (split,)
                        )
                    ),
                )
                return CaseConclusionResult(
                    OperationStatus.VERIFIED, judgment, issued, ""
                )
            if isinstance(committed, Rejected):
                status = (
                    OperationStatus.REFUTED
                    if committed.refutation is not None
                    else OperationStatus.INVALID
                )
                return CaseConclusionResult(status, detail=committed.detail)
            if isinstance(committed, Deferred):
                return CaseConclusionResult(
                    OperationStatus.UNSUPPORTED, detail=committed.detail
                )
            raise TypeError("commit returned an unknown result")

    @contextmanager
    def transaction(self) -> Iterator[None]:
        """Group several workspace actions into one atomic rollback unit.

        Every action still records its own revision and event.  If any action
        raises, the kernel batch, frames, workspace records and revision DAG are
        restored to the state before the first action.
        """
        with self._transaction():
            yield

    # --- record keeping ---

    @contextmanager
    def _transaction(self) -> Iterator[None]:
        """One synchronous workspace transaction.

        The kernel batch and the workspace records become visible together: if
        anything raises after the kernel has staged its judgments, both the
        kernel dictionaries and the workspace snapshot are restored.  A
        refusal that returns before any record is written leaves no event or
        revision; a rejected or refuted candidate that reached the recording
        stage remains in history.  Only an exception means that no part of the
        action happened.
        """
        expressions = dict(self._expressions)
        functions = dict(self._functions)
        candidates = dict(self._candidates)
        tasks = dict(self._tasks)
        attempts = dict(self._attempts)
        case_splits = dict(self._case_splits)
        events = dict(self._events)
        revisions = dict(self._revisions)
        children = {
            parent: list(children)
            for parent, children in self._children.items()
        }
        head = self._head
        try:
            with self._runtime.frames.transaction():
                with self._runtime.store.transaction():
                    yield
        except BaseException:
            self._expressions = expressions
            self._functions = functions
            self._candidates = candidates
            self._tasks = tasks
            self._attempts = attempts
            self._case_splits = case_splits
            self._events = events
            self._revisions = revisions
            self._children = children
            self._head = head
            raise

    def _input_issue(
        self, expression: Expression
    ) -> tuple[OperationStatus, str] | None:
        """Why `expression` cannot be used as an input in this view, if any.

        An Expression is a handle into this workspace, not a value the caller
        may reconstruct.  Version ids are workspace-local, so a version-only
        check would accept an equal id from another workspace (or a forged
        Expression with a visible version).
        """
        if self._expressions.get(expression.version) is not expression:
            return (
                OperationStatus.INVALID,
                "an input is not an object of this workspace",
            )
        if not self._runtime.frames.is_visible(expression.frame, self.frame):
            return (
                OperationStatus.UNSUPPORTED,
                "an input is outside the current frame",
            )
        if expression.version not in self.revision.objects:
            return (
                OperationStatus.INVALID,
                "an input is not visible in the current revision",
            )
        return None

    @staticmethod
    def _rejected_projection(
        committed: Rejected,
        *,
        target: Pr.Proposition | None,
        budget: ExecutionBudget | None,
        attempted: tuple[str, ...],
    ) -> tuple[
        OperationStatus,
        CandidateState,
        CandidateApplicability,
        Blocker | None,
    ]:
        """Map one rejected submission without flattening its kind.

        A refuted conclusion is `REFUTED`; a refuted necessary condition is
        `UNSUPPORTED` with the condition recorded in the blocker, never a
        conclusion refutation.  Invalid evidence and invalid requests remain
        distinct through their missing capability and status.
        """
        if committed.refutation is not None:
            return (
                OperationStatus.REFUTED,
                CandidateState.REFUTED,
                CandidateApplicability.OUT_OF_SCOPE,
                None,
            )
        if committed.kind is RejectedKind.REFUTED_CONDITION:
            return (
                OperationStatus.UNSUPPORTED,
                CandidateState.UNVERIFIED,
                CandidateApplicability.BLOCKED,
                Blocker(
                    Reason.GUARDED,
                    "a necessary condition was refuted: " + committed.detail,
                    conditions=committed.refuted_conditions,
                    attempted=attempted,
                    target=target,
                    budget=budget,
                ),
            )
        missing = (
            frozenset({"accepted_proposal_evidence"})
            if committed.kind is RejectedKind.INVALID_EVIDENCE
            else frozenset({"valid_proposal_request"})
        )
        return (
            OperationStatus.INVALID,
            CandidateState.UNVERIFIED,
            CandidateApplicability.BLOCKED,
            Blocker(
                Reason.FRAGMENT,
                "the checker rejected the proposed evidence: "
                + committed.detail,
                missing=missing,
                attempted=attempted,
                target=target,
                budget=budget,
            ),
        )

    @staticmethod
    def _status_for(reason: Reason) -> OperationStatus:
        """A fragment gap is unsupported; an undecided premise is unknown."""
        if reason is Reason.FRAGMENT:
            return OperationStatus.UNSUPPORTED
        return OperationStatus.UNKNOWN

    def _failure(
        self,
        operation: str,
        status: OperationStatus,
        detail: str,
        *,
        region: Pr.Proposition | None = None,
        trace: tuple[str, ...] = (),
        task: TaskRecord | None = None,
        blocker: Blocker | None = None,
        target: Pr.Proposition | None = None,
        budget: ExecutionBudget | None = None,
    ) -> OperationResult:
        if blocker is None and status is OperationStatus.UNSUPPORTED:
            blocker = Blocker(
                Reason.FRAGMENT,
                detail,
                target=target,
                budget=budget,
            )
        return OperationResult(
            operation,
            status,
            None,
            (),
            None,
            detail,
            region,
            None,
            trace,
            task,
            blocker=blocker,
        )

    def _problem_structure_issue(
        self,
        request: OperationRequest,
        problem: ProblemSpec,
    ) -> str | None:
        """Whether a built problem describes the requested fixed structure.

        The problem carries typed inputs while the request is still a draft of
        terms.  The draft terms are elaborated in the request frame first, so a
        request that mentions an alias compares its resolved term with the
        problem's resolved input instead of being refused by spelling.  Every
        typed input must also be readable in the current frame, so an operation
        cannot fix a problem whose inputs come from a foreign frame or world.
        """
        typed_request_inputs: list[Ty.TypedExpr] = []
        for term in request.inputs:
            outcome = elaborate.typed(
                term,
                self._runtime.frames,
                request.frame,
                self._runtime.signature,
            )
            if not isinstance(outcome, Ty.TypedExpr):
                return (
                    "the requested inputs cannot be typed: "
                    + outcome.detail
                )
            typed_request_inputs.append(outcome)
        if tuple(item.term for item in problem.inputs) != tuple(
            item.term for item in typed_request_inputs
        ):
            return "the problem does not describe the requested inputs"
        frames = self._runtime.frames
        world = self._runtime.world.id
        for item in problem.inputs:
            if item.meaning.world != world:
                return "the problem inputs are outside the current world"
            if not frames.is_visible(item.meaning.frame, self.frame):
                return "the problem inputs are outside the current frame"
        if request.target is not None and problem.target != request.target:
            return "the problem does not describe the requested target"
        if problem.region != request.region:
            return "the problem does not describe the requested region"
        return None

    def _same_problem(
        self,
        stored: ProblemSpec,
        execution: ProblemSpec,
    ) -> bool:
        """Whether an execution rebuilt the manual task's fixed problem.

        The execution types its inputs in the current frame while the stored
        problem was fixed when the task was defined.  A descendant frame may
        therefore hold the stored inputs under an ancestor meaning key; the
        comparison is by resolved terms and fixed dimensions, not by the frame
        that happened to type each copy.  The explicit `externalizable` set is
        part of the fixed problem and must match exactly: an execution that
        rebuilt a different set did not run the task the user defined.  The
        exactness, interpretation requirement and domain requirement are fixed
        request contract fields as well, so an execution that rebuilt a
        different answer standard, interpretation or coefficient/value domain
        did not run the task the user defined.  The stored inputs must still be
        readable from the current frame and must not mention escaping symbols.
        """
        if stored.operation != execution.operation:
            return False
        if tuple(item.term for item in stored.inputs) != tuple(
            item.term for item in execution.inputs
        ):
            return False
        if stored.roles != execution.roles:
            return False
        if stored.function_inputs != execution.function_inputs:
            return False
        if stored.region != execution.region:
            return False
        if stored.result_language != execution.result_language:
            return False
        if stored.coverage != execution.coverage:
            return False
        if stored.externalizable != execution.externalizable:
            return False
        if stored.exactness != execution.exactness:
            return False
        if (
            stored.interpretation_requirement
            != execution.interpretation_requirement
        ):
            return False
        if stored.domain_requirement != execution.domain_requirement:
            return False
        frames = self._runtime.frames
        world = self._runtime.world.id
        for item in stored.inputs:
            if item.meaning.world != world:
                return False
            if not frames.is_visible(item.meaning.frame, self.frame):
                return False
            if frames.escapes(self.frame, item.term):
                return False
        return True

    @staticmethod
    def _problem_dimension_issue(
        request: OperationRequest,
        problem: ProblemSpec,
    ) -> str | None:
        """Whether an explicit request dimension differs from the fixed one."""
        if (
            request.result_language is not None
            and problem.result_language != request.result_language
        ):
            return (
                "the problem does not describe the requested result language"
            )
        if (
            request.parameter_mode is not None
            and problem.parameter_mode != request.parameter_mode
        ):
            return (
                "the problem does not describe the requested parameter mode"
            )
        return None

    def _record_blocked_definition(
        self,
        problem: ProblemSpec,
        detail: str,
        blocker: Blocker,
        depends_on: tuple[TaskId, ...],
        input_versions: tuple[ObjectVersionId, ...],
    ) -> TaskRecord:
        """Record a manual problem that admission refused at definition time."""
        if problem.region is not None:
            blocker = replace(blocker, target=problem.region)
        task_id = TaskId(self._task_ids.issue())
        event = self._record_event(
            "DefineProblem",
            tasks=(task_id,),
            inputs=input_versions,
        )
        task = TaskRecord(
            task_id,
            problem,
            self.frame,
            derive_task_state(problem, (), (), blocker, ()),
            (),
            detail,
            TaskOrigin.MANUAL,
            None,
            depends_on,
            input_versions,
            (),
            blocker=blocker,
        )
        self._tasks[task.id] = task
        self._append_revision(
            f"define problem {task.id}",
            event,
            focus=TaskFocus(task.id),
        )
        return task

    def _record_blocked_task(
        self,
        operation: str,
        problem: ProblemSpec,
        detail: str,
        status: OperationStatus = OperationStatus.UNSUPPORTED,
        *,
        inputs: tuple[ObjectVersionId, ...] = (),
        parameters: tuple[tuple[str, object], ...] = (),
        blocker: Blocker | None = None,
        target: Pr.Proposition | None = None,
        budget: ExecutionBudget | None = None,
    ) -> OperationResult:
        """Record a fixed problem whose proposal was refused.

        An unsupported or invalid proposal is a gap in the implemented
        proposal/checking fragment unless the caller supplies a more precise
        blocker.  An unknown outcome must carry its own reason: the four
        classes are not interchangeable.  `target` and `budget` are supplied by
        the caller from its fixed problem and execution request; this method
        never derives a target of its own.
        """
        if blocker is None:
            if status is OperationStatus.UNKNOWN:
                raise ValueError(
                    "an unknown task needs an explicit blocker"
                )
            blocker = Blocker(
                Reason.FRAGMENT,
                detail,
                target=target,
                budget=budget,
            )
        elif target is not None or budget is not None:
            blocker = replace(
                blocker,
                target=(
                    blocker.target
                    if blocker.target is not None
                    else target
                ),
                budget=(
                    blocker.budget
                    if blocker.budget is not None
                    else budget
                ),
            )
        task_id = TaskId(self._task_ids.issue())
        attempt = self._record_attempt(
            task_id,
            ExecutionState.BLOCKED,
            status,
            detail,
            blocker=blocker,
        )
        event = self._record_event(
            operation,
            tasks=(task_id,),
            attempts=(attempt.id,),
            inputs=inputs,
            parameters=parameters,
            execution_report=status,
        )
        task = TaskRecord(
            task_id,
            problem,
            self.frame,
            derive_task_state(problem, (), (), blocker, (attempt,)),
            (),
            detail,
            TaskOrigin.EXECUTION,
            None,
            (),
            (),
            (attempt.id,),
            blocker=blocker,
        )
        self._tasks[task.id] = task
        self._append_revision(f"{operation} blocked", event)
        return self._failure(
            operation, status, detail, task=task, blocker=blocker
        )

    def _record_expression(
        self,
        term: T.Term,
        label: str,
        source_operation: str = "",
        *,
        object_id: ObjectId | None = None,
        presentation: tuple[tuple[str, str], ...] = (),
    ) -> Expression:
        expression = Expression(
            ObjectId(self._objects.issue())
            if object_id is None
            else object_id,
            ObjectVersionId(self._versions.issue()),
            term,
            self.frame,
            label,
            source_operation,
            presentation,
        )
        self._expressions[expression.version] = expression
        return expression

    def _record_event(
        self,
        operation: str,
        *,
        objects: tuple[ObjectVersionId, ...] = (),
        functions: tuple[ObjectVersionId, ...] = (),
        tasks: tuple[TaskId, ...] = (),
        attempts: tuple[ExecutionAttemptId, ...] = (),
        candidates: tuple[CandidateId, ...] = (),
        judgments: tuple[JudgmentId, ...] = (),
        inputs: tuple[ObjectVersionId, ...] = (),
        parameters: tuple[tuple[str, object], ...] = (),
        execution_report: OperationStatus | None = None,
    ) -> Event:
        registered = self._runtime.operations.get(operation)
        event = Event(
            id=EventId(self._event_ids.issue()),
            operation=operation,
            operation_version=(
                "" if registered is None else registered.version
            ),
            objects=objects,
            functions=functions,
            tasks=tasks,
            attempts=attempts,
            candidates=candidates,
            judgments=judgments,
            input_revision=self.revision.id,
            frame=self.frame,
            inputs=inputs,
            parameters=parameters,
            execution_report=execution_report,
            frame_digest=self._runtime.frames.digest(self.frame),
        )
        self._events[event.id] = event
        return event

    def _record_attempt(
        self,
        task: TaskId,
        state: ExecutionState,
        outcome: OperationStatus | None,
        detail: str,
        *,
        blocker: Blocker | None = None,
    ) -> ExecutionAttempt:
        attempt = ExecutionAttempt(
            ExecutionAttemptId(self._attempt_ids.issue()),
            task,
            state,
            outcome,
            detail,
            blocker=blocker,
        )
        self._attempts[attempt.id] = attempt
        return attempt

    def _open_obligations(
        self, committed: Committed
    ) -> tuple[Pr.Proposition, ...]:
        """The obligations that remain open after this validated batch.

        `Committed.obligations` includes inherited, reused and new
        obligations; a batch may also discharge some of them.  Only
        obligations that remain open in the current frame are conditions of
        the result.  A discharged obligation is support, not an open premise.
        """
        store = self._runtime.store
        discharged = set(committed.discharged)
        open_propositions: list[Pr.Proposition] = []
        for identifier in committed.obligations:
            if identifier in discharged:
                continue
            if store.is_discharged(identifier, self.frame):
                continue
            proposition = store.get_obligation(identifier).proposition
            if proposition not in open_propositions:
                open_propositions.append(proposition)
        return tuple(open_propositions)

    def _task_candidates(
        self,
        identifiers: tuple[CandidateId, ...],
        extra: tuple[Candidate, ...] = (),
    ) -> tuple[Candidate, ...]:
        """Candidate versions visible for a task in the current snapshot.

        `extra` carries a record the caller has just derived but not yet
        published in a revision (a manual check or edit).  It must never fall
        back to the global version store: after undo that store still holds
        later versions that are not visible.
        """
        visible = {
            candidate.id: candidate
            for candidate in self.revision.candidate_records
        }
        for candidate in extra:
            visible[candidate.id] = candidate
        return tuple(
            visible[identifier]
            for identifier in identifiers
            if identifier in visible
        )

    def _task_links(
        self,
        identifiers: tuple[CandidateId, ...],
        extra: tuple[VerificationLink, ...] = (),
        *,
        extra_candidates: tuple[Candidate, ...] = (),
    ) -> tuple[VerificationLink, ...]:
        """The visible links that can affect the current task state.

        A link is scoped to the frame in which its check was issued.  A link
        from a sibling frame is visible as a record but cannot support a task in
        the current frame.  The link's specification kind must also agree with
        the candidate it belongs to; a mismatch is an internal record error, not
        a second kind of evidence.  The kind check comes first so a corrupt
        record is never silently dropped as merely out of view.

        Candidate records come from the revision snapshot, with `extra` naming
        records the caller has just derived.  The global store would leak later
        versions into an older revision after undo.
        """
        known = set(identifiers)
        candidates = {
            candidate.id: candidate
            for candidate in self.revision.candidate_records
        }
        for extra_candidate in extra_candidates:
            candidates[extra_candidate.id] = extra_candidate
        links: list[VerificationLink] = []
        for link in self.revision.links + extra:
            if link.candidate not in known:
                continue
            candidate = candidates.get(link.candidate)
            if (
                candidate is not None
                and link.specification_kind != candidate.specification_kind
            ):
                raise ValueError(
                    "a verification link names another specification kind"
                )
            if not self._runtime.frames.is_visible(link.frame, self.frame):
                continue
            links.append(link)
        return tuple(links)

    def _task_attempts(
        self, identifiers: tuple[ExecutionAttemptId, ...]
    ) -> tuple[ExecutionAttempt, ...]:
        return tuple(self._attempts[identifier] for identifier in identifiers)

    def _snapshot_tasks(
        self,
        current: tuple[TaskRecord, ...],
        identifiers: tuple[TaskId, ...],
    ) -> tuple[TaskRecord, ...]:
        """The current task snapshot plus the versions named by one event."""
        records = {record.id: record for record in current}
        for identifier in identifiers:
            record = self._tasks.get(identifier)
            if record is None:
                raise ValueError(
                    f"an event names an unknown task record: {identifier}"
                )
            records[identifier] = record
        return tuple(records.values())

    def _snapshot_candidates(
        self,
        current: tuple[Candidate, ...],
        identifiers: tuple[CandidateId, ...],
    ) -> tuple[Candidate, ...]:
        """The current candidate snapshot plus the versions named by one event."""
        records = {record.id: record for record in current}
        for identifier in identifiers:
            record = self._candidates.get(identifier)
            if record is None:
                raise ValueError(
                    "an event names an unknown candidate record: "
                    f"{identifier}"
                )
            records[identifier] = record
        return tuple(records.values())

    @staticmethod
    def _merge_task_records(
        first: tuple[TaskRecord, ...],
        second: tuple[TaskRecord, ...],
    ) -> tuple[TaskRecord, ...]:
        """Union two task snapshots, refusing two versions of one task id."""
        merged = {record.id: record for record in first}
        for record in second:
            existing = merged.get(record.id)
            if existing is not None and existing != record:
                raise ValueError(
                    "the revisions contain conflicting task records"
                )
            merged[record.id] = record
        return tuple(merged.values())

    @staticmethod
    def _merge_candidate_records(
        first: tuple[Candidate, ...],
        second: tuple[Candidate, ...],
    ) -> tuple[Candidate, ...]:
        """Union two candidate snapshots, refusing two versions of one id."""
        merged = {record.id: record for record in first}
        for record in second:
            existing = merged.get(record.id)
            if existing is not None and existing != record:
                raise ValueError(
                    "the revisions contain conflicting candidate records"
                )
            merged[record.id] = record
        return tuple(merged.values())

    @staticmethod
    def _merge_generic_results(
        first: tuple[tuple[ObjectVersionId, GenericResult], ...],
        second: tuple[tuple[ObjectVersionId, GenericResult], ...],
    ) -> tuple[tuple[ObjectVersionId, GenericResult], ...]:
        """Union two family snapshots without collapsing a source to one row.

        A source version may carry several families with different
        orientations, so the merge key is the recorded family, not only its
        source version.  Exact duplicate recordings inherited from a common
        ancestor are kept once; different families for the same source stay
        side by side in recording order.
        """
        merged: list[tuple[ObjectVersionId, GenericResult]] = []
        for item in first + second:
            if any(item == existing for existing in merged):
                continue
            merged.append(item)
        return tuple(merged)

    @staticmethod
    def _merge_construction_relations(
        first: tuple[ConstructionRelation, ...],
        second: tuple[ConstructionRelation, ...],
    ) -> tuple[ConstructionRelation, ...]:
        """Union two relation snapshots, deduplicating by relation identity.

        The relation identity is `(source, target, kind)`, not the dataclass
        identity: a branch that inherited the same relation must not duplicate
        it, while two different specifications for the same edge are a conflict
        rather than a second relation.
        """
        merged: dict[
            tuple[ObjectVersionId, ObjectVersionId, str],
            ConstructionRelation,
        ] = {}
        for relation in first + second:
            key = (relation.source, relation.target, relation.kind)
            existing = merged.get(key)
            if existing is not None and existing != relation:
                raise ValueError(
                    "the revisions contain conflicting construction relations"
                )
            merged[key] = relation
        return tuple(merged.values())

    def _append_revision(
        self,
        label: str,
        event: Event,
        links: tuple[VerificationLink, ...] = (),
        *,
        frame: FrameId | None = None,
        generic_results: tuple[
            tuple[ObjectVersionId, GenericResult], ...
        ] | None = None,
        structured_results: tuple[
            tuple[ObjectVersionId, StructuredResult], ...
        ] | None = None,
        rewrites: tuple[RewriteRecord, ...] | None = None,
        case_splits: tuple[CaseSplit, ...] | None = None,
        construction_relations: tuple[ConstructionRelation, ...] | None = None,
        identifier: RevisionId | None = None,
        focus: Focus | None | _KeepFocus = _KEEP_FOCUS,
    ) -> Revision:
        recorded = set(event.judgments)
        for link in links:
            if link.judgment is not None and link.judgment not in recorded:
                raise ValueError(
                    "a verification link references a judgment outside its "
                    "event"
                )
        current = self.revision
        target_frame = current.frame if frame is None else frame
        task_records = self._snapshot_tasks(
            current.task_records, event.tasks
        )
        candidate_records = self._snapshot_candidates(
            current.candidate_records, event.candidates
        )
        object_names = dict(current.object_names)
        for version in event.objects:
            object_names[version] = f"v{version}"
        revision = Revision(
            id=(
                RevisionId(self._revision_ids.issue())
                if identifier is None
                else identifier
            ),
            frame=target_frame,
            objects=tuple(dict.fromkeys(current.objects + event.objects)),
            links=current.links + links,
            events=current.events + (event.id,),
            label=label,
            parents=(current.id,),
            functions=tuple(
                dict.fromkeys(current.functions + event.functions)
            ),
            tasks=tuple(dict.fromkeys(current.tasks + event.tasks)),
            attempts=tuple(
                dict.fromkeys(current.attempts + event.attempts)
            ),
            candidates=tuple(
                dict.fromkeys(current.candidates + event.candidates)
            ),
            rewrites=(
                current.rewrites if rewrites is None else rewrites
            ),
            case_splits=(
                current.case_splits if case_splits is None else case_splits
            ),
            construction_relations=(
                current.construction_relations
                if construction_relations is None
                else construction_relations
            ),
            generic_results=(
                current.generic_results
                if generic_results is None
                else generic_results
            ),
            structured_results=(
                current.structured_results
                if structured_results is None
                else structured_results
            ),
            world=self._runtime.world.id,
            producing_event=event.id,
            focus=(
                current.focus
                if isinstance(focus, _KeepFocus)
                else focus
            ),
            task_records=task_records,
            candidate_records=candidate_records,
            object_names=tuple(object_names.items()),
            frame_digest=self._runtime.frames.digest(target_frame),
        )
        self._revisions[revision.id] = revision
        self._children.setdefault(current.id, []).append(revision.id)
        self._head = revision.id
        self._events[event.id] = replace(
            event, output_revision=revision.id
        )
        return revision


__all__ = ["Workspace"]
