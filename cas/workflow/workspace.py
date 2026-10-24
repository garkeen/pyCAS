"""Workspace: generic operation application, records and history.

The workspace owns presentation and history, never mathematics. It resolves
current object versions, asks the registered operation for a problem and a
proposal, commits the proposal through the declared checker binding, and records
the resulting expression, verification links, event and revision.

Differentiation and specialisation are registered operations, not branches in
this module. Adding another operation does not change this file.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import replace
from fractions import Fraction
from typing import TYPE_CHECKING, Any

from cas.foundation.ids import (
    CandidateId,
    EventId,
    FrameId,
    IdIssuer,
    JudgmentId,
    ObjectId,
    ObjectVersionId,
    RevisionId,
    SymbolId,
)
from cas.kernel.commit import (
    CommitProposal,
    Committed,
    Deferred,
    Rejected,
    commit,
)
from cas.kernel.consistency import assess_consistency
from cas.kernel.context_rules import HypothesisChecker
from cas.kernel.model import Applicability, Inconsistent
from cas.language import propositions as Pr
from cas.operations.protocols import (
    GenericResultInput,
    OperationInput,
    OperationRequest,
    ProblemBuilt,
    ProblemInvalid,
    ProblemUnsupported,
    ProposalInvalid,
    ProposalUnsupported,
    Proposed,
    ValueMappingInput,
)
from cas.semantics import elaborate
from cas.semantics.frames import Hypothesis
from cas.semantics.specialization import GenericResult
from cas.syntax import term as T
from cas.workflow.records import (
    AssumptionResult,
    Candidate,
    Event,
    Expression,
    OperationResult,
    OperationStatus,
    Revision,
    VerificationLink,
)

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


class Workspace:
    """One session over an assembled runtime."""

    def __init__(self, runtime: Runtime[Any]) -> None:
        self._runtime = runtime
        self._objects = IdIssuer()
        self._versions = IdIssuer()
        self._candidate_ids = IdIssuer()
        self._event_ids = IdIssuer()
        self._expressions: dict[ObjectVersionId, Expression] = {}
        self._generic_results: dict[ObjectVersionId, GenericResult] = {}
        self._candidates: dict[CandidateId, Candidate] = {}
        self._events: dict[EventId, Event] = {}
        self._revisions: list[Revision] = [
            Revision(
                RevisionId(0),
                runtime.frame.id,
                (),
                (),
                (),
                "start",
            )
        ]
        self._index = 0

    # --- the current view ---

    @property
    def revision(self) -> Revision:
        return self._revisions[self._index]

    @property
    def frame(self) -> FrameId:
        return self.revision.frame

    def expressions(self) -> tuple[Expression, ...]:
        return tuple(
            self._expressions[version] for version in self.revision.objects
        )

    def links(self) -> tuple[VerificationLink, ...]:
        return self.revision.links

    def events(self) -> tuple[Event, ...]:
        return tuple(self._events[event] for event in self.revision.events)

    def candidate(self, identifier: CandidateId) -> Candidate:
        return self._candidates[identifier]

    def applicability(self, judgment: JudgmentId) -> Applicability:
        return self._runtime.store.applicability(judgment, self.frame)

    # --- operations ---

    def intake(self, term: T.Term, label: str = "") -> Expression:
        """Store an expression object. No judgment is created."""
        expression = self._record_expression(term, label)
        event = self._record_event("Intake", objects=(expression.version,))
        self._append_revision(f"intake {label or expression.id}", event)
        return expression

    def assume(self, term: T.Term) -> AssumptionResult:
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
        outcome = commit(
            runtime.store,
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
        event = self._record_event(
            "Assume",
            judgments=(judgment,) + witness,
            note="inconsistent" if inconsistent else "",
        )
        self._append_revision(
            f"assume {issued.term}", event, frame=child.id
        )
        return AssumptionResult(
            OperationStatus.INVALID if inconsistent else OperationStatus.VERIFIED,
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

    def apply(
        self,
        operation_id: str,
        inputs: tuple[Expression, ...],
        *,
        target: SymbolId | None = None,
        region: Pr.Proposition | None = None,
        parameters: tuple[tuple[str, OperationInput], ...] = (),
    ) -> OperationResult:
        """Apply one registered operation to fixed current object versions."""
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
        visible = {
            expression.version for expression in self.expressions()
        }
        for expression in inputs:
            if not runtime.frames.is_visible(expression.frame, self.frame):
                return self._failure(
                    operation_id,
                    OperationStatus.UNSUPPORTED,
                    "an input is outside the current frame",
                )
            if expression.version not in visible:
                return self._failure(
                    operation_id,
                    OperationStatus.INVALID,
                    "an input is not visible in the current revision",
                )

        operation = runtime.operations.get(operation_id)
        if operation is None:
            return self._failure(
                operation_id,
                OperationStatus.UNSUPPORTED,
                f"operation not registered: {operation_id}",
            )
        request = OperationRequest(
            self.frame,
            tuple(expression.term for expression in inputs),
            target,
            region,
            tuple(parameters),
        )
        problem_outcome = operation.build_problem(request)
        if isinstance(problem_outcome, ProblemUnsupported):
            return self._failure(
                operation_id,
                OperationStatus.UNSUPPORTED,
                problem_outcome.detail,
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
        problem = problem_outcome.problem

        proposal_outcome = operation.propose(request, problem)
        if isinstance(proposal_outcome, ProposalUnsupported):
            return self._failure(
                operation_id,
                OperationStatus.UNSUPPORTED,
                proposal_outcome.detail,
            )
        if isinstance(proposal_outcome, ProposalInvalid):
            return self._failure(
                operation_id,
                OperationStatus.INVALID,
                proposal_outcome.detail,
            )
        if not isinstance(proposal_outcome, Proposed):
            raise TypeError(
                "an operation returned an unknown proposal outcome"
            )
        proposal = proposal_outcome.proposal
        binding = next(
            (
                item
                for item in operation.checker_bindings
                if item.specification_kind == proposal.specification_kind
            ),
            None,
        )
        if binding is None:
            return self._failure(
                operation_id,
                OperationStatus.INVALID,
                "the operation has no checker for the proposed specification",
            )

        candidate_problem = (
            problem
            if proposal.result_region is None
            else replace(problem, region=proposal.result_region)
        )
        candidate = Candidate(
            CandidateId(self._candidate_ids.issue()),
            candidate_problem,
            proposal.result,
            self.frame,
        )
        self._candidates[candidate.id] = candidate

        committed = commit(
            runtime.store,
            CommitProposal(
                self.frame,
                proposal.specifications,
                binding.checker_id,
                binding.problem_kind,
                proposal.specification_kind,
                certificate=proposal.certificate,
            ),
        )
        judgments: tuple[JudgmentId, ...] = ()
        if isinstance(committed, Committed):
            status = (
                OperationStatus.CONDITIONAL
                if proposal.result_region is not None
                else OperationStatus.VERIFIED
            )
            judgments = committed.judgments
            detail = ""
        elif isinstance(committed, Rejected):
            status = (
                OperationStatus.REFUTED
                if committed.refutation is not None
                else OperationStatus.INVALID
            )
            detail = committed.detail
        elif isinstance(committed, Deferred):
            status = OperationStatus.UNSUPPORTED
            detail = committed.detail
        else:
            raise TypeError("commit returned an unknown result")

        result: Expression | None = None
        generic: GenericResult | None = None
        if status in (OperationStatus.VERIFIED, OperationStatus.CONDITIONAL):
            result = self._record_expression(
                proposal.result,
                f"{operation_id} {inputs[0].label or inputs[0].id}",
            )
            if proposal.coverage is not None:
                if proposal.valid_on is None:
                    raise AssertionError(
                        "a coverage claim without a validity region"
                    )
                generic = GenericResult(
                    result=proposal.result,
                    valid_on=proposal.valid_on,
                    excluded_cases=proposal.excluded_cases,
                    correctness_specification=proposal.specifications[0],
                    coverage_claim=proposal.coverage,
                )
                self._generic_results[inputs[0].version] = generic

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
                candidate.id,
                specification,
                judgments[index] if index < len(judgments) else None,
                link_status,
                detail,
                proposal.result_region,
            )
            for index, specification in enumerate(proposal.specifications)
        )
        event = self._record_event(
            operation_id,
            objects=() if result is None else (result.version,),
            candidates=(candidate.id,),
            judgments=judgments,
            note=detail,
        )
        self._append_revision(
            f"{operation_id} {inputs[0].id}", event, links
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
        )

    def differentiate(
        self,
        source: Expression,
        variable: SymbolId,
    ) -> OperationResult:
        """Convenience entry for the registered differentiation operation."""
        return self.apply("differentiate", (source,), target=variable)

    def generic_result(self, source: Expression) -> GenericResult | None:
        """The verified parameter-family result associated with `source`."""
        return self._generic_results.get(source.version)

    def specialize(
        self,
        source: Expression,
        values: Mapping[SymbolId, Fraction],
        *,
        generic: GenericResult | None = None,
    ) -> OperationResult:
        """Convenience entry for the registered specialisation operation."""
        if not self._runtime.request.parameters:
            return self._failure(
                "specialize",
                OperationStatus.UNSUPPORTED,
                "this runtime has no formal parameters",
            )
        family = (
            generic
            if generic is not None
            else self._generic_results.get(source.version)
        )
        if family is None:
            return self._failure(
                "specialize",
                OperationStatus.UNSUPPORTED,
                "differentiate the source first so a verified parameter "
                "family exists",
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
        """Step back one revision; returns False at the beginning."""
        if self._index == 0:
            return False
        self._index -= 1
        return True

    def redo(self) -> bool:
        """Step forward one revision; returns False at the newest one."""
        if self._index + 1 >= len(self._revisions):
            return False
        self._index += 1
        return True

    # --- record keeping ---

    def _failure(
        self,
        operation: str,
        status: OperationStatus,
        detail: str,
        *,
        region: Pr.Proposition | None = None,
        trace: tuple[str, ...] = (),
    ) -> OperationResult:
        return OperationResult(
            operation, status, None, (), None, detail, region, None, trace
        )

    def _record_expression(self, term: T.Term, label: str) -> Expression:
        expression = Expression(
            ObjectId(self._objects.issue()),
            ObjectVersionId(self._versions.issue()),
            term,
            self.frame,
            label,
        )
        self._expressions[expression.version] = expression
        return expression

    def _record_event(
        self,
        operation: str,
        *,
        objects: tuple[ObjectVersionId, ...] = (),
        candidates: tuple[CandidateId, ...] = (),
        judgments: tuple[JudgmentId, ...] = (),
        note: str = "",
    ) -> Event:
        event = Event(
            EventId(self._event_ids.issue()),
            operation,
            objects,
            candidates,
            judgments,
            note,
        )
        self._events[event.id] = event
        return event

    def _append_revision(
        self,
        label: str,
        event: Event,
        links: tuple[VerificationLink, ...] = (),
        *,
        frame: FrameId | None = None,
    ) -> Revision:
        current = self.revision
        revision = Revision(
            RevisionId(len(self._revisions)),
            current.frame if frame is None else frame,
            tuple(dict.fromkeys(current.objects + event.objects)),
            current.links + links,
            current.events + (event.id,),
            label,
        )
        del self._revisions[self._index + 1:]
        self._revisions.append(revision)
        self._index = len(self._revisions) - 1
        return revision


__all__ = ["Workspace"]
