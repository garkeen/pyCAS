"""Workspace: expression objects, candidates, verification links and undo.

The workspace owns presentation and history, never mathematics.

- Intake stores an expression object and creates no judgment.
- Differentiation computes a candidate, builds the exact specification, and asks
  the kernel to commit it. The verification link records the judgment id only
  when the kernel actually issued one.
- Undo and redo move a revision pointer over immutable snapshots. The ledger is
  append-only and is never rolled back.

A failed verification keeps its candidate and its reason; it is not deleted and
it is not displayed as a result.
"""

from __future__ import annotations

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
from cas.kernel.model import Applicability
from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language.problems import (
    Coverage,
    ProblemSpec,
    ResultLanguage,
)
from cas.math.calculus.differentiation.checker import DerivativeCertificate
from cas.math.calculus.differentiation.specification import has_derivative
from cas.semantics import elaborate
from cas.syntax import term as T
from cas.workflow.records import (
    Candidate,
    DerivativeResult,
    Event,
    Expression,
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

    def differentiate(
        self,
        source: Expression,
        variable: SymbolId,
    ) -> DerivativeResult:
        """Differentiate one expression and try to publish the specification."""
        runtime = self._runtime
        if variable != runtime.variable:
            return DerivativeResult(
                OperationStatus.UNSUPPORTED,
                None,
                None,
                None,
                "this runtime differentiates with respect to x only",
            )
        source_polynomial = runtime.bridge.to_value(source.term)
        if source_polynomial is None:
            return DerivativeResult(
                OperationStatus.UNSUPPORTED,
                None,
                None,
                None,
                "the source is outside the polynomial fragment",
            )
        candidate_term = runtime.bridge.to_term(
            runtime.differential.deriv(source_polynomial)
        )
        if candidate_term is None:
            return DerivativeResult(
                OperationStatus.INVALID,
                None,
                None,
                None,
                "the derivative cannot be rendered in this language",
            )

        variable_reference = T.symbol(variable, runtime.table.name_of(variable))
        specification_term = has_derivative(
            runtime.vocabulary,
            T.TRUE,
            source.term,
            variable_reference,
            candidate_term,
        )
        issued = elaborate.proposition(
            specification_term,
            runtime.frames,
            source.frame,
            runtime.signature,
        )
        if not isinstance(issued, Pr.Proposition):
            return DerivativeResult(
                OperationStatus.INVALID,
                None,
                None,
                None,
                "the derivative specification is not a proposition",
            )

        candidate = Candidate(
            CandidateId(self._candidate_ids.issue()),
            ProblemSpec(
                operation="differentiate",
                inputs=(source.term,),
                target=variable,
                target_sort=S.REAL,
                region=None,
                result_language=ResultLanguage.EXPRESSION,
                parameter_mode=runtime.request.parameter_mode,
                coverage=Coverage.ONE_VERIFIED,
            ),
            candidate_term,
            source.frame,
        )
        self._candidates[candidate.id] = candidate

        outcome = commit(
            runtime.store,
            CommitProposal(
                source.frame,
                (issued,),
                runtime.checker.id,
                certificate=DerivativeCertificate(
                    T.TRUE, source.term, variable, candidate_term
                ),
            ),
        )
        judgment: JudgmentId | None = None
        if isinstance(outcome, Committed):
            status = OperationStatus.VERIFIED
            judgment = outcome.judgments[0]
            detail = ""
        elif isinstance(outcome, Rejected):
            status = (
                OperationStatus.REFUTED
                if outcome.refutation is not None
                else OperationStatus.INVALID
            )
            detail = outcome.detail
        elif isinstance(outcome, Deferred):
            status = OperationStatus.UNSUPPORTED
            detail = outcome.detail
        else:
            raise RuntimeError(f"unknown commit result: {type(outcome).__name__}")

        result: Expression | None = None
        if status is OperationStatus.VERIFIED:
            result = self._record_expression(
                candidate_term, f"d/dx {source.label or source.id}"
            )
        link = VerificationLink(
            candidate.id, issued, judgment, status, detail
        )
        event = self._record_event(
            "Differentiate",
            objects=() if result is None else (result.version,),
            candidates=(candidate.id,),
            judgments=() if judgment is None else (judgment,),
            note=detail,
        )
        self._append_revision(f"differentiate {source.id}", event, (link,))
        return DerivativeResult(status, candidate, link, result, detail)

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
    ) -> Revision:
        current = self.revision
        revision = Revision(
            RevisionId(len(self._revisions)),
            current.frame,
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
