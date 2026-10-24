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

from collections.abc import Mapping
from fractions import Fraction
from typing import TYPE_CHECKING, Any

from cas.algebra.polynomial import Polynomial
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
from cas.semantics.specialization import (
    Applied,
    GenericResult,
    InvalidSpecialization,
    NeedsRecomputation,
    OutsideValidity,
    Specialization,
)
from cas.semantics.specialization import (
    specialize as specialize_family,
)
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.workflow.records import (
    Candidate,
    DerivativeResult,
    Event,
    Expression,
    OperationStatus,
    Revision,
    SpecializationPath,
    SpecializationResult,
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

        generic: GenericResult | None = None
        if runtime.request.parameters:
            valid_on = elaborate.proposition(
                T.TRUE,
                runtime.frames,
                source.frame,
                runtime.signature,
            )
            if not isinstance(valid_on, Pr.Proposition):
                return DerivativeResult(
                    OperationStatus.INVALID,
                    None,
                    None,
                    None,
                    "the parameter validity region is not a proposition",
                )
            generic = GenericResult.assemble(
                result=candidate_term,
                valid_on=valid_on,
                excluded_cases=(),
                correctness_specification=issued,
                parameter_mode=runtime.request.parameter_mode,
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
            if generic is not None:
                self._generic_results[source.version] = generic
        else:
            generic = None
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
        return DerivativeResult(
            status, candidate, link, result, detail, generic
        )

    def generic_result(self, source: Expression) -> GenericResult | None:
        """The verified parameter-family result associated with `source`."""
        return self._generic_results.get(source.version)

    def specialize(
        self,
        source: Expression,
        values: Mapping[SymbolId, Fraction],
        *,
        generic: GenericResult | None = None,
    ) -> SpecializationResult:
        """Apply an exact parameter point to a verified parameter family.

        The recorded family is used by default. A caller may pass the family
        explicitly; it only chooses which candidate to try, because the
        specialized instance is verified independently before publication.
        """
        runtime = self._runtime
        view = runtime.specialization
        if view is None or not runtime.request.parameters:
            return SpecializationResult(
                OperationStatus.UNSUPPORTED,
                None,
                None,
                None,
                None,
                "this runtime has no formal parameters",
            )
        if source.version not in {
            expression.version for expression in self.expressions()
        }:
            return SpecializationResult(
                OperationStatus.UNSUPPORTED,
                None,
                None,
                None,
                None,
                "the source is not visible in the current revision",
            )
        family = (
            generic
            if generic is not None
            else self._generic_results.get(source.version)
        )
        if family is None:
            return SpecializationResult(
                OperationStatus.UNSUPPORTED,
                None,
                None,
                None,
                None,
                "differentiate the source first so a verified parameter "
                "family exists",
            )
        try:
            specialization = Specialization(values)
        except (TypeError, ValueError) as error:
            return SpecializationResult(
                OperationStatus.INVALID,
                None,
                None,
                None,
                None,
                f"invalid specialization: {error}",
            )

        outcome = specialize_family(
            family,
            runtime.request,
            specialization,
            runtime.signature,
        )
        if isinstance(outcome, InvalidSpecialization):
            return SpecializationResult(
                OperationStatus.INVALID,
                None,
                None,
                None,
                None,
                outcome.detail,
            )

        mapping = {
            symbol_id: T.number(value)
            for symbol_id, value in specialization.values.items()
        }
        substituted_source = B.substitute_free(source.term, mapping)
        source_value = view.bridge.to_value(substituted_source)
        if source_value is None:
            return SpecializationResult(
                OperationStatus.UNSUPPORTED,
                None,
                None,
                None,
                None,
                "the specialized source is outside the polynomial fragment",
            )
        specialized_source = view.bridge.to_term(source_value)
        if specialized_source is None:
            return SpecializationResult(
                OperationStatus.INVALID,
                None,
                None,
                None,
                None,
                "the specialized source cannot be rendered",
            )

        path: SpecializationPath
        candidate_value: Polynomial[Fraction] | None = None
        if isinstance(outcome, Applied):
            candidate_value = view.bridge.to_value(outcome.result)
        elif not isinstance(outcome, (NeedsRecomputation, OutsideValidity)):
            raise RuntimeError(
                f"unknown specialization outcome: {type(outcome).__name__}"
            )
        if candidate_value is None:
            candidate_value = view.differential.deriv(source_value)
            path = SpecializationPath.RECOMPUTED
        else:
            path = SpecializationPath.GENERIC_FORMULA
        rendered = view.bridge.to_term(candidate_value)
        if rendered is None:
            return SpecializationResult(
                OperationStatus.INVALID,
                None,
                None,
                None,
                None,
                "the specialized derivative cannot be rendered",
            )
        candidate_term = rendered

        variable_reference = T.symbol(
            runtime.variable, runtime.table.name_of(runtime.variable)
        )
        specification_term = has_derivative(
            runtime.vocabulary,
            T.TRUE,
            specialized_source,
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
            return SpecializationResult(
                OperationStatus.INVALID,
                None,
                None,
                None,
                None,
                "the specialized specification is not a proposition",
            )

        candidate = Candidate(
            CandidateId(self._candidate_ids.issue()),
            ProblemSpec(
                operation="specialize",
                inputs=(specialized_source,),
                target=runtime.variable,
                target_sort=S.REAL,
                region=None,
                result_language=ResultLanguage.EXPRESSION,
                parameter_mode=view.request.parameter_mode,
                coverage=Coverage.ONE_VERIFIED,
            ),
            candidate_term,
            source.frame,
        )
        self._candidates[candidate.id] = candidate

        committed = commit(
            runtime.store,
            CommitProposal(
                source.frame,
                (issued,),
                view.checker.id,
                certificate=DerivativeCertificate(
                    T.TRUE, specialized_source, runtime.variable, candidate_term
                ),
            ),
        )
        judgment: JudgmentId | None = None
        if isinstance(committed, Committed):
            status = OperationStatus.VERIFIED
            judgment = committed.judgments[0]
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
            raise RuntimeError(
                f"unknown commit result: {type(committed).__name__}"
            )

        result: Expression | None = None
        if status is OperationStatus.VERIFIED:
            result = self._record_expression(
                candidate_term, f"specialize {source.label or source.id}"
            )
        link = VerificationLink(
            candidate.id, issued, judgment, status, detail
        )
        event = self._record_event(
            "Specialize",
            objects=() if result is None else (result.version,),
            candidates=(candidate.id,),
            judgments=() if judgment is None else (judgment,),
            note=path.value,
        )
        self._append_revision(f"specialize {source.id}", event, (link,))
        return SpecializationResult(
            status, candidate, link, result, path, detail
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
