"""Condition checking and applicability resolution.

`ConditionChecker` proves a condition from supplied premise judgments using the
restricted condition implication service. It reports only premises that are
actually needed, so the kernel does not inherit support that the proof did not
use.

`resolve_applicability` is the resolver side of §14.6: it inspects a judgment's
open obligations, tries to prove each one from visible unconditional judgments,
commits the proof, and records a discharge. It never turns an undecided
condition into `Applicable`; unresolved conditions remain `Conditional`.
"""

from __future__ import annotations

from collections.abc import Iterable

from cas.foundation.ids import FrameId, JudgmentId
from cas.kernel.commit import CommitProposal, Committed, commit
from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    Unverified,
    Verified,
)
from cas.kernel.model import Applicability, Conditional, OutOfScope
from cas.kernel.store import KernelStore
from cas.language.decisions import Reason
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature
from cas.semantics.conditions import and_all, implies


class ConditionChecker:
    """Prove a condition from premise judgments by restricted implication."""

    id = "logic.condition"
    version = "1"

    def __init__(self, signature: LanguageSignature) -> None:
        self._signature = signature

    def check(self, request: CheckRequest) -> CheckOutcome:
        used: set[int] = set()
        for conclusion in request.conclusions:
            indices = self._needed(request.premises, conclusion)
            if indices is None:
                return Unverified(
                    Reason.GUARDED,
                    "the condition is not entailed by the supplied premises",
                )
            used.update(indices)
        return Verified(
            tuple(request.conclusions),
            used_premises=tuple(sorted(used)),
        )

    def _needed(
        self,
        premises: tuple[Proposition, ...],
        conclusion: Proposition,
    ) -> list[int] | None:
        if not self._entails(premises, range(len(premises)), conclusion):
            return None
        kept = list(range(len(premises)))
        for index in list(kept):
            trial = [position for position in kept if position != index]
            if self._entails(premises, trial, conclusion):
                kept = trial
        return kept

    def _entails(
        self,
        premises: tuple[Proposition, ...],
        indices: Iterable[int],
        conclusion: Proposition,
    ) -> bool:
        assumption = and_all(
            self._signature,
            *(premises[index].term for index in indices),
        )
        return implies(
            assumption, conclusion.term, self._signature
        ) is True


def resolve_applicability(
    store: KernelStore,
    judgment: JudgmentId,
    frame: FrameId,
    *,
    checker_id: str = ConditionChecker.id,
    premise_limit: int = 64,
) -> Applicability:
    """Try to discharge every open obligation of `judgment` in `frame`.

    Each successful step publishes the proof and its discharge in one atomic
    commit batch. If a proof or discharge cannot be completed, the obligation
    stays open and the result is `Conditional`.
    """
    target = store.get_judgment(judgment)
    if not store.frames.is_visible(target.frame, frame):
        return OutOfScope(target.frame, frame)
    current = store.applicability(judgment, frame)
    if not current.is_conditional():
        return current
    assert isinstance(current, Conditional)

    forbidden = {judgment}
    for obligation_id in current.obligations:
        if store.is_discharged(obligation_id, frame):
            continue
        candidates = _candidates(store, frame, forbidden, premise_limit)
        if candidates is None:
            continue
        obligation = store.get_obligation(obligation_id)
        outcome = commit(
            store,
            CommitProposal(
                frame,
                (obligation.proposition,),
                checker_id,
                "discharge",
                "Condition",
                premises=candidates,
                discharge_obligations=(obligation_id,),
            ),
        )
        if not isinstance(outcome, Committed):
            continue

    return store.applicability(judgment, frame)


def _candidates(
    store: KernelStore,
    frame: FrameId,
    forbidden: frozenset[JudgmentId] | set[JudgmentId],
    limit: int,
) -> tuple[JudgmentId, ...] | None:
    out: list[JudgmentId] = []
    for candidate in store.judgments_visible(frame):
        if candidate.id in forbidden:
            continue
        if not store.applicability(candidate.id, frame).is_applicable():
            continue
        if len(out) >= limit:
            return None
        out.append(candidate.id)
    return tuple(out)


__all__ = ["ConditionChecker", "resolve_applicability"]
