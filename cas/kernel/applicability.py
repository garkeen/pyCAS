"""Applicability resolution: try to discharge a judgment's open obligations.

`resolve_applicability` is the resolver side of §14.6. It inspects a judgment's
open obligations, offers visible unconditional judgments to the registered
condition checker, commits the proof, and records a discharge. It never turns
an undecided condition into `Applicable`; unresolved conditions remain
`Conditional`. The checker itself lives in `condition_checker.py`.
"""

from __future__ import annotations

from cas.foundation.ids import FrameId, JudgmentId
from cas.kernel.commit import CommitProposal, Committed, commit
from cas.kernel.condition_checker import ConditionChecker
from cas.kernel.model import Applicability, Conditional, OutOfScope
from cas.kernel.store import KernelStore


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


__all__ = ["resolve_applicability"]
