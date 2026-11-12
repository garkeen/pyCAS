"""Frame consistency: the core contradiction rule and its assessment.

A frame is `Inconsistent` only when a closed judgment of `false` was issued in
it. This module supplies the smallest rule that can produce one: visible
hypotheses are read in the submission frame (ancestor hypotheses weaken into
descendants), and a complementary pair yields `false`.

The rule is deliberately narrow. It does not attempt general logical
satisfiability, it does not evaluate arithmetic, and finding no complementary
pair leaves the frame `Unassessed` rather than declaring it consistent.
"""

from __future__ import annotations

from cas.foundation.ids import FrameId
from cas.kernel.commit import (
    CommitProposal,
    ValidatedCommitBatch,
    publish_commit,
    validate_commit,
)
from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    Unverified,
    Verified,
)
from cas.kernel.model import FrameConsistency, Inconsistent
from cas.kernel.store import KernelStore
from cas.language import propositions as Pr
from cas.language.decisions import Reason
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics.conditions import condition_truth
from cas.semantics.frames import FrameSorts, FrameStore
from cas.syntax import term as T


class ContradictionChecker:
    """`Gamma, H, not H |- false` over hypotheses visible in one frame.

    Only `false` is verified. The rule reads ancestor hypotheses in the
    submission frame, which is the scope-weakening step of §6.3; it does not
    claim that propositions from sibling frames agree.
    """

    id = "kernel.contradiction"
    version = "1"

    def __init__(
        self, frames: FrameStore, signature: LanguageSignature
    ) -> None:
        self._frames = frames
        self._signature = signature

    def check(self, request: CheckRequest) -> CheckOutcome:
        if any(conclusion.term != T.FALSE for conclusion in request.conclusions):
            return Unverified(
                Reason.FRAGMENT,
                "the contradiction rule proves false only",
            )
        propositions = self._frames.assumptions(request.frame)
        environment = FrameSorts(self._frames, request.frame)
        if any(
            condition_truth(
                proposition.term, self._signature, environment
            )
            is False
            for proposition in propositions
        ):
            return Verified(tuple(request.conclusions))
        if self._signature.symbol_of(StructuralHead.NOT) is None:
            return Unverified(
                Reason.FRAGMENT,
                "the language has no negation symbol",
            )
        for left in propositions:
            for right in propositions:
                if not self._frames.agree_in(request.frame, left, right):
                    continue
                if Pr.negates(
                    left.term, right.term, self._signature
                ) or Pr.negates(
                    right.term, left.term, self._signature
                ):
                    return Verified(tuple(request.conclusions))
        return Unverified(
            Reason.GUARDED,
            "the visible assumptions are not a complementary pair",
        )


def assess_consistency(
    store: KernelStore,
    frame: FrameId,
    *,
    checker_id: str = ContradictionChecker.id,
) -> FrameConsistency:
    """Try to close a contradiction in `frame`.

    Success publishes `false` and records `Inconsistent`. Failure to find a
    contradiction, an unavailable checker or an open result all leave the frame
    at its previous state; none of them is evidence of consistency.
    """
    current = store.consistency(frame)
    if isinstance(current, Inconsistent):
        return current
    false_proposition = Pr.check(
        T.FALSE,
        store.frames.world.language,
        FrameSorts(store.frames, frame),
        store.frames.get(frame).meaning,
    )
    if not isinstance(false_proposition, Pr.Proposition):
        return current
    validated = validate_commit(
        store,
        CommitProposal(
            frame,
            (false_proposition,),
            checker_id,
            "consistency",
            "Contradiction",
            certificate=None,
        ),
    )
    if not isinstance(validated, ValidatedCommitBatch):
        return store.consistency(frame)
    outcome = publish_commit(store, validated)
    return store.record_inconsistency(frame, outcome.judgments[0])


__all__ = ["ContradictionChecker", "assess_consistency"]
