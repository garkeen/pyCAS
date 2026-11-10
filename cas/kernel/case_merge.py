"""Case-analysis merge for two complementary branch judgments.

If a frame `F` has two direct child frames `F+P` and `F+not P`, and each child
contains a closed judgment of the same formula `Q`, then `Q` follows in `F`.
This is the kernel-side rule; the workspace records the resulting judgment.

The checker rejects a branch whose conclusion is itself assumed there: assuming
`Q` in both branches would prove nothing.  Branch obligations must be discharged
in their own frames; otherwise the conclusion would be conditional and is not
issued unconditionally.  The caller must supply the two branch judgment
propositions as premises; the checker verifies their terms and meaning frames
and records both as the support of the merged conclusion.

A kernel-built request carries a `SupportsService`, which the checker uses to
read the two branch judgments and their discharge state.  The late-bound
`JudgmentLookup` remains only for direct tests that construct a request without
a verification context.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING

from cas.foundation.ids import FrameId, JudgmentId, ObligationId
from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    InvalidEvidence,
    Unverified,
    Verified,
)
from cas.language.decisions import Reason
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics.frames import FrameStore
from cas.syntax import term as T

if TYPE_CHECKING:
    from cas.kernel.store import KernelStore


class JudgmentLookup:
    """Late-bound access to the kernel store for the case-merge checker.

    The checker is registered while the store is being assembled; the store is
    bound immediately after construction.  This is assembly wiring, not global
    state.
    """

    __slots__ = ("_store",)

    def __init__(self) -> None:
        self._store: KernelStore | None = None

    def bind(self, store: KernelStore) -> None:
        if self._store is not None:
            raise ValueError("the judgment lookup is already bound")
        self._store = store

    @property
    def store(self) -> KernelStore:
        if self._store is None:
            raise RuntimeError("the judgment lookup is not bound")
        return self._store


@dataclass(frozen=True, slots=True)
class CaseMergeCertificate:
    """The two branch judgments and the complementary frames they live in."""

    assumption: Proposition
    positive_frame: FrameId
    negative_frame: FrameId
    positive_judgment: JudgmentId
    negative_judgment: JudgmentId

    def __post_init__(self) -> None:
        if not isinstance(self.assumption, Proposition):
            raise TypeError("a case merge needs an assumption proposition")
        if self.positive_frame == self.negative_frame:
            raise ValueError("a case merge needs two distinct frames")


class CaseMergeChecker:
    """The independent case-analysis rule for two complementary branches."""

    id = "kernel.case_merge"
    version = "1"
    # Branch judgments live in child frames, which are not visible from the
    # submission frame.  The kernel admits this checker to receive them as
    # premises; the checker itself proves the branch relation.
    accepts_cross_frame_premises = True

    def __init__(
        self,
        frames: FrameStore,
        signature: LanguageSignature,
        lookup: JudgmentLookup,
    ) -> None:
        self._frames = frames
        self._signature = signature
        self._lookup = lookup

    def check(self, request: CheckRequest) -> CheckOutcome:
        if len(request.conclusions) != 1:
            return InvalidEvidence(
                "a case merge issues exactly one conclusion"
            )
        conclusion = request.conclusions[0]
        certificate = request.certificate
        if not isinstance(certificate, CaseMergeCertificate):
            return InvalidEvidence("a case-merge certificate is required")
        base = request.frame
        try:
            positive_frame = self._frames.get(certificate.positive_frame)
            negative_frame = self._frames.get(certificate.negative_frame)
        except KeyError:
            return InvalidEvidence("a case branch frame does not exist")
        if positive_frame.parent != base or negative_frame.parent != base:
            return InvalidEvidence(
                "the case branch frames are not direct children of the "
                "submission frame"
            )
        if (
            positive_frame.declarations
            or positive_frame.definitions
            or len(positive_frame.hypotheses) != 1
        ):
            return InvalidEvidence(
                "the positive branch is not a pure hypothesis extension"
            )
        if (
            negative_frame.declarations
            or negative_frame.definitions
            or len(negative_frame.hypotheses) != 1
        ):
            return InvalidEvidence(
                "the negative branch is not a pure hypothesis extension"
            )
        if (
            positive_frame.hypotheses[0].proposition.term
            != certificate.assumption.term
        ):
            return InvalidEvidence(
                "the positive branch does not assume the stated case"
            )
        negated = T.app(
            self._signature.head_term(StructuralHead.NOT),
            certificate.assumption.term,
        )
        if negative_frame.hypotheses[0].proposition.term != negated:
            return InvalidEvidence(
                "the negative branch does not assume the negated case"
            )
        if not self._frames.readable(conclusion, base):
            return InvalidEvidence(
                "the conclusion is not readable in the case base frame"
            )
        context = request.context
        is_discharged: Callable[[ObligationId, FrameId], bool]
        if context is None:
            store = self._lookup.store
            try:
                positive = store.get_judgment(certificate.positive_judgment)
                negative = store.get_judgment(certificate.negative_judgment)
            except KeyError:
                return InvalidEvidence("a branch judgment does not exist")
            is_discharged = store.is_discharged
        else:
            supports = context.supports
            if supports is None:
                return InvalidEvidence(
                    "the verification context has no support service"
                )
            try:
                positive = supports.judgment(
                    certificate.positive_judgment
                )
                negative = supports.judgment(
                    certificate.negative_judgment
                )
            except KeyError:
                return InvalidEvidence("a branch judgment does not exist")
            is_discharged = supports.is_discharged
        if (
            positive.frame != positive_frame.id
            or negative.frame != negative_frame.id
        ):
            return InvalidEvidence(
                "a branch judgment is not in the stated branch frame"
            )
        if (
            positive.proposition.term != conclusion.term
            or negative.proposition.term != conclusion.term
        ):
            return InvalidEvidence(
                "the branch judgments do not state the requested conclusion"
            )
        expected_premises = (positive.proposition, negative.proposition)
        supplied_premises = request.premises
        if len(supplied_premises) != 2 or (
            supplied_premises != expected_premises
            and supplied_premises
            != (expected_premises[1], expected_premises[0])
        ):
            return InvalidEvidence(
                "a case merge must be supplied exactly the two branch "
                "judgment premises, with the same terms and frames"
            )
        for frame in (positive_frame.id, negative_frame.id):
            if any(
                assumption.term == conclusion.term
                for assumption in self._frames.assumptions(frame)
            ):
                return Unverified(
                    Reason.GUARDED,
                    "the conclusion is assumed in a branch",
                )
        for judgment in (positive, negative):
            if any(
                not is_discharged(obligation, judgment.frame)
                for obligation in judgment.obligations
            ):
                return Unverified(
                    Reason.GUARDED,
                    "a branch judgment still has open conditions",
                )
        return Verified((conclusion,), used_premises=(0, 1))


__all__ = [
    "CaseMergeCertificate",
    "CaseMergeChecker",
    "JudgmentLookup",
]
