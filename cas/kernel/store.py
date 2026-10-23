"""The trusted ledger.

All writes go through `publish`, which validates the whole batch before touching
a dictionary. There are no reverse indexes to repair and no half-inserted state:
a batch either passes validation and is inserted, or nothing is inserted.

This is atomicity for one synchronous writer, which is the current model. A
concurrent or persisted ledger needs a real transaction, and the interface is
shaped so that `publish` is the only place to implement it.
"""

from __future__ import annotations

from collections.abc import Hashable, Mapping, Sequence
from typing import TypeVar

from cas.foundation.ids import (
    FrameId,
    IdIssuer,
    InferenceId,
    JudgmentId,
    ObligationId,
)
from cas.kernel.evidence import CheckerRegistry
from cas.kernel.model import (
    Applicability,
    Applicable,
    Conditional,
    Discharge,
    InferenceRecord,
    Judgment,
    Obligation,
    OutOfScope,
)
from cas.semantics.frames import FrameStore


class KernelError(Exception):
    """A request violates a kernel invariant."""


Id = TypeVar("Id", bound=Hashable)
Record = TypeVar("Record")


class KernelStore:
    """Committed records, the single write site, and applicability queries."""

    __slots__ = (
        "_obligations",
        "_judgments",
        "_inferences",
        "_discharges",
        "_obligation_issuer",
        "_judgment_issuer",
        "_inference_issuer",
        "frames",
        "checkers",
    )

    def __init__(self, frames: FrameStore, checkers: CheckerRegistry) -> None:
        self.frames = frames
        self.checkers = checkers
        self._obligations: dict[ObligationId, Obligation] = {}
        self._judgments: dict[JudgmentId, Judgment] = {}
        self._inferences: dict[InferenceId, InferenceRecord] = {}
        self._discharges: dict[ObligationId, list[Discharge]] = {}
        self._obligation_issuer = IdIssuer()
        self._judgment_issuer = IdIssuer()
        self._inference_issuer = IdIssuer()

    # --- ids ---

    def new_obligation_id(self) -> ObligationId:
        return ObligationId(self._obligation_issuer.issue())

    def new_judgment_id(self) -> JudgmentId:
        return JudgmentId(self._judgment_issuer.issue())

    def new_inference_id(self) -> InferenceId:
        return InferenceId(self._inference_issuer.issue())

    # --- the single write site ---

    def publish(
        self,
        *,
        obligations: tuple[Obligation, ...] = (),
        judgments: tuple[Judgment, ...] = (),
        inferences: tuple[InferenceRecord, ...] = (),
        discharges: tuple[Discharge, ...] = (),
    ) -> None:
        """Insert one validated batch, or nothing.

        Duplicate ids inside the batch and ids already in the ledger are refused
        before any insertion; after that, insertion cannot fail.
        """
        self._reject_duplicates(
            "obligation", [record.id for record in obligations], self._obligations
        )
        self._reject_duplicates(
            "judgment", [record.id for record in judgments], self._judgments
        )
        self._reject_duplicates(
            "inference", [record.id for record in inferences], self._inferences
        )
        for obligation in obligations:
            self._obligations[obligation.id] = obligation
        for judgment in judgments:
            self._judgments[judgment.id] = judgment
        for inference in inferences:
            self._inferences[inference.id] = inference
        for discharge in discharges:
            self._discharges.setdefault(discharge.obligation, []).append(discharge)

    @staticmethod
    def _reject_duplicates(
        kind: str,
        identifiers: Sequence[Id],
        existing: Mapping[Id, Record],
    ) -> None:
        if len(set(identifiers)) != len(identifiers):
            raise KernelError(f"a publication repeats a {kind} id")
        for identifier in identifiers:
            if identifier in existing:
                raise KernelError(f"{kind} id already issued: {identifier!r}")

    # --- queries ---

    def get_obligation(self, identifier: ObligationId) -> Obligation:
        return self._obligations[identifier]

    def get_judgment(self, identifier: JudgmentId) -> Judgment:
        return self._judgments[identifier]

    def get_inference(self, identifier: InferenceId) -> InferenceRecord:
        return self._inferences[identifier]

    def inference_of(self, judgment: JudgmentId) -> InferenceRecord:
        return self._inferences[self._judgments[judgment].inference]

    def support(self, judgment: JudgmentId) -> frozenset[JudgmentId]:
        """Every premise reached transitively, excluding the judgment itself."""
        seen: set[JudgmentId] = set()
        stack = list(self.inference_of(judgment).premises)
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            stack.extend(self.inference_of(current).premises)
        return frozenset(seen)

    def is_discharged(self, obligation: ObligationId, frame: FrameId) -> bool:
        """Whether a discharge performed in `frame` or an ancestor is visible."""
        return any(
            self.frames.is_visible(discharge.frame, frame)
            for discharge in self._discharges.get(obligation, ())
        )

    def applicability(
        self, judgment: JudgmentId, frame: FrameId
    ) -> Applicability:
        """Whether the judgment can be used in `frame`."""
        record = self._judgments[judgment]
        if not self.frames.is_visible(record.frame, frame):
            return OutOfScope(record.frame, frame)
        pending = tuple(
            obligation
            for obligation in record.obligations
            if not self.is_discharged(obligation, frame)
        )
        return Conditional(pending) if pending else Applicable()

    # --- discharge (an explicit kernel operation) ---

    def discharge(
        self,
        obligation: ObligationId,
        by_judgment: JudgmentId,
        frame: FrameId,
    ) -> Discharge:
        """Record that `by_judgment` proves `obligation`, checked for cycles.

        The proof must state exactly the obligation's proposition, be visible in
        `frame`, and not itself depend — directly or transitively — on any
        judgment that carries this obligation.
        """
        target = self._obligations.get(obligation)
        if target is None:
            raise KernelError(f"obligation does not exist: {obligation!r}")
        proof = self._judgments.get(by_judgment)
        if proof is None:
            raise KernelError(f"judgment does not exist: {by_judgment!r}")
        if proof.proposition != target.proposition:
            raise KernelError("the proof states a different proposition")
        if not self.frames.is_visible(proof.frame, frame):
            raise KernelError("the proof is outside the discharge frame")
        if not self.frames.is_visible(target.frame, frame):
            raise KernelError("the obligation is outside the discharge frame")
        for used in self.support(by_judgment) | {by_judgment}:
            if obligation in self._judgments[used].obligations:
                raise KernelError(
                    "cyclic discharge: the proof depends on the obligation"
                )
        for known in self._discharges.get(obligation, ()):
            if known.by_judgment == by_judgment and known.frame == frame:
                raise KernelError("this discharge is already recorded")
        discharge = Discharge(obligation, by_judgment, frame)
        self.publish(discharges=(discharge,))
        return discharge

    # --- size ---

    def stats(self) -> dict[str, int]:
        return {
            "frames": self.frames.count(),
            "obligations": len(self._obligations),
            "judgments": len(self._judgments),
            "inferences": len(self._inferences),
            "discharges": sum(len(items) for items in self._discharges.values()),
        }


__all__ = ["KernelError", "KernelStore"]
