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
    BasisRef,
    Blocked,
    Conditional,
    ConsistentForFragment,
    Discharge,
    FrameConsistency,
    Inconsistent,
    InferenceRecord,
    Judgment,
    Obligation,
    OutOfScope,
    Unassessed,
)
from cas.language.propositions import Proposition
from cas.language.signatures import StructuralHead
from cas.semantics.frames import FrameStore
from cas.syntax import term as T


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
        "_consistency",
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
        self._consistency: dict[FrameId, FrameConsistency] = {}
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

    def _publish(
        self,
        *,
        obligations: tuple[Obligation, ...] = (),
        judgments: tuple[Judgment, ...] = (),
        inferences: tuple[InferenceRecord, ...] = (),
        discharges: tuple[Discharge, ...] = (),
    ) -> None:
        """Insert one validated batch, or nothing.

        This is the only insertion point; it is called by `commit` and
        `discharge`, never by a frontend. Duplicate ids and dangling references
        are refused before any insertion, and every stored proposition must be
        readable in the frame that stores it. After validation, insertion cannot
        fail.
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
        pending_obligations = {record.id: record for record in obligations}
        pending_judgments = {record.id: record for record in judgments}
        pending_inferences = {record.id: record for record in inferences}
        obligation_ids = set(self._obligations) | set(pending_obligations)
        judgment_ids = set(self._judgments) | set(pending_judgments)

        def obligation_of(identifier: ObligationId) -> Obligation | None:
            return pending_obligations.get(identifier) or self._obligations.get(
                identifier
            )

        def judgment_of(identifier: JudgmentId) -> Judgment | None:
            return pending_judgments.get(identifier) or self._judgments.get(
                identifier
            )

        def inference_of(identifier: InferenceId) -> InferenceRecord | None:
            return pending_inferences.get(identifier) or self._inferences.get(
                identifier
            )

        for inference in inferences:
            self._require_frame(inference.frame)
            for premise in inference.premises:
                if premise not in judgment_ids:
                    raise KernelError(f"premise does not exist: {premise!r}")
            for conclusion in inference.conclusions:
                if conclusion not in judgment_ids:
                    raise KernelError(
                        f"conclusion does not exist: {conclusion!r}"
                    )
                known = judgment_of(conclusion)
                if known is None or known.inference != inference.id:
                    raise KernelError(
                        "an inference and its judgment disagree about support"
                    )
        for obligation in obligations:
            self._require_frame(obligation.frame)
            introducer = inference_of(obligation.introduced_by)
            if introducer is None:
                raise KernelError(
                    f"introducing inference does not exist: "
                    f"{obligation.introduced_by!r}"
                )
            if introducer.frame != obligation.frame:
                raise KernelError(
                    "an obligation is stored outside its inference frame"
                )
            if not self.frames.is_visible(
                obligation.proposition.meaning.frame, obligation.frame
            ):
                raise KernelError(
                    "an obligation proposition is not readable in its frame"
                )
            escaped = self.frames.escapes(
                obligation.frame, obligation.proposition.term
            )
            if escaped:
                raise KernelError(
                    "an obligation proposition contains a symbol outside "
                    "its frame"
                )
        for judgment in judgments:
            self._require_frame(judgment.frame)
            owner = inference_of(judgment.inference)
            if owner is None:
                raise KernelError(
                    f"inference does not exist: {judgment.inference!r}"
                )
            if owner.frame != judgment.frame:
                raise KernelError(
                    "a judgment is stored outside its inference frame"
                )
            if judgment.id not in owner.conclusions:
                raise KernelError(
                    "an inference does not list its own judgment"
                )
            for obligation_id in judgment.obligations:
                if obligation_id not in obligation_ids:
                    raise KernelError(
                        f"obligation does not exist: {obligation_id!r}"
                    )
            if not self.frames.is_visible(
                judgment.proposition.meaning.frame, judgment.frame
            ):
                raise KernelError(
                    "a judgment proposition is not readable in its frame"
                )
            escaped = self.frames.escapes(
                judgment.frame, judgment.proposition.term
            )
            if escaped:
                raise KernelError(
                    "a judgment proposition contains a symbol outside "
                    "its frame"
                )
        seen_discharges: set[tuple[ObligationId, JudgmentId, FrameId]] = set()
        for discharge in discharges:
            self._require_frame(discharge.frame)
            key = (
                discharge.obligation,
                discharge.by_judgment,
                discharge.frame,
            )
            if key in seen_discharges:
                raise KernelError("a publication repeats a discharge")
            seen_discharges.add(key)
            if any(
                known.by_judgment == discharge.by_judgment
                and known.frame == discharge.frame
                for known in self._discharges.get(discharge.obligation, ())
            ):
                raise KernelError("this discharge is already recorded")
            target = obligation_of(discharge.obligation)
            proof = judgment_of(discharge.by_judgment)
            if target is None:
                raise KernelError(
                    f"obligation does not exist: {discharge.obligation!r}"
                )
            if proof is None:
                raise KernelError(
                    f"judgment does not exist: {discharge.by_judgment!r}"
                )
            if proof.proposition != target.proposition:
                raise KernelError("the discharge proof states another proposition")
            if not self.frames.is_visible(proof.frame, discharge.frame):
                raise KernelError("the discharge proof is outside its frame")
            if not self.frames.is_visible(target.frame, discharge.frame):
                raise KernelError("the discharged obligation is outside its frame")
        for obligation in obligations:
            self._obligations[obligation.id] = obligation
        for judgment in judgments:
            self._judgments[judgment.id] = judgment
        for inference in inferences:
            self._inferences[inference.id] = inference
        for discharge in discharges:
            self._discharges.setdefault(discharge.obligation, []).append(discharge)

    def _require_frame(self, identifier: FrameId) -> None:
        try:
            self.frames.get(identifier)
        except KeyError:
            raise KernelError(f"frame does not exist: {identifier!r}") from None

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

    def judgments_visible(self, frame: FrameId) -> tuple[Judgment, ...]:
        """Every issued judgment whose frame is visible from `frame`."""
        return tuple(
            judgment
            for judgment in self._judgments.values()
            if self.frames.is_visible(judgment.frame, frame)
        )

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

    def find_obligation(
        self, proposition: Proposition, frame: FrameId
    ) -> ObligationId | None:
        """An existing obligation with the same proposition in `frame`.

        Propositions carry their meaning environment, so exact equality is the
        semantic identity key for the current immutable-frame model.
        """
        for obligation in self._obligations.values():
            if (
                obligation.frame == frame
                and obligation.proposition == proposition
            ):
                return obligation.id
        return None

    def is_discharged(self, obligation: ObligationId, frame: FrameId) -> bool:
        """Whether a discharge performed in `frame` or an ancestor is visible."""
        return any(
            self.frames.is_visible(discharge.frame, frame)
            for discharge in self._discharges.get(obligation, ())
        )

    def _is_closed(self, judgment: Judgment, frame: FrameId) -> bool:
        """Whether every obligation is discharged, without refutation checks.

        Applicability needs a non-recursive closure test: refutation lookups
        themselves ask which visible judgments are closed.
        """
        return all(
            self.is_discharged(obligation, frame)
            for obligation in judgment.obligations
        )

    def refutation_of(
        self, proposition: Proposition, frame: FrameId
    ) -> JudgmentId | None:
        """A closed visible judgment that states the negation of `proposition`.

        The comparison is structural because frames only extend along a chain:
        every visible frame resolves the same stable symbol ids. A conditional
        judgment is not a refutation; only a closed one is used.
        """
        if not self.frames.is_visible(proposition.meaning.frame, frame):
            return None
        not_symbol = self.frames.world.language.symbol_of(StructuralHead.NOT)
        if not_symbol is None:
            return None
        head = T.symbol(not_symbol, StructuralHead.NOT.value)

        def negates(outer: T.Term, inner: T.Term) -> bool:
            return (
                isinstance(outer, T.Apply)
                and outer.operator == head
                and len(outer.arguments) == 1
                and outer.arguments[0] == inner
            )

        for judgment in self.judgments_visible(frame):
            if not self._is_closed(judgment, frame):
                continue
            if negates(
                judgment.proposition.term, proposition.term
            ) or negates(proposition.term, judgment.proposition.term):
                return judgment.id
        return None

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
        if not pending:
            return Applicable()
        refuted: list[ObligationId] = []
        unresolved: list[ObligationId] = []
        witnesses: list[JudgmentId] = []
        for obligation_id in pending:
            obligation = self._obligations[obligation_id]
            witness = self.refutation_of(obligation.proposition, frame)
            if witness is None:
                unresolved.append(obligation_id)
            else:
                refuted.append(obligation_id)
                if witness not in witnesses:
                    witnesses.append(witness)
        if refuted:
            return Blocked(tuple(refuted), tuple(unresolved), tuple(witnesses))
        return Conditional(tuple(unresolved))

    # --- frame consistency ---

    def consistency(self, frame: FrameId) -> FrameConsistency:
        """The recorded state, with inconsistency inherited from ancestors.

        A fragment claim is not inherited: extending a frame can add a
        hypothesis that invalidates it. Inconsistency is inherited because a
        closed contradiction remains a contradiction in every descendant.
        """
        self._require_frame(frame)
        for ancestor in self.frames.chain(frame):
            state = self._consistency.get(ancestor.id)
            if isinstance(state, Inconsistent):
                return state
        return self._consistency.get(frame, Unassessed())

    def record_inconsistency(
        self, frame: FrameId, witness: JudgmentId
    ) -> Inconsistent:
        """Record a closed false judgment as the contradiction witness."""
        self._require_frame(frame)
        try:
            proof = self._judgments[witness]
        except KeyError:
            raise KernelError(f"judgment does not exist: {witness!r}") from None
        if not self.frames.is_visible(proof.frame, frame):
            raise KernelError("the contradiction proof is outside the frame")
        if proof.proposition.term != T.FALSE:
            raise KernelError("a contradiction proof must state false")
        if not self._is_closed(proof, frame):
            raise KernelError(
                "the contradiction proof still has open conditions"
            )
        existing = self._consistency.get(frame)
        if isinstance(existing, Inconsistent):
            return existing
        state = Inconsistent(witness, "the frame proves false")
        self._consistency[frame] = state
        return state

    def record_consistency_claim(
        self,
        frame: FrameId,
        fragment: str,
        *,
        evidence: tuple[JudgmentId, ...] = (),
        basis: tuple[BasisRef, ...] = (),
    ) -> ConsistentForFragment:
        """Record an explicit, evidence-bearing consistency claim.

        The kernel checks that the evidence exists, is visible and is closed.
        It does not turn the claim into a general consistency theorem.
        """
        self._require_frame(frame)
        if isinstance(self.consistency(frame), Inconsistent):
            raise KernelError(
                "an inconsistent frame cannot be declared consistent"
            )
        for identifier in evidence:
            try:
                judgment = self._judgments[identifier]
            except KeyError:
                raise KernelError(
                    f"judgment does not exist: {identifier!r}"
                ) from None
            if not self.frames.is_visible(judgment.frame, frame):
                raise KernelError("consistency evidence is outside the frame")
            if not self._is_closed(judgment, frame):
                raise KernelError(
                    "consistency evidence still has open conditions"
                )
        for reference in basis:
            if reference.world != self.frames.world.id:
                raise KernelError(
                    "a basis reference belongs to another world"
                )
        state = ConsistentForFragment(fragment, evidence, basis)
        self._consistency[frame] = state
        return state

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
