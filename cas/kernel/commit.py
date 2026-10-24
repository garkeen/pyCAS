"""The single trusted publication boundary.

`commit` turns a verified proposal into ledger records. It checks the frame, the
conclusions, the premises and the checker's report, applies one condition policy
to every open obligation — inherited or newly reported — and publishes exactly
one batch.

The kernel never decides mathematics. It ensures that whatever was verified is
exactly what was requested, that every condition is recorded, and that nothing
is written unless the whole submission passes.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import FrameId, InferenceId, JudgmentId, ObligationId
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    ObligationReport,
    Refuted,
    Unverified,
    Verified,
)
from cas.kernel.model import (
    Discharge,
    Inconsistent,
    InferenceRecord,
    Judgment,
    Obligation,
)
from cas.kernel.store import KernelStore
from cas.language.decisions import Reason
from cas.language.propositions import Proposition


class ConditionPolicy(StrEnum):
    """How open obligations are handled at the submission boundary."""

    REQUIRE_PROVED = "require_proved"
    ALLOW_CONDITIONAL = "allow_conditional"
    REQUEST_CASES = "request_cases"


@dataclass(frozen=True, slots=True)
class CommitProposal:
    """One submission.

    `conclusions` are the propositions the caller claims; `certificate` is
    interpreted only by the checker named by `checker_id`. The kernel does not
    accept an "all of it is true" flag anywhere.
    """

    frame: FrameId
    conclusions: tuple[Proposition, ...]
    checker_id: str
    problem_kind: str
    specification_kind: str
    premises: tuple[JudgmentId, ...] = ()
    certificate: object = None
    policy: ConditionPolicy = ConditionPolicy.REQUIRE_PROVED
    discharge_obligations: tuple[ObligationId, ...] = ()


class CommitResult:
    __slots__ = ()

    def is_committed(self) -> bool:
        return isinstance(self, Committed)

    def is_deferred(self) -> bool:
        return isinstance(self, Deferred)

    def is_rejected(self) -> bool:
        return isinstance(self, Rejected)


@dataclass(frozen=True, slots=True)
class Committed(CommitResult):
    inference: InferenceId
    judgments: tuple[JudgmentId, ...]
    obligations: tuple[ObligationId, ...] = ()
    discharged: tuple[ObligationId, ...] = ()


@dataclass(frozen=True, slots=True)
class Deferred(CommitResult):
    """Nothing was written; the submission can be retried after resolution."""

    reason: Reason
    detail: str
    conditions: tuple[Proposition, ...] = ()


@dataclass(frozen=True, slots=True)
class Rejected(CommitResult):
    """The submission is invalid or the specification was refuted.

    `refutation` is a refutation of a requested conclusion. `refuted_conditions`
    are necessary conditions proved false; they invalidate this application but
    do not refute the conclusion itself.
    """

    detail: str
    refutation: Refuted | None = None
    refuted_conditions: tuple[Proposition, ...] = ()


def commit(store: KernelStore, proposal: CommitProposal) -> CommitResult:
    """Verify and publish one submission, or return without writing."""
    try:
        frame = store.frames.get(proposal.frame)
    except KeyError:
        return Rejected(f"frame does not exist: {proposal.frame}")
    if not proposal.conclusions:
        return Rejected("a submission needs at least one conclusion")
    consistency = store.consistency(frame.id)
    if isinstance(consistency, Inconsistent):
        return Rejected(
            "the frame is inconsistent: " + consistency.detail
        )

    for conclusion in proposal.conclusions:
        if not store.frames.is_visible(conclusion.meaning.frame, frame.id):
            return Rejected("a conclusion was read in a frame outside the submission")
        escaped = store.frames.escapes(frame.id, conclusion.term)
        if escaped:
            return Rejected(f"a local symbol escapes the frame: {escaped!r}")

    spec = store.checkers.spec(proposal.checker_id)
    if spec is None:
        return Deferred(
            Reason.FRAGMENT,
            f"checker not registered: {proposal.checker_id}",
        )
    if proposal.problem_kind not in spec.accepted_problem_kinds:
        return Rejected(
            f"checker {spec.checker.id} is not admitted for problem kind "
            f"{proposal.problem_kind!r}"
        )
    if proposal.specification_kind not in spec.accepted_specification_kinds:
        return Rejected(
            f"checker {spec.checker.id} is not admitted for specification "
            f"kind {proposal.specification_kind!r}"
        )
    if not spec.certificate_schema.accepts(proposal.certificate):
        return Rejected(
            "invalid evidence: certificate does not match the declared schema"
        )
    checker = spec.checker

    premise_propositions: list[Proposition] = []
    premises_by_id: dict[JudgmentId, Judgment] = {}
    for premise_id in proposal.premises:
        try:
            premise = store.get_judgment(premise_id)
        except KeyError:
            return Rejected(f"premise does not exist: {premise_id}")
        if not store.frames.is_visible(premise.frame, frame.id):
            return Rejected("a premise is outside the submission frame")
        premise_propositions.append(premise.proposition)
        premises_by_id[premise_id] = premise

    outcome = checker.check(
        CheckRequest(
            frame=frame.id,
            conclusions=proposal.conclusions,
            premises=tuple(premise_propositions),
            certificate=proposal.certificate,
        )
    )
    if isinstance(outcome, InvalidEvidence):
        return Rejected(f"invalid evidence: {outcome.detail}")
    if isinstance(outcome, Refuted):
        return Rejected(f"refuted: {outcome.detail}", refutation=outcome)
    if isinstance(outcome, Unverified):
        return Deferred(outcome.reason, outcome.detail or "not verified")
    if not isinstance(outcome, Verified):
        return Rejected("checker returned an unsupported outcome")
    if outcome.checked != proposal.conclusions:
        return Rejected("the checker verified a different specification")

    used_indices = outcome.used_premises
    if any(
        not isinstance(index, int)
        or index < 0
        or index >= len(proposal.premises)
        for index in used_indices
    ):
        return Rejected("the checker reported an invalid premise index")
    used_premises = tuple(
        dict.fromkeys(proposal.premises[index] for index in used_indices)
    )
    inherited: list[ObligationId] = []
    for premise_id in used_premises:
        inherited.extend(premises_by_id[premise_id].obligations)
    inherited_ids = list(dict.fromkeys(inherited))
    inherited_obligations = [
        store.get_obligation(identifier) for identifier in inherited_ids
    ]
    for obligation in inherited_obligations:
        if not store.frames.is_visible(
            obligation.proposition.meaning.frame, frame.id
        ):
            return Rejected(
                "an inherited obligation was read outside the submission frame"
            )

    inherited_propositions = {
        obligation.proposition for obligation in inherited_obligations
    }
    reported: list[ObligationReport] = []
    for report in outcome.obligations:
        if report.proposition in inherited_propositions:
            continue
        if any(report.proposition == known.proposition for known in reported):
            continue
        if not store.frames.is_visible(report.proposition.meaning.frame, frame.id):
            return Rejected(
                "an obligation was read outside the submission frame"
            )
        reported.append(report)

    reused_ids: list[ObligationId] = []
    new_reports: list[ObligationReport] = []
    for report in reported:
        existing = store.find_obligation(report.proposition, frame.id)
        if existing is not None and existing not in inherited_ids:
            reused_ids.append(existing)
        else:
            new_reports.append(report)

    pending = [
        obligation.proposition
        for obligation in inherited_obligations
        if not store.is_discharged(obligation.id, frame.id)
    ] + [
        store.get_obligation(identifier).proposition
        for identifier in reused_ids
        if not store.is_discharged(identifier, frame.id)
    ] + [report.proposition for report in new_reports]
    refuted_conditions = tuple(
        proposition
        for proposition in dict.fromkeys(pending)
        if store.refutation_of(proposition, frame.id) is not None
    )
    if refuted_conditions:
        return Rejected(
            "a required condition is refuted",
            refuted_conditions=refuted_conditions,
        )
    if pending:
        if proposal.policy is ConditionPolicy.REQUIRE_PROVED:
            return Deferred(
                Reason.GUARDED,
                "the submission has open conditions and the policy requires proof",
                tuple(pending),
            )
        if proposal.policy is ConditionPolicy.REQUEST_CASES:
            return Deferred(
                Reason.GUARDED,
                "the submission requests a case split over its open conditions",
                tuple(pending),
            )

    inference_id = store.new_inference_id()
    new_obligations = []
    new_obligation_ids: list[ObligationId] = []
    for report in new_reports:
        obligation_id = store.new_obligation_id()
        new_obligation_ids.append(obligation_id)
        new_obligations.append(
            Obligation(
                obligation_id,
                frame.id,
                report.proposition,
                report.reason,
                inference_id,
            )
        )
    carried = tuple(
        dict.fromkeys(
            tuple(inherited_ids)
            + tuple(reused_ids)
            + tuple(new_obligation_ids)
        )
    )

    judgments = []
    judgment_ids: list[JudgmentId] = []
    for conclusion in proposal.conclusions:
        judgment_id = store.new_judgment_id()
        judgment_ids.append(judgment_id)
        judgments.append(
            Judgment(judgment_id, frame.id, conclusion, carried, inference_id)
        )
    inference = InferenceRecord(
        inference_id,
        frame.id,
        checker.id,
        checker.version,
        used_premises,
        tuple(judgment_ids),
        proposal.certificate,
        outcome.reads,
        spec.trusted_dependencies,
    )

    discharges: list[Discharge] = []
    if proposal.discharge_obligations:
        if len(set(proposal.discharge_obligations)) != len(
            proposal.discharge_obligations
        ):
            return Rejected("a submission repeats a discharge target")
        supports: set[JudgmentId] = set()
        for premise_id in used_premises:
            supports.add(premise_id)
            supports.update(store.support(premise_id))
        for obligation_id in proposal.discharge_obligations:
            try:
                target_obligation = store.get_obligation(obligation_id)
            except KeyError:
                return Rejected(
                    f"obligation does not exist: {obligation_id}"
                )
            if not store.frames.is_visible(
                target_obligation.frame, frame.id
            ):
                return Rejected(
                    "the discharged obligation is outside the submission frame"
                )
            if not store.frames.is_visible(
                target_obligation.proposition.meaning.frame, frame.id
            ):
                return Rejected(
                    "the discharged obligation proposition is outside the "
                    "submission frame"
                )
            if store.is_discharged(obligation_id, frame.id):
                return Rejected("the obligation is already discharged")
            proof = next(
                (
                    judgment
                    for judgment in judgments
                    if judgment.proposition == target_obligation.proposition
                ),
                None,
            )
            if proof is None:
                return Rejected(
                    "no new judgment proves the discharged obligation"
                )
            for open_obligation in proof.obligations:
                if not store.is_discharged(open_obligation, frame.id):
                    return Rejected(
                        "the discharging proof still has open conditions"
                    )
            for support_id in supports:
                support = store.get_judgment(support_id)
                if obligation_id in support.obligations and not (
                    store.is_discharged(obligation_id, frame.id)
                ):
                    return Rejected(
                        "cyclic discharge: the proof support depends on "
                        "the open obligation"
                    )
            discharges.append(
                Discharge(obligation_id, proof.id, frame.id)
            )

    store._publish(
        obligations=tuple(new_obligations),
        judgments=tuple(judgments),
        inferences=(inference,),
        discharges=tuple(discharges),
    )
    return Committed(
        inference_id,
        tuple(judgment_ids),
        carried,
        tuple(discharge.obligation for discharge in discharges),
    )


__all__ = [
    "CommitProposal",
    "CommitResult",
    "Committed",
    "ConditionPolicy",
    "Deferred",
    "Rejected",
    "commit",
]
