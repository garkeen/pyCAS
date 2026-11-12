"""The single trusted publication boundary.

`validate_commit` turns a verified proposal into an immutable
`ValidatedCommitBatch`. It checks the frame, the conclusions, the premises and
the checker's report, applies one condition policy to every open obligation —
inherited or newly reported — and fixes exactly one batch. `publish_commit`
then inserts that batch into the ledger, or refuses it without writing.

The kernel never decides mathematics. It ensures that whatever was verified is
exactly what was requested, that every condition is recorded, and that nothing
is written unless the whole submission passes.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import StrEnum
from typing import TypeAlias

from cas.foundation.ids import (
    FrameId,
    InferenceId,
    JudgmentId,
    ObligationId,
    WorldId,
)
from cas.kernel.evidence import (
    AlgebraService,
    BudgetService,
    CheckRequest,
    DecisionService,
    DefinednessService,
    InvalidEvidence,
    ObligationReport,
    Refuted,
    SupportsService,
    Unverified,
    VerificationContext,
    Verified,
)
from cas.kernel.model import (
    Discharge,
    Inconsistent,
    InferenceRecord,
    Judgment,
    Obligation,
)
from cas.kernel.store import KernelError, KernelStore
from cas.kernel.trust import AxiomRef, certificate_limits
from cas.language.decisions import Reason
from cas.language.execution import (
    BudgetTicket,
    ConditionPolicy,
    ExecutionBudget,
)
from cas.language.problems import ProblemSpec
from cas.language.propositions import Proposition
from cas.language.roles import CandidateRole
from cas.semantics.frames import FrameSorts
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class CommitProposal:
    """One submission.

    `conclusions` are the propositions the caller claims; `certificate` is
    interpreted only by the checker named by `checker_id`. The kernel does not
    accept an "all of it is true" flag anywhere.

    `candidate` is the actual mathematical value the workflow will publish.  It
    is handed to the checker unchanged so the checker can require that the
    certificate and specification name the same term.  `candidate_role` names
    which part of the claim that value is; the checker selects the expected
    term from the role, never from the operation name.  A core-logic
    submission publishes no candidate and leaves both fields `None`; a
    mathematical checker must reject that omission.
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
    problem: ProblemSpec | None = None
    budget: ExecutionBudget | None = None
    candidate: T.Term | None = None
    candidate_role: CandidateRole | None = None
    structured: tuple[tuple[str, T.Term], ...] | None = None
    algebra: AlgebraRequest | None = None

    def __post_init__(self) -> None:
        if self.structured is not None:
            names = [name for name, _ in self.structured]
            if any(not name for name in names):
                raise ValueError(
                    "a structured commit payload needs a component name"
                )
            if len(set(names)) != len(names):
                raise ValueError(
                    "a structured commit payload repeats a component name"
                )
            if any(
                not isinstance(term, T.Term) for _, term in self.structured
            ):
                raise TypeError(
                    "a structured commit payload holds terms"
                )
        if not isinstance(self.policy, ConditionPolicy):
            raise TypeError("a commit policy must be a ConditionPolicy")
        if self.budget is not None and not isinstance(
            self.budget, ExecutionBudget
        ):
            raise TypeError(
                "a commit budget must be an ExecutionBudget or None"
            )
        if self.problem is not None and not isinstance(
            self.problem, ProblemSpec
        ):
            raise TypeError("a commit problem must be a ProblemSpec")
        if self.candidate is not None and not isinstance(
            self.candidate, T.Term
        ):
            raise TypeError("a commit candidate must be a term")
        if self.candidate_role is not None and not isinstance(
            self.candidate_role, CandidateRole
        ):
            raise TypeError(
                "a commit candidate role must be a CandidateRole or None"
            )
        if self.algebra is not None and not isinstance(
            self.algebra, AlgebraRequest
        ):
            raise TypeError(
                "a commit algebra request must be an AlgebraRequest or None"
            )
        for label, value in (
            ("checker", self.checker_id),
            ("problem kind", self.problem_kind),
            ("specification kind", self.specification_kind),
        ):
            if not isinstance(value, str) or not value:
                raise ValueError(f"a commit needs a {label}")
        if any(
            not isinstance(item, Proposition)
            for item in self.conclusions
        ):
            raise TypeError("commit conclusions must be propositions")


@dataclass(frozen=True, slots=True)
class Committed:
    inference: InferenceId
    judgments: tuple[JudgmentId, ...]
    obligations: tuple[ObligationId, ...] = ()
    discharged: tuple[ObligationId, ...] = ()


_BATCH_SEAL = object()


def _require_identifier(value: object, label: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"a validated batch needs a {label}")


def _require_unique(values: tuple[object, ...], label: str) -> None:
    if len(set(values)) != len(values):
        raise ValueError(f"a validated batch repeats a {label}")


@dataclass(frozen=True, slots=True)
class ValidatedCommitBatch:
    """One fully validated publication that is not in the ledger yet.

    Only `_issue_batch` can construct a batch. The batch is immutable and
    carries the exact records and identifiers that `publish_commit` will write:
    the workflow may publish it or abandon it, never edit it.
    """

    frame: FrameId
    world: WorldId
    conclusions: tuple[Proposition, ...]
    used_premises: tuple[JudgmentId, ...]
    obligations: tuple[Obligation, ...]
    judgments: tuple[Judgment, ...]
    inference: InferenceRecord
    discharges: tuple[Discharge, ...]
    committed: Committed
    store_token: object = field(repr=False, compare=False)
    _seal: object = field(
        init=False, default=None, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if getattr(self, "_seal", None) is not _BATCH_SEAL:
            raise ValueError(
                "a validated commit batch must be issued by the kernel"
            )
        _require_identifier(self.frame, "frame id")
        _require_identifier(self.world, "world id")
        if self.store_token is None:
            raise TypeError("a validated batch needs its issuing store token")

        if not isinstance(self.conclusions, tuple):
            raise TypeError("validated conclusions must be a tuple")
        if not self.conclusions:
            raise ValueError("a validated batch needs at least one conclusion")
        if any(
            not isinstance(item, Proposition) for item in self.conclusions
        ):
            raise TypeError("validated conclusions must be propositions")

        if not isinstance(self.used_premises, tuple):
            raise TypeError("validated premises must be a tuple")
        for premise in self.used_premises:
            _require_identifier(premise, "premise id")
        _require_unique(self.used_premises, "used premise")

        if not isinstance(self.obligations, tuple):
            raise TypeError("validated obligations must be a tuple")
        if any(
            not isinstance(item, Obligation) for item in self.obligations
        ):
            raise TypeError("validated obligations must be obligations")
        obligation_ids = tuple(item.id for item in self.obligations)
        _require_unique(obligation_ids, "obligation")

        if not isinstance(self.judgments, tuple):
            raise TypeError("validated judgments must be a tuple")
        if any(not isinstance(item, Judgment) for item in self.judgments):
            raise TypeError("validated judgments must be judgments")
        judgment_ids = tuple(item.id for item in self.judgments)
        _require_unique(judgment_ids, "judgment")

        if not isinstance(self.inference, InferenceRecord):
            raise TypeError("a validated batch needs an inference record")

        if not isinstance(self.discharges, tuple):
            raise TypeError("validated discharges must be a tuple")
        if any(not isinstance(item, Discharge) for item in self.discharges):
            raise TypeError("validated discharges must be discharges")
        _require_unique(
            tuple(item.obligation for item in self.discharges),
            "discharge target",
        )

        for obligation in self.obligations:
            if obligation.frame != self.frame:
                raise ValueError(
                    "a validated obligation is outside the batch frame"
                )
            if obligation.introduced_by != self.inference.id:
                raise ValueError(
                    "a validated obligation was introduced by another inference"
                )
        for judgment in self.judgments:
            if judgment.frame != self.frame:
                raise ValueError(
                    "a validated judgment is outside the batch frame"
                )
            if judgment.inference != self.inference.id:
                raise ValueError(
                    "a validated judgment belongs to another inference"
                )
        if self.inference.frame != self.frame:
            raise ValueError(
                "a validated inference is outside the batch frame"
            )
        if self.inference.conclusions != judgment_ids:
            raise ValueError(
                "a validated inference and its judgments disagree"
            )
        for discharge in self.discharges:
            if discharge.frame != self.frame:
                raise ValueError(
                    "a validated discharge is outside the batch frame"
                )

        if not isinstance(self.committed, Committed):
            raise TypeError("a validated batch needs a committed result")
        committed = self.committed
        _require_identifier(committed.inference, "committed inference id")
        if not isinstance(committed.judgments, tuple):
            raise TypeError("committed judgments must be a tuple")
        for identifier in committed.judgments:
            _require_identifier(identifier, "committed judgment id")
        _require_unique(committed.judgments, "committed judgment")
        if not isinstance(committed.obligations, tuple):
            raise TypeError("committed obligations must be a tuple")
        for obligation_identifier in committed.obligations:
            _require_identifier(
                obligation_identifier, "committed obligation id"
            )
        _require_unique(committed.obligations, "committed obligation")
        if not isinstance(committed.discharged, tuple):
            raise TypeError("committed discharges must be a tuple")
        for discharged_identifier in committed.discharged:
            _require_identifier(
                discharged_identifier, "committed discharged id"
            )
        _require_unique(committed.discharged, "committed discharge")
        if committed.inference != self.inference.id:
            raise ValueError(
                "the committed result names another inference"
            )
        if committed.judgments != judgment_ids:
            raise ValueError(
                "the committed result names other judgments"
            )
        if committed.discharged != tuple(
            item.obligation for item in self.discharges
        ):
            raise ValueError(
                "the committed result names other discharges"
            )


def _issue_batch(
    *,
    frame: FrameId,
    world: WorldId,
    conclusions: tuple[Proposition, ...],
    used_premises: tuple[JudgmentId, ...],
    obligations: tuple[Obligation, ...],
    judgments: tuple[Judgment, ...],
    inference: InferenceRecord,
    discharges: tuple[Discharge, ...],
    committed: Committed,
    store_token: object,
) -> ValidatedCommitBatch:
    """Build the one sealed batch a successful validation may publish.

    The constructor is bypassed on purpose: `_seal` is not an init field, so a
    `dataclasses.replace` copy receives the rejecting default.  Only this
    factory writes the module seal, and it runs the same `__post_init__`
    validation as a direct construction.
    """
    batch = object.__new__(ValidatedCommitBatch)
    object.__setattr__(batch, "frame", frame)
    object.__setattr__(batch, "world", world)
    object.__setattr__(batch, "conclusions", conclusions)
    object.__setattr__(batch, "used_premises", used_premises)
    object.__setattr__(batch, "obligations", obligations)
    object.__setattr__(batch, "judgments", judgments)
    object.__setattr__(batch, "inference", inference)
    object.__setattr__(batch, "discharges", discharges)
    object.__setattr__(batch, "committed", committed)
    object.__setattr__(batch, "store_token", store_token)
    object.__setattr__(batch, "_seal", _BATCH_SEAL)
    batch.__post_init__()
    return batch


@dataclass(frozen=True, slots=True)
class Deferred:
    """Nothing was written; the submission can be retried after resolution.

    `conditions` are the open obligations that caused the deferral and
    `missing` preserves the capabilities the checker reported.
    """

    reason: Reason
    detail: str
    conditions: tuple[Proposition, ...] = ()
    missing: frozenset[str] = frozenset()

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("a deferred result needs a Reason")
        if not isinstance(self.detail, str) or not self.detail:
            raise ValueError("a deferred result needs a detail")
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError("deferred conditions must be propositions")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError(
                "deferred capabilities must be non-empty strings"
            )
        object.__setattr__(self, "conditions", conditions)
        object.__setattr__(self, "missing", missing)


class RejectedKind(StrEnum):
    """Why a submission was refused; the closed set of rejection categories."""

    INVALID_EVIDENCE = "invalid_evidence"
    INVALID_REQUEST = "invalid_request"
    REFUTED_CONDITION = "refuted_condition"
    REFUTED_SPECIFICATION = "refuted_specification"


@dataclass(frozen=True, slots=True)
class Rejected:
    """The submission is invalid or the specification was refuted.

    `kind` is the closed category of refusal.  `refutation` is a refutation of a
    requested conclusion; `refuted_conditions` are necessary conditions proved
    false, which invalidate this application but do not refute the conclusion
    itself.  `detail` is always a non-empty explanation.
    """

    detail: str
    refutation: Refuted | None = None
    refuted_conditions: tuple[Proposition, ...] = ()
    kind: RejectedKind = RejectedKind.INVALID_REQUEST

    def __post_init__(self) -> None:
        if not isinstance(self.detail, str) or not self.detail:
            raise ValueError("a rejected result needs a detail")
        if not isinstance(self.kind, RejectedKind):
            raise TypeError("a rejected result needs a RejectedKind")
        if self.refutation is not None and not isinstance(
            self.refutation, Refuted
        ):
            raise TypeError(
                "a rejected result refutation must be a Refuted or None"
            )
        conditions = tuple(self.refuted_conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError("rejected conditions must be propositions")
        object.__setattr__(self, "refuted_conditions", conditions)


CommitResult: TypeAlias = ValidatedCommitBatch | Deferred | Rejected


def validate_commit(
    store: KernelStore, proposal: CommitProposal
) -> CommitResult:
    """Validate one submission and fix its publication batch.

    Nothing is written to the ledger. A successful validation returns the
    immutable `ValidatedCommitBatch`; otherwise the submission is `Deferred` or
    `Rejected` and the ledger is unchanged.
    """
    try:
        frame = store.frames.get(proposal.frame)
    except KeyError:
        return Rejected(
            f"frame does not exist: {proposal.frame}",
            kind=RejectedKind.INVALID_REQUEST,
        )
    if not proposal.conclusions:
        return Rejected(
            "a submission needs at least one conclusion",
            kind=RejectedKind.INVALID_REQUEST,
        )
    consistency = store.consistency(frame.id)
    if isinstance(consistency, Inconsistent):
        return Rejected(
            "the frame is inconsistent: " + consistency.detail,
            kind=RejectedKind.INVALID_REQUEST,
        )

    for conclusion in proposal.conclusions:
        if not store.frames.readable(conclusion, frame.id):
            if conclusion.meaning.world != frame.world:
                return Rejected(
                    "a conclusion belongs to another meaning world",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            if not store.frames.is_visible(
                conclusion.meaning.frame, frame.id
            ):
                return Rejected(
                    "a conclusion was read in a frame outside the submission",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            escaped = store.frames.escapes(frame.id, conclusion.term)
            return Rejected(
                f"a local symbol escapes the frame: {escaped!r}",
                kind=RejectedKind.INVALID_REQUEST,
            )

    spec = store.checkers.spec(proposal.checker_id)
    if spec is None:
        return Deferred(
            Reason.FRAGMENT,
            f"checker not registered: {proposal.checker_id}",
        )
    for basis in spec.trusted_dependencies:
        if not store.bases.verify(basis):
            return Rejected(
                f"checker {spec.checker.id} depends on an unadmitted basis: "
                f"{basis.name!r} {basis.version!r}",
                kind=RejectedKind.INVALID_REQUEST,
            )
    if proposal.problem_kind not in spec.accepted_problem_kinds:
        return Rejected(
            f"checker {spec.checker.id} is not admitted for problem kind "
            f"{proposal.problem_kind!r}",
            kind=RejectedKind.INVALID_REQUEST,
        )
    if proposal.specification_kind not in spec.accepted_specification_kinds:
        return Rejected(
            f"checker {spec.checker.id} is not admitted for specification "
            f"kind {proposal.specification_kind!r}",
            kind=RejectedKind.INVALID_REQUEST,
        )
    if spec.world != frame.world:
        return Rejected(
            f"checker {spec.checker.id} is registered for another world",
            kind=RejectedKind.INVALID_REQUEST,
        )
    if spec.requires_problem and proposal.problem is None:
        return Rejected(
            f"checker {spec.checker.id} requires the original problem",
            kind=RejectedKind.INVALID_REQUEST,
        )
    if (
        proposal.problem is not None
        and proposal.problem.operation != proposal.problem_kind
    ):
        return Rejected(
            "the problem does not match the checker problem kind",
            kind=RejectedKind.INVALID_REQUEST,
        )
    if not spec.certificate_schema.accepts(proposal.certificate):
        return Rejected(
            "invalid evidence: certificate does not match the declared schema",
            kind=RejectedKind.INVALID_EVIDENCE,
        )
    if not spec.certificate_schema.within_budget(proposal.certificate):
        return Rejected(
            "invalid evidence: certificate exceeds the schema budget",
            kind=RejectedKind.INVALID_EVIDENCE,
        )
    if proposal.budget is not None:
        max_nodes = spec.certificate_schema.max_nodes
        max_depth = spec.certificate_schema.max_depth
        if proposal.budget.max_nodes is not None:
            max_nodes = min(max_nodes, proposal.budget.max_nodes)
        if proposal.budget.max_depth is not None:
            max_depth = min(max_depth, proposal.budget.max_depth)
        if (
            certificate_limits(
                proposal.certificate,
                max_nodes=max_nodes,
                max_depth=max_depth,
            )
            is None
        ):
            return Rejected(
                "invalid evidence: certificate exceeds the execution budget",
                kind=RejectedKind.INVALID_EVIDENCE,
            )
    checker = spec.checker

    premise_propositions: list[Proposition] = []
    premises_by_id: dict[JudgmentId, Judgment] = {}
    cross_frame_premises = spec.accepts_cross_frame_premises
    for premise_id in proposal.premises:
        try:
            premise = store.get_judgment(premise_id)
        except KeyError:
            return Rejected(
                f"premise does not exist: {premise_id}",
                kind=RejectedKind.INVALID_REQUEST,
            )
        if cross_frame_premises:
            # A case-analysis checker must read judgments issued in its
            # branch frames, which are children of the submission frame and
            # therefore never visible from it.  The proposition must still
            # belong to this store's world and be well scoped in the frame
            # where it was issued; the checker owns the branch relation.
            premise_frame = premise.frame
        else:
            premise_frame = frame.id
        if not store.frames.readable(premise.proposition, premise_frame):
            if premise.proposition.meaning.world != frame.world:
                return Rejected(
                    "a premise belongs to another meaning world",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            if not cross_frame_premises and not store.frames.is_visible(
                premise.frame, frame.id
            ):
                return Rejected(
                    "a premise is outside the submission frame",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            if cross_frame_premises:
                return Rejected(
                    "a premise proposition is not readable in its own frame",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            return Rejected(
                "a premise proposition is not readable in the submission frame",
                kind=RejectedKind.INVALID_REQUEST,
            )
        premise_propositions.append(premise.proposition)
        premises_by_id[premise_id] = premise

    ticket_budget = (
        proposal.budget
        if proposal.budget is not None
        else ExecutionBudget()
    )
    decision = DecisionService(
        store.frames.world.language,
        FrameSorts(store.frames, frame.id),
    )
    context = VerificationContext(
        world=frame.world,
        frame=frame.id,
        frames=store.frames,
        decision=decision,
        supports=SupportsService(
            store.get_judgment,
            store.judgments_visible,
            store.is_discharged,
        ),
        budget=BudgetService(proposal.budget, BudgetTicket(ticket_budget)),
        axioms=tuple(
            AxiomRef.from_basis(basis)
            for basis in spec.trusted_dependencies
        ),
        algebra=(
            None
            if proposal.algebra is None
            else AlgebraService(proposal.algebra)
        ),
        definedness=DefinednessService(
            decision, store.frames, frame.id
        ),
    )
    outcome = checker.check(
        CheckRequest(
            frame=frame.id,
            conclusions=proposal.conclusions,
            premises=tuple(premise_propositions),
            certificate=proposal.certificate,
            problem=proposal.problem,
            candidate=proposal.candidate,
            candidate_role=proposal.candidate_role,
            context=context,
            structured=proposal.structured,
        )
    )
    if isinstance(outcome, InvalidEvidence):
        return Rejected(
            f"invalid evidence: {outcome.detail}",
            kind=RejectedKind.INVALID_EVIDENCE,
        )
    if isinstance(outcome, Refuted):
        return Rejected(
            f"refuted: {outcome.detail}",
            refutation=outcome,
            kind=RejectedKind.REFUTED_SPECIFICATION,
        )
    if isinstance(outcome, Unverified):
        return Deferred(
            outcome.reason,
            outcome.detail,
            outcome.conditions,
            outcome.missing,
        )
    if not isinstance(outcome, Verified):
        return Rejected(
            "checker returned an unsupported outcome",
            kind=RejectedKind.INVALID_EVIDENCE,
        )
    if outcome.checked != proposal.conclusions:
        return Rejected(
            "the checker verified a different specification",
            kind=RejectedKind.INVALID_EVIDENCE,
        )

    used_indices = outcome.used_premises
    if any(
        not isinstance(index, int)
        or index < 0
        or index >= len(proposal.premises)
        for index in used_indices
    ):
        return Rejected(
            "the checker reported an invalid premise index",
            kind=RejectedKind.INVALID_EVIDENCE,
        )
    used_premises = tuple(
        dict.fromkeys(proposal.premises[index] for index in used_indices)
    )
    inherited: list[ObligationId] = []
    for premise_id in used_premises:
        premise = premises_by_id[premise_id]
        if cross_frame_premises:
            # A checker admitted to cross-frame premises certifies that each
            # premise is closed in the frame where it was issued.  Its
            # obligations are therefore not inherited into the submission
            # frame; an open one would make the premise unusable.
            for obligation_id in premise.obligations:
                if not store.is_discharged(
                    obligation_id, premise.frame
                ):
                    return Rejected(
                        "a cross-frame premise still has open conditions",
                        kind=RejectedKind.INVALID_EVIDENCE,
                    )
            continue
        inherited.extend(premise.obligations)
    inherited_ids = list(dict.fromkeys(inherited))
    inherited_obligations = [
        store.get_obligation(identifier) for identifier in inherited_ids
    ]
    for obligation in inherited_obligations:
        if not store.frames.readable(obligation.proposition, frame.id):
            if obligation.proposition.meaning.world != frame.world:
                return Rejected(
                    "an inherited obligation belongs to another meaning world",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            return Rejected(
                "an inherited obligation was read outside the submission frame",
                kind=RejectedKind.INVALID_REQUEST,
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
        if not store.frames.readable(report.proposition, frame.id):
            if report.proposition.meaning.world != frame.world:
                return Rejected(
                    "an obligation belongs to another meaning world",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            return Rejected(
                "an obligation was read outside the submission frame",
                kind=RejectedKind.INVALID_REQUEST,
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
            kind=RejectedKind.REFUTED_CONDITION,
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
        spec.certificate_schema.name,
        spec.certificate_schema.version,
    )

    discharges: list[Discharge] = []
    if proposal.discharge_obligations:
        if len(set(proposal.discharge_obligations)) != len(
            proposal.discharge_obligations
        ):
            return Rejected(
                "a submission repeats a discharge target",
                kind=RejectedKind.INVALID_REQUEST,
            )
        supports: set[JudgmentId] = set()
        for premise_id in used_premises:
            supports.add(premise_id)
            supports.update(store.support(premise_id))
        for obligation_id in proposal.discharge_obligations:
            try:
                target_obligation = store.get_obligation(obligation_id)
            except KeyError:
                return Rejected(
                    f"obligation does not exist: {obligation_id}",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            if not store.frames.is_visible(
                target_obligation.frame, frame.id
            ):
                return Rejected(
                    "the discharged obligation is outside the submission frame",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            if not store.frames.readable(
                target_obligation.proposition, frame.id
            ):
                if target_obligation.proposition.meaning.world != frame.world:
                    return Rejected(
                        "the discharged obligation belongs to another "
                        "meaning world",
                        kind=RejectedKind.INVALID_REQUEST,
                    )
                return Rejected(
                    "the discharged obligation proposition is outside the "
                    "submission frame",
                    kind=RejectedKind.INVALID_REQUEST,
                )
            if store.is_discharged(obligation_id, frame.id):
                return Rejected(
                    "the obligation is already discharged",
                    kind=RejectedKind.INVALID_REQUEST,
                )
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
                    "no new judgment proves the discharged obligation",
                    kind=RejectedKind.INVALID_EVIDENCE,
                )
            if not store.frames.readable(proof.proposition, frame.id):
                if proof.proposition.meaning.world != frame.world:
                    return Rejected(
                        "the discharging proof belongs to another meaning "
                        "world",
                        kind=RejectedKind.INVALID_EVIDENCE,
                    )
                return Rejected(
                    "the discharging proof proposition is outside the "
                    "submission frame",
                    kind=RejectedKind.INVALID_EVIDENCE,
                )
            for open_obligation in proof.obligations:
                if not store.is_discharged(open_obligation, frame.id):
                    return Rejected(
                        "the discharging proof still has open conditions",
                        kind=RejectedKind.INVALID_EVIDENCE,
                    )
            for support_id in supports:
                support = store.get_judgment(support_id)
                if obligation_id in support.obligations and not (
                    store.is_discharged(obligation_id, frame.id)
                ):
                    return Rejected(
                        "cyclic discharge: the proof support depends on "
                        "the open obligation",
                        kind=RejectedKind.INVALID_EVIDENCE,
                    )
            discharges.append(
                Discharge(obligation_id, proof.id, frame.id)
            )

    committed = Committed(
        inference_id,
        tuple(judgment_ids),
        carried,
        tuple(discharge.obligation for discharge in discharges),
    )
    return _issue_batch(
        frame=frame.id,
        world=frame.world,
        conclusions=proposal.conclusions,
        used_premises=used_premises,
        obligations=tuple(new_obligations),
        judgments=tuple(judgments),
        inference=inference,
        discharges=tuple(discharges),
        committed=committed,
        store_token=store._token,
    )


def publish_commit(
    store: KernelStore, batch: ValidatedCommitBatch
) -> Committed:
    """Insert one validated batch, or raise without writing anything.

    A batch is publishable only once, only in its own world and only while its
    frame still exists. Duplicate identifiers are refused by the ledger before
    any insertion, so a second publication leaves the store untouched.
    """
    if not isinstance(batch, ValidatedCommitBatch):
        raise TypeError("only a validated commit batch can be published")
    if getattr(batch, "_seal", None) is not _BATCH_SEAL:
        raise ValueError(
            "a validated commit batch must be issued by the kernel"
        )
    if batch.store_token is not store._token:
        raise KernelError("the commit batch belongs to another store")
    if batch.world != store.frames.world.id:
        raise KernelError("the commit batch belongs to another world")
    try:
        store.frames.get(batch.frame)
    except KeyError:
        raise KernelError(
            f"frame does not exist: {batch.frame!r}"
        ) from None
    if batch.conclusions != tuple(
        judgment.proposition for judgment in batch.judgments
    ):
        raise KernelError(
            "the batch conclusions do not match its judgments"
        )
    if batch.used_premises != batch.inference.premises:
        raise KernelError(
            "the batch premises do not match its inference"
        )
    store._publish(
        obligations=batch.obligations,
        judgments=batch.judgments,
        inferences=(batch.inference,),
        discharges=batch.discharges,
    )
    return batch.committed


__all__ = [
    "ValidatedCommitBatch",
    "validate_commit",
    "publish_commit",
    "CommitProposal",
    "CommitResult",
    "Committed",
    "Deferred",
    "Rejected",
    "RejectedKind",
]
