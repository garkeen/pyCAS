"""Non-publishing three-valued decisions over the commit boundary.

A `Verdict` is the closed answer of `decide`:

    Yes(proof_receipt) | No(refutation_receipt) | Unknown(blockers)

`decide` calls `validate_commit` and never `publish_commit`.  A `Yes` therefore
carries a checked-but-unpublished `LocalReceipt`, not a `JudgmentId`: the batch
is fixed and immutable, but no judgment exists in the ledger until some caller
explicitly publishes that batch.  `No` carries the checker's witnesses, and
`Unknown` carries the structured blockers that prevented a decision.

The variants deliberately refuse truth testing.  Three-valued results must be
inspected by variant; `bool(verdict)` raises instead of silently treating an
unknown as true.  A necessary condition that is not closed in the query frame
is `Unknown(GUARDED)`, never `Yes` or `No`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from cas.foundation.ids import FrameId
from cas.kernel.commit import (
    CommitProposal,
    Deferred,
    Rejected,
    RejectedKind,
    ValidatedCommitBatch,
    validate_commit,
)
from cas.kernel.evidence import (
    AlgebraService,
    BudgetService,
    CheckerSpec,
    DecisionService,
    DefinednessService,
    SupportsService,
    VerificationContext,
)
from cas.kernel.store import KernelError, KernelStore
from cas.kernel.trust import AxiomRef
from cas.language.decisions import Blocker, Reason
from cas.language.execution import BudgetTicket, ExecutionBudget
from cas.language.propositions import Proposition
from cas.syntax import term as T

_NOT_A_BOOLEAN = (
    "a Verdict is three-valued; inspect VerdictYes, VerdictNo or "
    "VerdictUnknown instead of testing truthiness"
)


@dataclass(frozen=True, slots=True)
class LocalReceipt:
    """A checked but unpublished proof receipt bound to one snapshot.

    The receipt records the proposition, the checker identity, the certificate
    and the frame it was checked in, together with the immutable
    `ValidatedCommitBatch` that `validate_commit` fixed.  It is not a
    `JudgmentId`: nothing was inserted into the ledger.  Publishing the batch is
    a separate, explicit act and is never performed by `decide`.
    """

    proposition: Proposition
    checker_id: str
    checker_version: str
    certificate: object
    frame: FrameId
    batch: ValidatedCommitBatch
    context: VerificationContext

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("a local receipt needs a proposition")
        for label, value in (
            ("checker id", self.checker_id),
            ("checker version", self.checker_version),
        ):
            if not isinstance(value, str) or not value:
                raise ValueError(f"a local receipt needs a {label}")
        if isinstance(self.frame, bool) or not isinstance(self.frame, int):
            raise TypeError("a local receipt needs a FrameId")
        if not isinstance(self.batch, ValidatedCommitBatch):
            raise TypeError(
                "a local receipt needs a validated commit batch"
            )
        if not isinstance(self.context, VerificationContext):
            raise TypeError(
                "a local receipt needs a verification context"
            )
        if self.batch.frame != self.frame:
            raise ValueError(
                "a local receipt batch belongs to another frame"
            )
        if (
            not self.batch.conclusions
            or self.batch.conclusions[0] != self.proposition
        ):
            raise ValueError(
                "a local receipt proposition is not the batch conclusion"
            )
        if self.context.world != self.batch.world:
            raise ValueError(
                "a local receipt context belongs to another world"
            )
        if self.context.frame != self.frame:
            raise ValueError(
                "a local receipt context belongs to another frame"
            )


@dataclass(frozen=True, slots=True)
class RefutationReceipt:
    """The checker refuted the requested proposition with witnesses."""

    proposition: Proposition
    witnesses: tuple[T.Term, ...]
    detail: str
    checker_id: str
    checker_version: str

    def __post_init__(self) -> None:
        if not isinstance(self.proposition, Proposition):
            raise TypeError("a refutation receipt needs a proposition")
        witnesses = tuple(self.witnesses)
        if not witnesses:
            raise ValueError("a refutation receipt needs at least one witness")
        if any(not isinstance(item, T.Term) for item in witnesses):
            raise TypeError("refutation witnesses must be terms")
        if not isinstance(self.detail, str) or not self.detail:
            raise ValueError("a refutation receipt needs a detail")
        for label, value in (
            ("checker id", self.checker_id),
            ("checker version", self.checker_version),
        ):
            if not isinstance(value, str) or not value:
                raise ValueError(f"a refutation receipt needs a {label}")
        object.__setattr__(self, "witnesses", witnesses)


@dataclass(frozen=True, slots=True)
class VerdictYes:
    """The requested proposition was verified but not published."""

    receipt: LocalReceipt

    def __post_init__(self) -> None:
        if not isinstance(self.receipt, LocalReceipt):
            raise TypeError("a yes verdict needs a local receipt")

    def __bool__(self) -> bool:
        raise TypeError(_NOT_A_BOOLEAN)


@dataclass(frozen=True, slots=True)
class VerdictNo:
    """The requested proposition was refuted."""

    receipt: RefutationReceipt

    def __post_init__(self) -> None:
        if not isinstance(self.receipt, RefutationReceipt):
            raise TypeError("a no verdict needs a refutation receipt")

    def __bool__(self) -> bool:
        raise TypeError(_NOT_A_BOOLEAN)


@dataclass(frozen=True, slots=True)
class VerdictUnknown:
    """No decision was reached; at least one blocker explains why."""

    blockers: tuple[Blocker, ...]

    def __post_init__(self) -> None:
        blockers = tuple(self.blockers)
        if not blockers:
            raise ValueError("an unknown verdict needs at least one blocker")
        if any(not isinstance(item, Blocker) for item in blockers):
            raise TypeError("unknown verdict blockers must be Blockers")
        object.__setattr__(self, "blockers", blockers)

    def __bool__(self) -> bool:
        raise TypeError(_NOT_A_BOOLEAN)


Verdict: TypeAlias = VerdictYes | VerdictNo | VerdictUnknown


def _checker_spec(store: KernelStore, proposal: CommitProposal) -> CheckerSpec:
    """The admitted checker registration a validated proposal used."""
    spec = store.checkers.spec(proposal.checker_id)
    if spec is None:
        raise KernelError(
            "a validated submission names an unregistered checker: "
            f"{proposal.checker_id}"
        )
    return spec


def _checker_identity(
    store: KernelStore, proposal: CommitProposal
) -> tuple[str, str]:
    """The admitted checker identity a validated or refuted proposal used."""
    spec = _checker_spec(store, proposal)
    return spec.checker.id, spec.checker.version


def _context_for(
    store: KernelStore,
    proposal: CommitProposal,
) -> VerificationContext:
    """Reconstruct the same context `validate_commit` built.

    The receipt must carry the same decision, support, budget ticket, admitted
    axioms and algebra request as the checked request, including the
    proposal's own budget and algebra view.
    """
    frame_record = store.frames.get(proposal.frame)
    spec = _checker_spec(store, proposal)
    ticket_budget = (
        proposal.budget
        if proposal.budget is not None
        else ExecutionBudget()
    )
    decision = DecisionService(store.frames.world.language)
    return VerificationContext(
        world=frame_record.world,
        frame=frame_record.id,
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
            decision, store.frames, frame_record.id
        ),
    )


def _target(proposal: CommitProposal) -> Proposition | None:
    return proposal.conclusions[0] if proposal.conclusions else None


def _deferred_blocker(
    proposal: CommitProposal, deferred: Deferred
) -> Blocker:
    return Blocker(
        deferred.reason,
        deferred.detail,
        missing=deferred.missing,
        conditions=deferred.conditions,
        target=_target(proposal),
        budget=proposal.budget,
    )


def _rejected_blocker(
    proposal: CommitProposal, rejected: Rejected
) -> Blocker:
    """Map a refusal that did not refute the conclusion to a blocker.

    A refuted necessary condition invalidates this application but does not
    refute the requested conclusion.  It is `GUARDED` with the exact conditions
    preserved, never `No`.
    """
    if rejected.kind is RejectedKind.REFUTED_CONDITION:
        return Blocker(
            Reason.GUARDED,
            "a necessary condition was refuted: " + rejected.detail,
            conditions=rejected.refuted_conditions,
            target=_target(proposal),
            budget=proposal.budget,
        )
    missing = (
        frozenset({"accepted_proposal_evidence"})
        if rejected.kind is RejectedKind.INVALID_EVIDENCE
        else frozenset({"valid_proposal_request"})
    )
    return Blocker(
        Reason.FRAGMENT,
        "the checker rejected the proposed evidence: " + rejected.detail,
        missing=missing,
        target=_target(proposal),
        budget=proposal.budget,
    )


def _open_conditions(
    store: KernelStore, batch: ValidatedCommitBatch
) -> tuple[Proposition, ...]:
    """The obligations the batch would publish without a closed proof.

    A batch may be validated under `ALLOW_CONDITIONAL`; `decide` must still
    report such an answer as `Unknown(GUARDED)`.  Discharges carried by the same
    batch count as closed even though they are not in the ledger yet.
    """
    discharged = set(batch.committed.discharged)
    new_obligations = {
        obligation.id: obligation.proposition
        for obligation in batch.obligations
    }
    open_conditions: list[Proposition] = []
    for identifier in batch.committed.obligations:
        if identifier in discharged:
            continue
        if store.is_discharged(identifier, batch.frame):
            continue
        proposition = new_obligations.get(identifier)
        if proposition is None:
            proposition = store.get_obligation(identifier).proposition
        open_conditions.append(proposition)
    return tuple(open_conditions)


def decide(store: KernelStore, proposal: CommitProposal) -> Verdict:
    """Decide one submission without writing the ledger or a workspace record.

    Only `validate_commit` runs.  A successful validation is returned as
    `Yes(LocalReceipt)`; a refutation is `No(RefutationReceipt)`; every other
    outcome is `Unknown` with its structured blockers.  A validated batch that
    still carries open conditions is `Unknown(GUARDED)`, because the necessary
    condition was not closed in the query frame.
    """
    outcome = validate_commit(store, proposal)
    if isinstance(outcome, ValidatedCommitBatch):
        open_conditions = _open_conditions(store, outcome)
        if open_conditions:
            return VerdictUnknown(
                (
                    Blocker(
                        Reason.GUARDED,
                        "the validated batch still has open conditions",
                        conditions=open_conditions,
                        target=_target(proposal),
                        budget=proposal.budget,
                    ),
                )
            )
        checker_id, checker_version = _checker_identity(store, proposal)
        return VerdictYes(
            LocalReceipt(
                proposal.conclusions[0],
                checker_id,
                checker_version,
                proposal.certificate,
                proposal.frame,
                outcome,
                _context_for(store, proposal),
            )
        )
    if isinstance(outcome, Deferred):
        return VerdictUnknown((_deferred_blocker(proposal, outcome),))
    if isinstance(outcome, Rejected):
        refutation = outcome.refutation
        if refutation is not None:
            checker_id, checker_version = _checker_identity(store, proposal)
            return VerdictNo(
                RefutationReceipt(
                    refutation.proposition,
                    refutation.witnesses,
                    refutation.detail,
                    checker_id,
                    checker_version,
                )
            )
        return VerdictUnknown((_rejected_blocker(proposal, outcome),))
    raise TypeError("validate_commit returned an unknown result")


__all__ = [
    "LocalReceipt",
    "RefutationReceipt",
    "Verdict",
    "VerdictNo",
    "VerdictUnknown",
    "VerdictYes",
    "decide",
]
