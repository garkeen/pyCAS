"""`commit`: the single trusted submission entry point.

**`commit` is a boundary operation, not a gate on the inner loop.** It promotes
a candidate conclusion into a dependable fact: it re-checks the evidence,
collects conditions, attempts discharge, and atomically writes Step /
Judgment / Requirement. A guard-free rewrite with no scope change does not need
to pass through it at all: rule soundness was settled when the rule was
admitted. Treating it as a mandatory gate on every computation step turns the
kernel back into an interpreter and the CAS into a theorem prover.

The ten-step flow:

    1  check scope validity and term binding legality
    2  check that premises are accessible in the current scope
    3  call the checker
    4  the checker verifies the conclusion and returns direct conditions
    5  collect undischarged conditions inherited from premises
    6  attempt to discharge conditions using the current context
    7  Proved   -> record the discharge
    8  Refuted  -> this application is inapplicable, refuse submission
    9  Unknown  -> handle according to the guard policy
    10 atomically write Step, Judgment, Requirement

The typical case with no premises and no conditions degenerates to four steps
(scope check -> checker call -> record conclusion -> atomic write), which is a
provable subset of the full flow.
"""


from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum

from cas.errors import BudgetExceeded
from cas.kernel.context import TrackedContext
from cas.kernel.evidence import (
    Accepted,
    Evidence,
    RefutationRejected,
    Rejected,
    UnknownResult,
)
from cas.kernel.ids import JudgmentId, RequirementId, ScopeId, StepId
from cas.kernel.mode import DEFAULT_MODE, ExecutionMode
from cas.kernel.model import (
    ContextReadSet,
    Discharge,
    Judgment,
    Requirement,
    RequirementReason,
    Step,
)
from cas.kernel.services import KernelServices, NullServices
from cas.kernel.store import KernelStore
from cas.kernel.verdict import No, Reason, Refutation, Unknown
from cas.syntax.term import Term


class GuardPolicy(Enum):
    """Guard policy. How Unknown is handled is the one switch that may never be
    turned off."""
    REQUIRE_PROVED = "require_proved"        # automatic simplification default: undecided does not land
    ALLOW_CONDITIONAL = "allow_conditional"  # explicit manual application: land with conditions
    REQUEST_SPLIT = "request_split"          # ask for a case split


@dataclass(frozen=True, slots=True)
class StepProposal:
    scope: ScopeId
    evidence: Evidence
    premises: tuple[JudgmentId, ...] = ()
    conclusions: tuple[Term, ...] = ()
    guard_policy: GuardPolicy = GuardPolicy.REQUIRE_PROVED


@dataclass(frozen=True, slots=True)
class ResolvedProposal:
    """A proposal after kernel premise resolution.

    Only the kernel creates this value. A checker receives resolved premises,
    never caller-supplied premise propositions.
    """
    scope: ScopeId
    evidence: Evidence
    premises: tuple[JudgmentId, ...]
    conclusions: tuple[Term, ...]
    guard_policy: GuardPolicy
    premise_propositions: tuple[Term, ...]


# ---------------------------------------------------------------------------
# Commit results: a closed hierarchy, so consumers must exhaust the branches
# ---------------------------------------------------------------------------

class CommitResult:
    __slots__ = ()

    def is_committed(self) -> bool:
        return isinstance(self, Committed)

    def is_refused(self) -> bool:
        return isinstance(self, Refused)

    def is_undecided(self) -> bool:
        return isinstance(self, Undecided)

    def is_needs_split(self) -> bool:
        return isinstance(self, NeedsSplit)


@dataclass(frozen=True, slots=True)
class Committed(CommitResult):
    step: StepId
    judgments: tuple[JudgmentId, ...]
    requirements: tuple[RequirementId, ...]
    reads: ContextReadSet = field(default_factory=ContextReadSet)


@dataclass(frozen=True, slots=True)
class Refused(CommitResult):
    """The conclusion does not hold, a premise is inaccessible, or a condition
    was refuted: this application is inapplicable."""

    reason: Reason = Reason.FRAGMENT
    detail: str = ""
    refutation: Refutation | None = None

@dataclass(frozen=True, slots=True)
class Undecided(CommitResult):
    """Re-checking was undecided and the policy requires proof: nothing is
    written, because an unverified candidate must not enter trusted reasoning."""
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


@dataclass(frozen=True, slots=True)
class NeedsSplit(CommitResult):
    """The policy requests a case split: hand the pending condition back to the
    workflow to open branches."""
    conditions: tuple[Term, ...] = ()


# ---------------------------------------------------------------------------
# Commit
# ---------------------------------------------------------------------------

def commit(
    store: KernelStore,
    proposal: StepProposal,
    context: TrackedContext | None = None,
    services: KernelServices | None = None,
    discharge_checker_id: str = "kernel.decide",
    mode: ExecutionMode | None = None,
    inherited_reads: ContextReadSet | None = None,
) -> CommitResult:
    """The trusted boundary: a budget-exhausted computation is undecided.

    Search layers (rule matching, definition expansion, simplification) raise
    `BudgetExceeded` when their explicit budget runs out. That is a resource
    limit, not a refutation, so it must leave through the
    `Undecided(Reason.BUDGET)` exit instead of escaping as an exception past the
    trusted boundary (an exception would bypass the three-valued result the rest
    of the system reasons about).
    """
    try:
        return _commit_checked(
            store,
            proposal,
            context=context,
            services=services,
            discharge_checker_id=discharge_checker_id,
            mode=mode,
            inherited_reads=inherited_reads,
        )
    except BudgetExceeded as error:
        return Undecided(Reason.BUDGET, f"budget exhausted during commit: {error}")


def _commit_checked(
    store: KernelStore,
    proposal: StepProposal,
    context: TrackedContext | None = None,
    services: KernelServices | None = None,
    discharge_checker_id: str = "kernel.decide",
    mode: ExecutionMode | None = None,
    inherited_reads: ContextReadSet | None = None,
) -> CommitResult:
    selected_mode = DEFAULT_MODE if mode is None else mode
    selected_services: KernelServices = (
        NullServices() if services is None else services)

    # --- 1. scope validity and term binding legality ---
    try:
        store.scopes.get(proposal.scope)
    except KeyError:
        return Refused(Reason.FRAGMENT, f"scope does not exist: {proposal.scope}")
    # A local symbol must not leak into a conclusion outside its scope: a
    # symbol introduced in a scope (declaration or definition left-hand side)
    # is meaningful only in that scope and its descendants.
    for prop in proposal.conclusions:
        escaped = store.scopes.escapes(proposal.scope, prop)
        if escaped:
            return Refused(Reason.FRAGMENT,
                           f"local symbol escapes into this scope's conclusion: {escaped!r}")
    ctx = TrackedContext(store.scopes, selected_services, proposal.scope, selected_mode) \
        if context is None else context

    # --- 2. premise visibility (a child conclusion may not be used upward;
    #        sibling branches cannot see each other) ---
    inherited: list[RequirementId] = []
    premise_props: list[Term] = []
    for pid in proposal.premises:
        try:
            pj = store.get_judgment(pid)
        except KeyError:
            return Refused(Reason.FRAGMENT, f"premise does not exist: {pid}")
        if not store.scopes.is_visible(pj.scope, proposal.scope):
            return Refused(Reason.FRAGMENT,
                           f"premise {pid} is not visible in scope {proposal.scope}")
        inherited.extend(pj.requirements)
        premise_props.append(pj.proposition)
    # The checker sees only the kernel-resolved premise propositions. The
    # public proposal remains unchanged and carries no trusted premise data.
    resolved = ResolvedProposal(
        scope=proposal.scope,
        evidence=proposal.evidence,
        premises=proposal.premises,
        conclusions=proposal.conclusions,
        guard_policy=proposal.guard_policy,
        premise_propositions=tuple(premise_props),
    )

    # --- 3. checker ---
    checker = store.checkers.get(proposal.evidence.checker_id)
    if checker is None:
        return Undecided(Reason.FRAGMENT,
                         f"checker not registered: {proposal.evidence.checker_id}")

    result = checker.check(resolved, ctx, selected_services)
    if isinstance(result, RefutationRejected):
        return Refused(
            result.reason,
            result.detail,
            refutation=result.refutation,
        )
    if isinstance(result, Rejected):
        return Refused(result.reason, result.detail)
    if isinstance(result, UnknownResult):
        return Undecided(result.reason, result.detail or "conclusion not re-checked")
    if not isinstance(result, Accepted):
        raise TypeError("checker returned an unsupported result")
    direct = result.direct_requirements

    # --- 5/6. condition collection and discharge attempt (Proved / Refuted /
    #          Unknown) ---
    proved_terms: list[Term] = []
    for term in direct:
        verdict = ctx.decide(term)
        if verdict.is_yes():
            proved_terms.append(term)
        elif isinstance(verdict, No):
            return Refused(
                Reason.GUARDED,
                f"condition refuted: {term!r}; {verdict.evidence.detail}",
                refutation=verdict.evidence,
            )
        else:
            if not isinstance(verdict, Unknown):
                raise TypeError("decision service returned a non-decision verdict")
            if proposal.guard_policy is GuardPolicy.REQUIRE_PROVED:
                return Undecided(
                    verdict.reason,
                    f"condition undecided, REQUIRE_PROVED refuses to land: {term!r}",
                )
            if proposal.guard_policy is GuardPolicy.REQUEST_SPLIT:
                return NeedsSplit((term,))

    for rid in inherited:
        if store.is_refuted(rid, proposal.scope):
            return Refused(Reason.GUARDED, f"premise condition already refuted: {rid}")

    # --- 10. atomic write ---
    step_id = store.new_step_id()

    direct_ids: dict[Term, RequirementId] = {}
    all_req = list(inherited)
    for t in direct:
        rid = store.new_requirement_id()
        store.put_requirement(Requirement(
            id=rid, scope=proposal.scope, proposition=t,
            introduced_by=step_id, reason=RequirementReason.RULE_GUARD))
        direct_ids[t] = rid
        all_req.append(rid)
    # A conclusion depends on all direct and inherited conditions; whether they
    # are discharged is a separate matter (discharge does not modify the
    # original conclusion, it only makes queries report direct applicability).
    carried = tuple(inherited) + tuple(direct_ids[t] for t in direct)

    jids: list[JudgmentId] = []
    for prop in proposal.conclusions:
        jid = store.new_judgment_id()
        store.put_judgment(Judgment(
            id=jid, scope=proposal.scope, proposition=prop,
            requirements=carried, producer=step_id))
        jids.append(jid)
    step_reads = ctx.read_set(dedupe=not selected_mode.raw_reads())
    if inherited_reads is not None:
        # Inherited read dependencies, e.g. a branch merge whose conclusion
        # depends on facts read in each branch. Merging and deduplication
        # follow read_set; granularity is still decided by the mode.
        step_reads = inherited_reads.merge(step_reads)
    store.put_step(Step(id=step_id, scope=proposal.scope,
                        premises=tuple(proposal.premises),
                        conclusions=tuple(jids),
                        evidence=proposal.evidence,
                        # Read dependencies come from the TrackedContext record;
                        # granularity follows the mode, so audit keeps every
                        # occurrence.
                        reads=step_reads))

    # --- 7. Proved -> record the discharge basis ---
    # interactive defers discharge registration: conditions are still decided
    # above (otherwise a refuted guard would slip through), but a proved
    # condition is not recorded as a Discharge yet.
    if not selected_mode.defers_discharge():
        for term in proved_terms:
            decided = _commit_decided(
                store, proposal.scope, term, ctx, selected_services,
                discharge_checker_id, selected_mode,
            )
            if decided is not None:
                store.add_discharge(Discharge(
                    requirement=direct_ids[term],
                    by_judgment=decided,
                    scope=proposal.scope,
                ))

    # 10d. refutation registration: when a conclusion is exactly the negation
    # of a pending condition, mark the original conclusion Inapplicable
    # without deleting it.
    for jid, prop in zip(jids, proposal.conclusions):
        _record_refutations(store, proposal.scope, prop, jid)

    return Committed(step=step_id, judgments=tuple(jids),
                     requirements=tuple(all_req), reads=step_reads)


def _commit_decided(
    store: KernelStore,
    scope: ScopeId,
    proposition: Term,
    ctx: TrackedContext,
    services: KernelServices,
    checker_id: str,
    mode: ExecutionMode | None = None,
) -> JudgmentId | None:
    """Land an already-decided condition through the same protocol, to serve as
    a discharge basis.

    Recursion-safe: the decide checker accepts no direct conditions, so it can
    never trigger discharge again.
    """
    if store.checkers.get(checker_id) is None:
        return None
    prop = StepProposal(scope=scope, premises=(), conclusions=(proposition,),
                        evidence=Evidence(checker_id, proposition),
                        guard_policy=GuardPolicy.REQUIRE_PROVED)
    res = commit(store, prop, context=ctx, services=services,
                 discharge_checker_id=checker_id, mode=mode)
    return res.judgments[0] if isinstance(res, Committed) else None


def _record_refutations(
    store: KernelStore,
    scope: ScopeId,
    proposition: Term,
    jid: JudgmentId,
) -> None:
    """When a conclusion is the syntactic negation of a pending condition,
    register a refutation. Syntactic negation only, no semantic guessing.

    Candidates come from the store's reverse index over requirement
    propositions, so no scan over the whole ledger happens per commit.
    """
    for rid in store.requirements_refuted_by(proposition):
        if store.is_discharged(rid, scope):
            continue
        store.add_refutation(rid, jid)
