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

from dataclasses import dataclass, field, replace
from enum import Enum

from cas.kernel.context import TrackedContext
from cas.kernel.evidence import Evidence
from cas.kernel.ids import StepId
from cas.kernel.model import (
    ContextReadSet, Discharge, Judgment, Requirement, RequirementReason, Step,
)
from cas.kernel.services import NullServices
from cas.kernel.verdict import Reason


class GuardPolicy(Enum):
    """Guard policy. How Unknown is handled is the one switch that may never be
    turned off."""
    REQUIRE_PROVED = "require_proved"        # automatic simplification default: undecided does not land
    ALLOW_CONDITIONAL = "allow_conditional"  # explicit manual application: land with conditions
    REQUEST_SPLIT = "request_split"          # ask for a case split


@dataclass(frozen=True, slots=True)
class StepProposal:
    scope: object
    premises: tuple = ()
    conclusions: tuple = ()
    evidence: Evidence = None
    guard_policy: GuardPolicy = GuardPolicy.REQUIRE_PROVED
    # Filled in by commit after resolving premises; a checker may read only
    # this and must never trust premises reported by the caller.
    premise_propositions: tuple = field(default=())


# ---------------------------------------------------------------------------
# Commit results: a closed hierarchy, so consumers must exhaust the branches
# ---------------------------------------------------------------------------

class CommitResult:
    __slots__ = ()

    def is_committed(self):
        return self.__class__ is Committed

    def is_refused(self):
        return self.__class__ is Refused

    def is_undecided(self):
        return self.__class__ is Undecided

    def is_needs_split(self):
        return self.__class__ is NeedsSplit


@dataclass(frozen=True, slots=True)
class Committed(CommitResult):
    step: StepId
    judgments: tuple
    requirements: tuple
    reads: ContextReadSet = field(default_factory=ContextReadSet)


@dataclass(frozen=True, slots=True)
class Refused(CommitResult):
    """The conclusion does not hold, a premise is inaccessible, or a condition
    was refuted: this application is inapplicable."""
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


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
    conditions: tuple = ()


# ---------------------------------------------------------------------------
# Commit
# ---------------------------------------------------------------------------

def commit(store, proposal, context=None, services=None,
           discharge_checker_id="kernel.decide",
           mode=None, inherited_reads=None) -> CommitResult:
    from cas.kernel.mode import DEFAULT_MODE
    mode = mode if mode is not None else DEFAULT_MODE
    services = services if services is not None else NullServices()

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
    ctx = context if context is not None \
        else TrackedContext(store.scopes, services, proposal.scope, mode)

    # --- 2. premise visibility (a child conclusion may not be used upward;
    #        sibling branches cannot see each other) ---
    inherited = []
    premise_props = []
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
    # Back-fill premise propositions: anything the caller reported is discarded
    # and the checker reads only what the kernel resolved.
    proposal = replace(proposal, premise_propositions=tuple(premise_props))

    # --- 3. checker ---
    checker = store.checkers.get(proposal.evidence.checker_id)
    if checker is None:
        return Undecided(Reason.FRAGMENT,
                         f"checker not registered: {proposal.evidence.checker_id}")

    # --- 4. re-check ---
    result = checker.check(proposal, ctx, services)
    if result.is_rejected():
        return Refused(result.reason, result.detail)

    # The checker could not re-check the conclusion: the candidate is
    # unverified and lands under no policy. GuardPolicy governs undecided
    # *condition discharge* below, not "let an unverified conclusion through".
    if result.is_unknown():
        return Undecided(result.reason, result.detail or "conclusion not re-checked")

    direct = tuple(result.direct_requirements) if result.is_accepted() else ()

    # --- 5/6. condition collection and discharge attempt (Proved / Refuted /
    #          Unknown) ---
    proved_terms = []
    for t in direct:
        v = ctx.decide(t)
        if v.is_yes():
            proved_terms.append(t)                    # 7. Proved
        elif v.is_no():
            return Refused(Reason.GUARDED, f"condition refuted: {t!r}")   # 8. Refuted
        else:
            # 9. Unknown -> handle by guard policy
            if proposal.guard_policy is GuardPolicy.REQUIRE_PROVED:
                return Undecided(v.reason,
                                 f"condition undecided, REQUIRE_PROVED refuses to land: {t!r}")
            if proposal.guard_policy is GuardPolicy.REQUEST_SPLIT:
                return NeedsSplit((t,))

    for rid in inherited:
        if store.is_refuted(rid, proposal.scope):
            return Refused(Reason.GUARDED, f"premise condition already refuted: {rid}")

    # --- 10. atomic write ---
    step_id = store.new_step_id()

    direct_ids = {}
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

    jids = []
    for prop in proposal.conclusions:
        jid = store.new_judgment_id()
        store.put_judgment(Judgment(
            id=jid, scope=proposal.scope, proposition=prop,
            requirements=carried, producer=step_id))
        jids.append(jid)

    step_reads = ctx.read_set(dedupe=not mode.raw_reads())
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
    if not mode.defers_discharge():
        for t in proved_terms:
            dj = _commit_decided(store, proposal.scope, t, ctx, services,
                                 discharge_checker_id, mode)
            if dj is not None:
                store.add_discharge(Discharge(requirement=direct_ids[t],
                                              by_judgment=dj,
                                              scope=proposal.scope))

    # 10d. refutation registration: when a conclusion is exactly the negation
    # of a pending condition, mark the original conclusion Inapplicable
    # without deleting it.
    for jid, prop in zip(jids, proposal.conclusions):
        _record_refutations(store, proposal.scope, prop, jid)

    return Committed(step=step_id, judgments=tuple(jids),
                     requirements=tuple(all_req), reads=step_reads)


def _commit_decided(store, scope, proposition, ctx, services, checker_id,
                    mode=None):
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
    return res.judgments[0] if res.is_committed() else None


def _record_refutations(store, scope, proposition, jid):
    """When a conclusion is the syntactic negation of a pending condition,
    register a refutation. Syntactic negation only, no semantic guessing.

    Candidates come from the store's reverse index over requirement
    propositions, so no scan over the whole ledger happens per commit.
    """
    for rid in store.requirements_refuted_by(proposition):
        if store.is_discharged(rid, scope):
            continue
        store.add_refutation(rid, jid)
