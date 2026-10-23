"""Validate conditional propositions and publish one complete ledger batch."""

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
from cas.syntax.term import Term, is_proposition
from cas.syntax.termpath import well_scoped


class GuardPolicy(Enum):
    REQUIRE_PROVED = "require_proved"
    ALLOW_CONDITIONAL = "allow_conditional"
    REQUEST_SPLIT = "request_split"


@dataclass(frozen=True, slots=True)
class StepProposal:
    scope: ScopeId
    evidence: Evidence
    premises: tuple[JudgmentId, ...] = ()
    conclusions: tuple[Term, ...] = ()
    guard_policy: GuardPolicy = GuardPolicy.REQUIRE_PROVED


@dataclass(frozen=True, slots=True)
class ResolvedProposal:
    scope: ScopeId
    evidence: Evidence
    premises: tuple[JudgmentId, ...]
    conclusions: tuple[Term, ...]
    guard_policy: GuardPolicy
    premise_propositions: tuple[Term, ...]


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
    reason: Reason = Reason.FRAGMENT
    detail: str = ""
    refutation: Refutation | None = None


@dataclass(frozen=True, slots=True)
class Undecided(CommitResult):
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


@dataclass(frozen=True, slots=True)
class NeedsSplit(CommitResult):
    conditions: tuple[Term, ...] = ()


def commit(
    store: KernelStore,
    proposal: StepProposal,
    context: TrackedContext | None = None,
    services: KernelServices | None = None,
    discharge_checker_id: str = "kernel.decide",
    mode: ExecutionMode | None = None,
    inherited_reads: ContextReadSet | None = None,
) -> CommitResult:
    try:
        return _commit_checked(
            store, proposal, context, services, discharge_checker_id, mode, inherited_reads
        )
    except BudgetExceeded as error:
        return Undecided(Reason.BUDGET, f"budget exhausted during commit: {error}")


def _commit_checked(
    store: KernelStore,
    proposal: StepProposal,
    context: TrackedContext | None,
    services: KernelServices | None,
    discharge_checker_id: str,
    mode: ExecutionMode | None,
    inherited_reads: ContextReadSet | None,
) -> CommitResult:
    selected_mode = DEFAULT_MODE if mode is None else mode
    selected_services: KernelServices = NullServices() if services is None else services
    try:
        store.scopes.get(proposal.scope)
    except KeyError:
        return Refused(Reason.FRAGMENT, f"scope does not exist: {proposal.scope}")
    if not isinstance(proposal.guard_policy, GuardPolicy):
        return Refused(Reason.FRAGMENT, "invalid guard policy")
    if not proposal.conclusions:
        return Refused(Reason.FRAGMENT, "a submission needs a proposition")
    if context is not None and not context.matches(store.scopes, selected_services, proposal.scope):
        return Refused(Reason.FRAGMENT, "verification context does not match the submission")
    ctx = TrackedContext(store.scopes, selected_services, proposal.scope, selected_mode)
    for proposition in proposal.conclusions:
        if not is_proposition(proposition) or not well_scoped(proposition):
            return Refused(Reason.FRAGMENT, "conclusion is not a well-bound proposition")
        if store.scopes.escapes(proposal.scope, proposition):
            return Refused(Reason.FRAGMENT, "a local symbol escapes in the conclusion")
    if not selected_services.supports_scope(proposal.scope):
        return Undecided(Reason.FRAGMENT, "the mathematical services do not interpret this scope's declarations")

    inherited: list[RequirementId] = []
    premise_props: list[Term] = []
    for identifier in proposal.premises:
        try:
            premise = store.get_judgment(identifier)
        except KeyError:
            return Refused(Reason.FRAGMENT, f"premise does not exist: {identifier}")
        if not store.scopes.is_visible(premise.scope, proposal.scope):
            return Refused(Reason.FRAGMENT, "premise is outside the submission scope")
        inherited.extend(premise.requirements)
        premise_props.append(premise.proposition)
    inherited = list(dict.fromkeys(inherited))
    resolved = ResolvedProposal(
        proposal.scope, proposal.evidence, proposal.premises, proposal.conclusions,
        proposal.guard_policy, tuple(premise_props),
    )
    checker = store.checkers.get(proposal.evidence.checker_id)
    if checker is None:
        return Undecided(Reason.FRAGMENT, f"checker not registered: {proposal.evidence.checker_id}")
    result = checker.check(resolved, ctx, selected_services)
    if isinstance(result, RefutationRejected):
        return Refused(result.reason, result.detail, result.refutation)
    if isinstance(result, Rejected):
        return Refused(result.reason, result.detail)
    if isinstance(result, UnknownResult):
        return Undecided(result.reason, result.detail or "conclusion not re-checked")
    if not isinstance(result, Accepted):
        raise TypeError("checker returned an unsupported result")

    required: dict[Term, list[RequirementId]] = {}
    for requirement_id in inherited:
        if store.is_refuted(requirement_id, proposal.scope):
            return Refused(Reason.GUARDED, "an inherited condition has been refuted")
        requirement = store.get_requirement(requirement_id)
        required.setdefault(requirement.proposition, []).append(requirement_id)
    for condition in result.direct_requirements:
        required.setdefault(condition, [])
    for proposition in proposal.conclusions:
        definedness = selected_services.definedness(proposition, proposal.scope)
        if definedness is None:
            return Undecided(Reason.FRAGMENT, "definedness analysis unavailable")
        for condition in definedness:
            required.setdefault(condition, [])

    dependencies: dict[Term, tuple[Term, ...]] = {}
    pending = list(required)
    while pending:
        condition = pending.pop()
        if condition in dependencies:
            continue
        if not is_proposition(condition) or not well_scoped(condition):
            return Refused(Reason.FRAGMENT, "checker produced an invalid condition")
        if store.scopes.escapes(proposal.scope, condition):
            return Refused(Reason.FRAGMENT, "a local symbol escapes in a condition")
        definedness = selected_services.definedness(condition, proposal.scope)
        if definedness is None:
            return Undecided(Reason.FRAGMENT, "condition definedness unavailable")
        dependencies[condition] = definedness
        for prerequisite in definedness:
            required.setdefault(prerequisite, [])
            if prerequisite not in dependencies:
                pending.append(prerequisite)

    proved: set[Term] = set()
    for condition, identifiers in required.items():
        verdict = ctx.decide(condition)
        if isinstance(verdict, No):
            return Refused(Reason.GUARDED, f"condition refuted: {condition!r}", verdict.evidence)
        if verdict.is_yes() or any(store.is_discharged(rid, proposal.scope) for rid in identifiers):
            proved.add(condition)
            continue
        if not isinstance(verdict, Unknown):
            raise TypeError("decision service returned an unsupported verdict")
        if proposal.guard_policy is GuardPolicy.REQUIRE_PROVED:
            return Undecided(verdict.reason, f"condition undecided: {condition!r}")
        if proposal.guard_policy is GuardPolicy.REQUEST_SPLIT:
            return NeedsSplit((condition,))

    closed: set[Term] = set()
    while True:
        newly_closed = {term for term in proved - closed if all(dep in closed for dep in dependencies[term])}
        if not newly_closed:
            break
        closed.update(newly_closed)
    unresolved = tuple(term for term in required if term not in closed)
    if unresolved and proposal.guard_policy is GuardPolicy.REQUIRE_PROVED:
        return Undecided(Reason.GUARDED, "condition support is not closed")
    if unresolved and proposal.guard_policy is GuardPolicy.REQUEST_SPLIT:
        return NeedsSplit(unresolved)

    direct_ids: dict[Term, RequirementId] = {}
    for condition, identifiers in required.items():
        if not identifiers:
            requirement_id = store.new_requirement_id()
            direct_ids[condition] = requirement_id
            identifiers.append(requirement_id)
    carried = tuple(identifier for identifiers in required.values() for identifier in identifiers)
    judgments: list[Judgment] = []
    steps: list[Step] = []
    discharges: list[Discharge] = []
    discharge_checker = store.checkers.get(discharge_checker_id)
    for condition in required:
        if condition not in closed:
            continue
        discharge_ids = tuple(rid for rid in required[condition] if not store.is_discharged(rid, proposal.scope))
        if not discharge_ids:
            continue
        if discharge_checker is None:
            return Undecided(Reason.FRAGMENT, "condition proof checker is not registered")
        evidence = Evidence(discharge_checker_id, condition)
        proof = ResolvedProposal(
            proposal.scope, evidence, (), (condition,), GuardPolicy.REQUIRE_PROVED, (),
        )
        checked = discharge_checker.check(proof, ctx, selected_services)
        if not isinstance(checked, Accepted) or checked.direct_requirements:
            return Undecided(Reason.GUARDED, "a condition proof could not be independently closed")
        proof_step = store.new_step_id()
        proof_judgment = store.new_judgment_id()
        judgments.append(Judgment(proof_judgment, proposal.scope, condition, (), proof_step))
        steps.append(Step(proof_step, proposal.scope, (), (proof_judgment,), evidence, ctx.read_set()))
        discharges.extend(Discharge(rid, proof_judgment, proposal.scope) for rid in discharge_ids)

    step_id = store.new_step_id()
    requirements = tuple(
        Requirement(identifier, proposal.scope, term, step_id, RequirementReason.RULE_GUARD)
        for term, identifier in direct_ids.items()
    )
    conclusion_ids: list[JudgmentId] = []
    for proposition in proposal.conclusions:
        identifier = store.new_judgment_id()
        judgments.append(Judgment(identifier, proposal.scope, proposition, carried, step_id))
        conclusion_ids.append(identifier)
    reads = ctx.read_set(dedupe=not selected_mode.raw_reads())
    if inherited_reads is not None:
        reads = inherited_reads.merge(reads)
    steps.append(Step(step_id, proposal.scope, proposal.premises, tuple(conclusion_ids), proposal.evidence, reads))
    refutations = tuple(
        (rid, identifier)
        for identifier, proposition in zip(conclusion_ids, proposal.conclusions)
        for rid in store.requirements_refuted_by(proposition)
        if not unresolved
    )
    store.publish(requirements, tuple(judgments), tuple(steps), tuple(discharges), refutations)
    return Committed(step_id, tuple(conclusion_ids), carried, reads)
