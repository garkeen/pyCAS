"""Commit: exact checker specifications, conditions and atomic publication."""

from dataclasses import replace
from typing import cast

import pytest
from support import (
    commit_now,
    equation,
    head_app,
    runtime_proposition,
    typed_in,
    variable,
)

from cas.foundation.ids import (
    FrameId,
    InferenceId,
    JudgmentId,
    ObligationId,
    WorldId,
)
from cas.kernel.commit import (
    CommitProposal,
    Committed,
    Deferred,
    Rejected,
    RejectedKind,
    ValidatedCommitBatch,
    validate_commit,
)
from cas.kernel.evidence import (
    AlgebraService,
    BudgetService,
    CheckerRegistry,
    CheckerSpec,
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
from cas.kernel.model import Judgment, ObligationReason
from cas.kernel.store import KernelStore
from cas.kernel.trust import (
    BasisKind,
    BasisRef,
    BasisRegistry,
    CertificateSchema,
)
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.execution import (
    BudgetTicket,
    ConditionPolicy,
    ExecutionBudget,
)
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import bootstrap, new_workspace
from cas.semantics.frames import Declaration
from cas.syntax import term as T


class StubChecker:
    id = "test.checker"
    version = "7"

    def __init__(self):
        self.outcome = None
        self.requests = []

    def check(self, request):
        self.requests.append(request)
        return self.outcome


def setup(runtime):
    checker = StubChecker()
    registration = CheckerSpec(
        checker,
        CertificateSchema("test", "1", str),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        runtime.world.id,
    )
    store = KernelStore(
        runtime.frames, CheckerRegistry({checker.id: registration})
    )
    return store, checker


def conclusion(runtime, value: int = 1):
    return equation(runtime, variable(runtime), T.number(value))


def proposal(runtime, proposition, **overrides):
    values = dict(
        frame=runtime.frame.id,
        conclusions=(proposition,),
        checker_id="test.checker",
        problem_kind="test.problem",
        specification_kind="test.specification",
        certificate="certificate",
    )
    values.update(overrides)
    return CommitProposal(**values)


def assert_empty(store: KernelStore) -> None:
    assert store.stats()["obligations"] == 0
    assert store.stats()["judgments"] == 0
    assert store.stats()["inferences"] == 0
    assert store.stats()["discharges"] == 0


def test_a_verified_submission_is_published_once(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Committed)
    judgment = store.get_judgment(result.judgments[0])
    assert judgment.proposition == proposition
    assert judgment.frame == runtime.frame.id
    assert judgment.obligations == ()
    inference = store.inference_of(judgment.id)
    assert inference.checker_id == "test.checker"
    assert inference.checker_version == "7"
    assert inference.certificate == "certificate"
    assert inference.premises == ()
    assert store.applicability(judgment.id, runtime.frame.id).is_applicable()
    request = checker.requests[0]
    assert request.frame == runtime.frame.id
    assert request.conclusions == (proposition,)
    assert request.certificate == "certificate"
    assert request.candidate is None


def test_validate_commit_builds_the_verification_context(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Committed)
    context = checker.requests[0].context
    assert isinstance(context, VerificationContext)
    assert context.world == runtime.world.id
    assert context.frame == runtime.frame.id
    assert context.frames is runtime.frames
    assert isinstance(context.decision, DecisionService)
    assert isinstance(context.supports, SupportsService)
    assert isinstance(context.budget, BudgetService)
    assert context.budget.budget is None


def test_validate_commit_populates_the_definedness_service(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Committed)
    context = checker.requests[0].context
    service = context.definedness
    assert isinstance(service, DefinednessService)
    assert service.decision is context.decision
    assert service.frames is runtime.frames
    assert service.frame == runtime.frame.id
    region = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )
    stronger = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(1),
        ),
    )
    assert service.covers(stronger, region) is True
    assert service.covers(region, stronger) is None


def test_validate_commit_populates_the_context_services(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    budget = ExecutionBudget(max_nodes=100, max_depth=10)
    result = commit_now(store, proposal(runtime, proposition, budget=budget))
    assert isinstance(result, Committed)
    context = checker.requests[0].context
    assert isinstance(context, VerificationContext)
    assert isinstance(context.decision, DecisionService)
    assert isinstance(context.supports, SupportsService)
    assert isinstance(context.budget, BudgetService)
    assert context.budget.budget is budget
    assert context.decision.is_subregion(T.TRUE, T.TRUE) is True
    judgment = store.get_judgment(result.judgments[0])
    assert context.supports.judgment(result.judgments[0]) is judgment
    assert judgment in context.supports.visible(runtime.frame.id)
    assert not context.supports.is_discharged(
        ObligationId(10_000), runtime.frame.id
    )
    with pytest.raises(KeyError):
        context.supports.judgment(JudgmentId(10_000))


def test_validate_commit_populates_the_budget_ticket(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    budget = ExecutionBudget(max_nodes=100, max_depth=10)
    result = commit_now(store, proposal(runtime, proposition, budget=budget))
    assert isinstance(result, Committed)
    service = checker.requests[0].context.budget
    assert isinstance(service, BudgetService)
    assert service.budget is budget
    assert isinstance(service.ticket, BudgetTicket)
    assert service.ticket.budget == budget
    assert service.ticket.consumed_nodes == 0
    assert service.ticket.consumed_depth == 0


def test_validate_commit_populates_the_algebra_service(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store, proposal(runtime, proposition, algebra=runtime.request)
    )
    assert isinstance(result, Committed)
    service = checker.requests[0].context.algebra
    assert isinstance(service, AlgebraService)
    assert service.request is runtime.request


def derivative_candidate(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "x")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    return result.candidate


def derivative_proposal(candidate, *, algebra):
    return CommitProposal(
        candidate.frame,
        candidate.specifications,
        candidate.checker_id,
        candidate.problem.operation,
        candidate.specification_kind,
        certificate=candidate.certificate,
        problem=candidate.problem,
        candidate=candidate.term,
        candidate_role=candidate.candidate_role,
        algebra=algebra,
    )


def test_a_derivative_proposal_needs_the_candidate_algebra_request(runtime):
    candidate = derivative_candidate(runtime)
    assert candidate.algebra is runtime.request
    accepted = validate_commit(
        runtime.store,
        derivative_proposal(candidate, algebra=candidate.algebra),
    )
    assert isinstance(accepted, ValidatedCommitBatch)
    missing = validate_commit(
        runtime.store, derivative_proposal(candidate, algebra=None)
    )
    assert isinstance(missing, Rejected)
    assert missing.kind is RejectedKind.INVALID_EVIDENCE
    assert "no fixed algebra request" in missing.detail
    forged = validate_commit(
        runtime.store,
        derivative_proposal(candidate, algebra=replace(runtime.request)),
    )
    assert isinstance(forged, Rejected)
    assert forged.kind is RejectedKind.INVALID_EVIDENCE
    assert "does not match the checker request" in forged.detail


def test_a_commit_algebra_request_must_be_an_algebra_request(runtime):
    with pytest.raises(TypeError):
        proposal(runtime, conclusion(runtime), algebra="algebra")


def test_validate_commit_passes_the_candidate_to_the_checker(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    candidate = T.number(1)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store, proposal(runtime, proposition, candidate=candidate)
    )
    assert isinstance(result, Committed)
    assert checker.requests[0].candidate is candidate


def test_validate_commit_passes_the_candidate_role_to_the_checker(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store,
        proposal(
            runtime,
            proposition,
            candidate=T.number(1),
            candidate_role=CandidateRole.RESULT,
        ),
    )
    assert isinstance(result, Committed)
    assert checker.requests[0].candidate_role is CandidateRole.RESULT


def test_a_commit_candidate_role_must_be_a_candidate_role(runtime):
    proposition = conclusion(runtime)
    with pytest.raises(TypeError):
        proposal(
            runtime,
            proposition,
            candidate=T.number(1),
            candidate_role="result",
        )


def test_a_commit_candidate_must_be_a_term(runtime):
    proposition = conclusion(runtime)
    with pytest.raises(TypeError):
        proposal(
            runtime,
            proposition,
            candidate=cast(T.Term, object()),
        )


def test_an_oversized_certificate_is_rejected_before_the_checker(runtime):
    checker = StubChecker()
    registration = CheckerSpec(
        checker,
        CertificateSchema("test", "1", tuple, max_nodes=3),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        runtime.world.id,
    )
    store = KernelStore(
        runtime.frames, CheckerRegistry({checker.id: registration})
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store,
        proposal(runtime, proposition, certificate=(1, 2, 3, 4)),
    )
    assert isinstance(result, Rejected)
    assert "budget" in result.detail
    assert checker.requests == []
    assert_empty(store)


def test_an_execution_budget_can_tighten_the_schema_budget(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    assert isinstance(commit_now(store, proposal(runtime, proposition)), Committed)
    assert isinstance(
        commit_now(
            store,
            proposal(
                runtime,
                proposition,
                budget=ExecutionBudget(max_nodes=100),
            ),
        ),
        Committed,
    )
    requests = len(checker.requests)
    result = commit_now(
        store,
        proposal(
            runtime,
            proposition,
            budget=ExecutionBudget(max_nodes=3),
        ),
    )
    assert isinstance(result, Rejected)
    assert "execution budget" in result.detail
    assert len(checker.requests) == requests


def test_a_commit_budget_must_be_an_execution_budget(runtime):
    with pytest.raises(TypeError):
        proposal(
            runtime,
            conclusion(runtime),
            budget="small",
        )


def test_a_checker_from_another_world_is_rejected(runtime):
    checker = StubChecker()
    registration = CheckerSpec(
        checker,
        CertificateSchema("test", "1", str),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        WorldId(runtime.world.id + 1),
    )
    store = KernelStore(
        runtime.frames, CheckerRegistry({checker.id: registration})
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert "world" in result.detail
    assert_empty(store)


def test_a_commit_policy_must_be_a_condition_policy(runtime):
    with pytest.raises(TypeError):
        proposal(
            runtime,
            conclusion(runtime),
            policy="allow_conditional",
        )
    with pytest.raises(TypeError):
        proposal(
            runtime,
            conclusion(runtime),
            conclusions=(T.number(1),),
        )
    with pytest.raises(ValueError):
        proposal(runtime, conclusion(runtime), checker_id="")


def test_a_checker_must_have_verified_exactly_the_request(runtime):
    store, checker = setup(runtime)
    checker.outcome = Verified((conclusion(runtime, 2),))
    result = commit_now(store, proposal(runtime, conclusion(runtime, 1)))
    assert isinstance(result, Rejected)
    assert "different specification" in result.detail
    assert_empty(store)


def test_an_unverified_submission_is_deferred_without_writing(runtime):
    store, checker = setup(runtime)
    checker.outcome = Unverified(Reason.FRAGMENT, "outside the fragment")
    result = commit_now(store, proposal(runtime, conclusion(runtime)))
    assert isinstance(result, Deferred)
    assert result.reason is Reason.FRAGMENT
    assert result.detail == "outside the fragment"
    assert result.missing == frozenset()
    assert result.conditions == ()
    assert_empty(store)


def test_an_unverified_submission_preserves_missing_and_conditions(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    condition = conclusion(runtime, 0)
    checker.outcome = Unverified(
        Reason.FRAGMENT,
        "the checker lacks a capability",
        missing={"capability"},
        conditions=(condition,),
    )
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Deferred)
    assert result.reason is Reason.FRAGMENT
    assert result.detail == "the checker lacks a capability"
    assert result.missing == frozenset({"capability"})
    assert result.conditions == (condition,)
    assert_empty(store)


def test_deferred_validates_its_missing_capabilities():
    with pytest.raises(TypeError):
        Deferred(Reason.FRAGMENT, "detail", missing=frozenset({""}))
    with pytest.raises(TypeError):
        Deferred(
            Reason.FRAGMENT,
            "detail",
            missing=frozenset({1}),  # type: ignore[arg-type]
        )


def test_invalid_evidence_is_not_a_refutation(runtime):
    store, checker = setup(runtime)
    checker.outcome = InvalidEvidence("malformed certificate")
    result = commit_now(store, proposal(runtime, conclusion(runtime)))
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_EVIDENCE
    assert result.refutation is None
    assert "invalid evidence" in result.detail
    assert_empty(store)


def test_a_refutation_is_rejected_with_its_witnesses(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    refutation = Refuted(proposition, (T.number(1),), "the candidate differs")
    checker.outcome = refutation
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.REFUTED_SPECIFICATION
    assert result.refutation is refutation
    assert result.refutation.witnesses == (T.number(1),)
    assert_empty(store)


def test_an_unregistered_checker_defers(runtime):
    store, _ = setup(runtime)
    result = commit_now(
        store, proposal(runtime, conclusion(runtime), checker_id="missing")
    )
    assert isinstance(result, Deferred)
    assert result.reason is Reason.FRAGMENT
    assert_empty(store)


def test_a_submission_needs_a_conclusion(runtime):
    store, _ = setup(runtime)
    result = commit_now(store, proposal(runtime, conclusion(runtime), conclusions=()))
    assert isinstance(result, Rejected)
    assert "at least one conclusion" in result.detail
    assert_empty(store)


def test_a_missing_frame_is_rejected(runtime):
    store, _ = setup(runtime)
    result = commit_now(
        store, proposal(runtime, conclusion(runtime), frame=FrameId(10_000))
    )
    assert isinstance(result, Rejected)
    assert "frame" in result.detail
    assert_empty(store)


def test_an_unsupported_checker_outcome_is_rejected(runtime):
    store, checker = setup(runtime)
    checker.outcome = object()
    result = commit_now(store, proposal(runtime, conclusion(runtime)))
    assert isinstance(result, Rejected)
    assert "unsupported outcome" in result.detail
    assert_empty(store)


def test_missing_premises_are_rejected_before_the_checker_runs(runtime):
    store, checker = setup(runtime)
    result = commit_now(
        store,
        proposal(runtime, conclusion(runtime), premises=(JudgmentId(10_000),)),
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_REQUEST
    assert "premise does not exist" in result.detail
    assert checker.requests == []
    assert_empty(store)


def test_a_premise_from_a_child_frame_is_out_of_scope_in_the_parent(runtime):
    store, checker = setup(runtime)
    child = runtime.frames.create(runtime.frame.id)
    child_proposition = equation(
        runtime, variable(runtime), T.number(1), child.id
    )
    checker.outcome = Verified((child_proposition,))
    first = commit_now(
        store, proposal(runtime, child_proposition, frame=child.id)
    )
    assert isinstance(first, Committed)
    checker.outcome = Verified((conclusion(runtime),))
    result = commit_now(
        store, proposal(runtime, conclusion(runtime), premises=first.judgments)
    )
    assert isinstance(result, Rejected)
    assert "premise is outside" in result.detail
    assert store.stats()["judgments"] == 1


def test_an_ancestor_premise_is_visible_and_is_resolved_for_the_checker(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    first = commit_now(store, proposal(runtime, proposition))
    assert isinstance(first, Committed)
    child = runtime.frames.create(runtime.frame.id)
    child_proposition = equation(
        runtime, variable(runtime), T.number(2), child.id
    )
    checker.outcome = Verified(
        (child_proposition,), used_premises=(0,)
    )
    second = commit_now(
        store,
        proposal(
            runtime,
            child_proposition,
            frame=child.id,
            premises=first.judgments,
        ),
    )
    assert isinstance(second, Committed)
    assert checker.requests[-1].premises == (proposition,)
    assert store.inference_of(second.judgments[0]).premises == first.judgments


def test_a_conclusion_read_in_another_frame_is_rejected(runtime):
    store, checker = setup(runtime)
    child = runtime.frames.create(runtime.frame.id)
    child_proposition = equation(
        runtime, variable(runtime), T.number(1), child.id
    )
    checker.outcome = Verified((child_proposition,))
    result = commit_now(store, proposal(runtime, child_proposition))
    assert isinstance(result, Rejected)
    assert "outside the submission" in result.detail
    assert_empty(store)


def test_open_conditions_follow_the_policy(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    deferred = commit_now(store, proposal(runtime, proposition))
    assert isinstance(deferred, Deferred)
    assert deferred.reason is Reason.GUARDED
    assert deferred.conditions == (condition,)
    assert_empty(store)

    cases = commit_now(
        store,
        proposal(runtime, proposition, policy=ConditionPolicy.REQUEST_CASES),
    )
    assert isinstance(cases, Deferred)
    assert cases.reason is Reason.GUARDED
    assert cases.conditions == (condition,)
    assert_empty(store)

    committed = commit_now(
        store,
        proposal(
            runtime, proposition, policy=ConditionPolicy.ALLOW_CONDITIONAL
        ),
    )
    assert isinstance(committed, Committed)
    assert len(committed.obligations) == 1
    judgment = store.get_judgment(committed.judgments[0])
    assert judgment.obligations == committed.obligations
    obligation = store.get_obligation(committed.obligations[0])
    assert obligation.proposition == condition
    assert obligation.reason is ObligationReason.DEFINEDNESS
    assert obligation.frame == runtime.frame.id
    application = store.applicability(judgment.id, runtime.frame.id)
    assert application.is_conditional()
    assert application.obligations == committed.obligations


def test_discharging_the_condition_makes_the_judgment_applicable(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    committed = commit_now(
        store,
        proposal(
            runtime, proposition, policy=ConditionPolicy.ALLOW_CONDITIONAL
        ),
    )
    assert isinstance(committed, Committed)
    checker.outcome = Verified((condition,))
    proof = commit_now(
        store,
        proposal(
            runtime,
            condition,
            discharge_obligations=committed.obligations,
        ),
    )
    assert isinstance(proof, Committed)
    assert proof.discharged == committed.obligations
    assert store.applicability(
        committed.judgments[0], runtime.frame.id
    ).is_applicable()


def test_a_proof_and_discharge_are_published_atomically(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    target = commit_now(
        store,
        proposal(
            runtime, proposition, policy=ConditionPolicy.ALLOW_CONDITIONAL
        ),
    )
    assert isinstance(target, Committed)
    obligation = target.obligations[0]

    checker.outcome = Verified((condition,))
    before = store.stats()
    proof = commit_now(
        store,
        proposal(
            runtime,
            condition,
            discharge_obligations=(obligation,),
        ),
    )
    assert isinstance(proof, Committed)
    assert proof.discharged == (obligation,)
    assert store.is_discharged(obligation, runtime.frame.id)
    assert store.applicability(
        target.judgments[0], runtime.frame.id
    ).is_applicable()
    assert store.stats()["judgments"] == before["judgments"] + 1
    assert store.stats()["discharges"] == before["discharges"] + 1


def test_a_conditional_proof_is_not_published_with_a_discharge(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    target = commit_now(
        store,
        proposal(
            runtime, proposition, policy=ConditionPolicy.ALLOW_CONDITIONAL
        ),
    )
    assert isinstance(target, Committed)
    obligation = target.obligations[0]

    before = store.stats()
    checker.outcome = Verified(
        (condition,),
        (ObligationReport(condition, ObligationReason.RULE_GUARD),),
    )
    result = commit_now(
        store,
        proposal(
            runtime,
            condition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
            discharge_obligations=(obligation,),
        ),
    )
    assert isinstance(result, Rejected)
    assert "open conditions" in result.detail
    assert store.stats() == before


def test_a_proof_cannot_use_an_open_obligation_as_support(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    target = commit_now(
        store,
        proposal(
            runtime, proposition, policy=ConditionPolicy.ALLOW_CONDITIONAL
        ),
    )
    assert isinstance(target, Committed)
    obligation = target.obligations[0]

    before = store.stats()
    checker.outcome = Verified((condition,), used_premises=(0,))
    result = commit_now(
        store,
        proposal(
            runtime,
            condition,
            premises=target.judgments,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
            discharge_obligations=(obligation,),
        ),
    )
    assert isinstance(result, Rejected)
    assert store.stats() == before


def test_an_unknown_discharge_target_is_rejected_without_writing(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store,
        proposal(
            runtime,
            proposition,
            discharge_obligations=(ObligationId(10_000),),
        ),
    )
    assert isinstance(result, Rejected)
    assert "obligation does not exist" in result.detail
    assert_empty(store)


def test_a_discharge_needs_a_matching_new_judgment(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    target = commit_now(
        store,
        proposal(
            runtime, proposition, policy=ConditionPolicy.ALLOW_CONDITIONAL
        ),
    )
    assert isinstance(target, Committed)
    obligation = target.obligations[0]

    before = store.stats()
    checker.outcome = Verified((conclusion(runtime, 2),))
    result = commit_now(
        store,
        proposal(
            runtime,
            conclusion(runtime, 2),
            discharge_obligations=(obligation,),
        ),
    )
    assert isinstance(result, Rejected)
    assert "no new judgment" in result.detail
    assert store.stats() == before


def test_inherited_conditions_are_carried_and_counted_by_the_policy(runtime):
    store, checker = setup(runtime)
    first_proposition = conclusion(runtime, 1)
    second_proposition = conclusion(runtime, 2)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (first_proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            first_proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)
    obligation = first.obligations[0]

    checker.outcome = Verified(
        (second_proposition,), used_premises=(0,)
    )
    deferred = commit_now(
        store,
        proposal(runtime, second_proposition, premises=first.judgments),
    )
    assert isinstance(deferred, Deferred)
    assert deferred.conditions == (condition,)
    assert store.stats()["judgments"] == 1

    checker.outcome = Verified(
        (second_proposition,), used_premises=(0,)
    )
    committed = commit_now(
        store,
        proposal(
            runtime,
            second_proposition,
            premises=first.judgments,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(committed, Committed)
    assert committed.obligations == (obligation,)
    second = store.get_judgment(committed.judgments[0])
    assert second.obligations == (obligation,)
    assert store.applicability(
        second.id, runtime.frame.id
    ).is_conditional()
    assert store.stats()["obligations"] == 1


def test_a_reported_condition_already_inherited_is_not_duplicated(runtime):
    store, checker = setup(runtime)
    first_proposition = conclusion(runtime, 1)
    second_proposition = conclusion(runtime, 2)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (first_proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            first_proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)
    checker.outcome = Verified(
        (second_proposition,),
        (ObligationReport(condition, ObligationReason.RULE_GUARD),),
        used_premises=(0,),
    )
    committed = commit_now(
        store,
        proposal(
            runtime,
            second_proposition,
            premises=first.judgments,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(committed, Committed)
    assert committed.obligations == first.obligations
    assert store.stats()["obligations"] == 1


def test_unused_premises_are_not_recorded_and_carry_no_conditions(runtime):
    store, checker = setup(runtime)
    first_proposition = conclusion(runtime, 1)
    second_proposition = conclusion(runtime, 2)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (first_proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            first_proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)

    checker.outcome = Verified((second_proposition,))
    second = commit_now(
        store,
        proposal(runtime, second_proposition, premises=first.judgments),
    )
    assert isinstance(second, Committed)
    judgment = store.get_judgment(second.judgments[0])
    assert judgment.obligations == ()
    assert store.inference_of(judgment.id).premises == ()
    assert store.support(judgment.id) == frozenset()


def test_an_invalid_premise_index_is_rejected(runtime):
    store, checker = setup(runtime)
    first_proposition = conclusion(runtime, 1)
    checker.outcome = Verified((first_proposition,))
    first = commit_now(store, proposal(runtime, first_proposition))
    assert isinstance(first, Committed)

    second_proposition = conclusion(runtime, 2)
    checker.outcome = Verified((second_proposition,), used_premises=(1,))
    result = commit_now(
        store,
        proposal(runtime, second_proposition, premises=first.judgments),
    )
    assert isinstance(result, Rejected)
    assert "invalid premise index" in result.detail
    assert store.stats()["judgments"] == 1


def test_an_obligation_read_outside_the_submission_frame_is_rejected(runtime):
    store, checker = setup(runtime)
    child = runtime.frames.create(runtime.frame.id)
    child_condition = equation(
        runtime, variable(runtime), T.number(0), child.id
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(child_condition, ObligationReason.DEFINEDNESS),),
    )
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert "obligation was read outside" in result.detail
    assert_empty(store)


def test_the_inference_records_the_trusted_basis(runtime):
    checker = StubChecker()
    basis = BasisRef(
        "test-library",
        BasisKind.STANDARD_LIBRARY,
        "1",
        "digest",
        runtime.world.id,
    )
    store = KernelStore(
        runtime.frames,
        CheckerRegistry(
            {
                checker.id: CheckerSpec(
                    checker,
                    CertificateSchema("test", "1", str),
                    frozenset({"test.problem"}),
                    frozenset({"test.specification"}),
                    runtime.world.id,
                    (basis,),
                )
            }
        ),
        bases=BasisRegistry((basis,)),
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Committed)
    assert store.inference_of(result.judgments[0]).basis == (basis,)


def test_a_checker_is_not_admitted_for_an_unknown_problem_kind(runtime):
    store, checker = setup(runtime)
    checker.outcome = Verified((conclusion(runtime),))
    result = commit_now(
        store, proposal(runtime, conclusion(runtime), problem_kind="other")
    )
    assert isinstance(result, Rejected)
    assert "problem kind" in result.detail
    assert_empty(store)


def test_a_checker_is_not_admitted_for_an_unknown_specification_kind(runtime):
    store, checker = setup(runtime)
    checker.outcome = Verified((conclusion(runtime),))
    result = commit_now(
        store,
        proposal(
            runtime,
            conclusion(runtime),
            specification_kind="other",
        ),
    )
    assert isinstance(result, Rejected)
    assert "specification kind" in result.detail
    assert_empty(store)


def test_a_refuted_condition_is_rejected_without_deferral(runtime):
    store, checker = setup(runtime)
    condition = conclusion(runtime, 0)
    target = conclusion(runtime, 1)
    not_condition = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NOT,
            condition.term,
        ),
    )
    checker.outcome = Verified((not_condition,))
    refutation = commit_now(store, proposal(runtime, not_condition))
    assert isinstance(refutation, Committed)

    checker.outcome = Verified(
        (target,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    result = commit_now(
        store,
        proposal(
            runtime,
            target,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.REFUTED_CONDITION
    assert result.refuted_conditions == (condition,)
    assert result.refutation is None
    assert store.stats()["judgments"] == 1


def test_an_inconsistent_frame_rejects_publication(runtime):
    store, checker = setup(runtime)
    child = runtime.frames.create(runtime.frame.id)
    false_proposition = runtime_proposition(runtime, T.FALSE, child.id)
    checker.outcome = Verified((false_proposition,))
    proof = commit_now(
        store, proposal(runtime, false_proposition, frame=child.id)
    )
    assert isinstance(proof, Committed)
    store.record_inconsistency(child.id, proof.judgments[0])

    proposition = conclusion(runtime, 2)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store, proposal(runtime, proposition, frame=child.id)
    )
    assert isinstance(result, Rejected)
    assert "inconsistent" in result.detail

    grandchild = runtime.frames.create(child.id)
    inherited = runtime_proposition(
        runtime, proposition.term, grandchild.id
    )
    result = commit_now(
        store, proposal(runtime, inherited, frame=grandchild.id)
    )
    assert isinstance(result, Rejected)
    assert "inconsistent" in result.detail
    assert store.stats()["judgments"] == 1


def test_an_ancestor_condition_is_reused_in_a_child_frame(runtime):
    store, checker = setup(runtime)
    parent_condition = conclusion(runtime, 0)
    first_proposition = conclusion(runtime, 1)
    checker.outcome = Verified(
        (first_proposition,),
        (ObligationReport(parent_condition, ObligationReason.DEFINEDNESS),),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            first_proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)

    child = runtime.frames.create(runtime.frame.id)
    child_condition = equation(
        runtime, variable(runtime), T.number(0), child.id
    )
    second_proposition = equation(
        runtime, variable(runtime), T.number(2), child.id
    )
    checker.outcome = Verified(
        (second_proposition,),
        (ObligationReport(child_condition, ObligationReason.RULE_GUARD),),
    )
    second = commit_now(
        store,
        proposal(
            runtime,
            second_proposition,
            frame=child.id,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(second, Committed)
    assert second.obligations == first.obligations
    assert store.stats()["obligations"] == 1


def test_an_identical_condition_reuses_the_existing_obligation(runtime):
    store, checker = setup(runtime)
    condition = conclusion(runtime, 0)
    first_proposition = conclusion(runtime, 1)
    second_proposition = conclusion(runtime, 2)
    checker.outcome = Verified(
        (first_proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            first_proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)

    checker.outcome = Verified(
        (second_proposition,),
        (ObligationReport(condition, ObligationReason.RULE_GUARD),),
    )
    second = commit_now(
        store,
        proposal(
            runtime,
            second_proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(second, Committed)
    assert second.obligations == first.obligations
    assert store.stats()["obligations"] == 1

    checker.outcome = Verified((condition,))
    proof = commit_now(
        store,
        proposal(
            runtime,
            condition,
            discharge_obligations=first.obligations,
        ),
    )
    assert isinstance(proof, Committed)
    assert store.applicability(
        first.judgments[0], runtime.frame.id
    ).is_applicable()
    assert store.applicability(
        second.judgments[0], runtime.frame.id
    ).is_applicable()

    third_proposition = conclusion(runtime, 3)
    checker.outcome = Verified(
        (third_proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    third = commit_now(store, proposal(runtime, third_proposition))
    assert isinstance(third, Committed)
    assert third.obligations == first.obligations
    assert store.stats()["obligations"] == 1
    assert store.applicability(
        third.judgments[0], runtime.frame.id
    ).is_applicable()


def test_an_obligation_is_not_reused_across_a_changed_environment(runtime):
    store, checker = setup(runtime)
    condition = conclusion(runtime, 0)
    proposition = conclusion(runtime, 1)
    checker.outcome = Verified(
        (proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)
    extra = runtime.table.intern("obligation_extra")
    child = runtime.frames.create(
        runtime.frame.id,
        declarations=(
            Declaration(extra, "obligation_extra", S.REAL),
        ),
    )
    assert store.find_obligation(condition, child.id) is None


def test_a_certificate_must_match_the_declared_schema(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store,
        proposal(runtime, proposition, certificate=object()),
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_EVIDENCE
    assert "declared schema" in result.detail
    assert checker.requests == []
    assert_empty(store)


def test_a_math_checker_requires_the_original_problem(runtime):
    checker = StubChecker()
    store = KernelStore(
        runtime.frames,
        CheckerRegistry(
            {
                checker.id: CheckerSpec(
                    checker,
                    CertificateSchema("test", "1", str),
                    frozenset({"test.problem"}),
                    frozenset({"test.specification"}),
                    runtime.world.id,
                    requires_problem=True,
                )
            }
        ),
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert "original problem" in result.detail
    assert checker.requests == []
    assert_empty(store)


def test_a_math_checker_rejects_a_different_problem(runtime):
    checker = StubChecker()
    store = KernelStore(
        runtime.frames,
        CheckerRegistry(
            {
                checker.id: CheckerSpec(
                    checker,
                    CertificateSchema("test", "1", str),
                    frozenset({"test.problem"}),
                    frozenset({"test.specification"}),
                    runtime.world.id,
                    requires_problem=True,
                )
            }
        ),
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    problem = ProblemSpec(
        "other.problem",
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                variable(runtime),
            ),
        ),
        runtime.request.roles,
        None,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=runtime.request.value_domain,
        ),
    )
    result = commit_now(
        store, proposal(runtime, proposition, problem=problem)
    )
    assert isinstance(result, Rejected)
    assert "problem kind" in result.detail
    assert checker.requests == []
    assert_empty(store)


def test_a_published_inference_records_the_certificate_schema(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(store, proposal(runtime, proposition))
    assert isinstance(result, Committed)
    inference = store.inference_of(result.judgments[0])
    assert inference.certificate_schema == "test"
    assert inference.certificate_schema_version == "1"


def test_a_conclusion_from_another_world_is_rejected(runtime):
    store, checker = setup(runtime)
    other = bootstrap()
    assert other.frame.id == runtime.frame.id
    assert other.world.id != runtime.world.id
    foreign = equation(other, variable(other), T.number(1))
    checker.outcome = Verified((foreign,))
    result = commit_now(store, proposal(runtime, foreign))
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_REQUEST
    assert "another meaning world" in result.detail
    assert checker.requests == []
    assert_empty(store)


def test_a_premise_from_another_world_is_rejected(runtime):
    store, checker = setup(runtime)
    other = bootstrap()
    assert other.frame.id == runtime.frame.id
    foreign = equation(other, variable(other), T.number(1))
    foreign_id = store.new_judgment_id()
    store._judgments[foreign_id] = Judgment(
        foreign_id,
        runtime.frame.id,
        foreign,
        (),
        InferenceId(0),
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store,
        proposal(runtime, proposition, premises=(foreign_id,)),
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_REQUEST
    assert "another meaning world" in result.detail
    assert checker.requests == []


def test_a_cross_frame_checker_still_rejects_a_foreign_world_premise(runtime):
    store, checker = setup(runtime)
    checker.accepts_cross_frame_premises = True
    other = bootstrap()
    assert other.frame.id == runtime.frame.id
    foreign = equation(other, variable(other), T.number(1))
    foreign_id = store.new_judgment_id()
    store._judgments[foreign_id] = Judgment(
        foreign_id,
        runtime.frame.id,
        foreign,
        (),
        InferenceId(0),
    )
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    result = commit_now(
        store,
        proposal(runtime, proposition, premises=(foreign_id,)),
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_REQUEST
    assert "another meaning world" in result.detail
    assert checker.requests == []


def test_a_cross_frame_premise_must_be_closed_in_its_own_frame(runtime):
    store, checker = setup(runtime)
    checker.accepts_cross_frame_premises = True
    child = runtime.frames.create(runtime.frame.id)
    condition = equation(runtime, variable(runtime), T.number(0), child.id)
    child_proposition = equation(
        runtime, variable(runtime), T.number(1), child.id
    )
    checker.outcome = Verified(
        (child_proposition,),
        (
            ObligationReport(
                condition, ObligationReason.DEFINEDNESS
            ),
        ),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            child_proposition,
            frame=child.id,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)
    base_proposition = conclusion(runtime)
    checker.outcome = Verified((base_proposition,), used_premises=(0,))
    result = commit_now(
        store,
        proposal(
            runtime,
            base_proposition,
            premises=first.judgments,
        ),
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_EVIDENCE
    assert "open conditions" in result.detail
    assert store.stats()["judgments"] == 1


def test_a_closed_cross_frame_premise_is_not_inherited(runtime):
    store, checker = setup(runtime)
    checker.accepts_cross_frame_premises = True
    child = runtime.frames.create(runtime.frame.id)
    condition = equation(runtime, variable(runtime), T.number(0), child.id)
    child_proposition = equation(
        runtime, variable(runtime), T.number(1), child.id
    )
    checker.outcome = Verified(
        (child_proposition,),
        (
            ObligationReport(
                condition, ObligationReason.DEFINEDNESS
            ),
        ),
    )
    first = commit_now(
        store,
        proposal(
            runtime,
            child_proposition,
            frame=child.id,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)
    checker.outcome = Verified((condition,))
    proof = commit_now(
        store,
        proposal(
            runtime,
            condition,
            frame=child.id,
            discharge_obligations=first.obligations,
        ),
    )
    assert isinstance(proof, Committed)
    base_proposition = conclusion(runtime)
    checker.outcome = Verified((base_proposition,), used_premises=(0,))
    result = commit_now(
        store,
        proposal(
            runtime,
            base_proposition,
            premises=first.judgments,
        ),
    )
    assert isinstance(result, Committed)
    judgment = store.get_judgment(result.judgments[0])
    assert judgment.obligations == ()
    assert store.stats()["obligations"] == 1


def test_an_obligation_from_another_world_is_rejected(runtime):
    store, checker = setup(runtime)
    other = bootstrap()
    assert other.frame.id == runtime.frame.id
    foreign_condition = equation(other, variable(other), T.number(0))
    proposition = conclusion(runtime)
    checker.outcome = Verified(
        (proposition,),
        (
            ObligationReport(
                foreign_condition, ObligationReason.DEFINEDNESS
            ),
        ),
    )
    result = commit_now(
        store,
        proposal(
            runtime,
            proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(result, Rejected)
    assert result.kind is RejectedKind.INVALID_REQUEST
    assert "another meaning world" in result.detail
    assert_empty(store)


def test_rejected_results_validate_kind_and_detail():
    with pytest.raises(ValueError):
        Rejected("")
    with pytest.raises(TypeError):
        Rejected("detail", kind="invalid_request")  # type: ignore[arg-type]
    assert Rejected("detail").kind is RejectedKind.INVALID_REQUEST
