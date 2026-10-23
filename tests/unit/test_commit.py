"""Commit: exact checker specifications, conditions and atomic publication."""

from support import equation, variable

from cas.foundation.ids import FrameId, JudgmentId
from cas.kernel.commit import (
    CommitProposal,
    Committed,
    ConditionPolicy,
    Deferred,
    Rejected,
    commit,
)
from cas.kernel.evidence import (
    CheckerRegistry,
    InvalidEvidence,
    ObligationReport,
    Refuted,
    Unverified,
    Verified,
)
from cas.kernel.model import ObligationReason
from cas.kernel.store import KernelStore
from cas.language.decisions import Reason
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
    store = KernelStore(runtime.frames, CheckerRegistry({checker.id: checker}))
    return store, checker


def conclusion(runtime, value: int = 1):
    return equation(runtime, variable(runtime), T.number(value))


def proposal(runtime, proposition, **overrides):
    values = dict(
        frame=runtime.frame.id,
        conclusions=(proposition,),
        checker_id="test.checker",
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
    result = commit(store, proposal(runtime, proposition))
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


def test_a_checker_must_have_verified_exactly_the_request(runtime):
    store, checker = setup(runtime)
    checker.outcome = Verified((conclusion(runtime, 2),))
    result = commit(store, proposal(runtime, conclusion(runtime, 1)))
    assert isinstance(result, Rejected)
    assert "different specification" in result.detail
    assert_empty(store)


def test_an_unverified_submission_is_deferred_without_writing(runtime):
    store, checker = setup(runtime)
    checker.outcome = Unverified(Reason.FRAGMENT, "outside the fragment")
    result = commit(store, proposal(runtime, conclusion(runtime)))
    assert isinstance(result, Deferred)
    assert result.reason is Reason.FRAGMENT
    assert result.detail == "outside the fragment"
    assert result.conditions == ()
    assert_empty(store)


def test_invalid_evidence_is_not_a_refutation(runtime):
    store, checker = setup(runtime)
    checker.outcome = InvalidEvidence("malformed certificate")
    result = commit(store, proposal(runtime, conclusion(runtime)))
    assert isinstance(result, Rejected)
    assert result.refutation is None
    assert "invalid evidence" in result.detail
    assert_empty(store)


def test_a_refutation_is_rejected_with_its_witnesses(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    refutation = Refuted(proposition, (T.number(1),), "the candidate differs")
    checker.outcome = refutation
    result = commit(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert result.refutation is refutation
    assert result.refutation.witnesses == (T.number(1),)
    assert_empty(store)


def test_an_unregistered_checker_defers(runtime):
    store, _ = setup(runtime)
    result = commit(
        store, proposal(runtime, conclusion(runtime), checker_id="missing")
    )
    assert isinstance(result, Deferred)
    assert result.reason is Reason.FRAGMENT
    assert_empty(store)


def test_a_submission_needs_a_conclusion(runtime):
    store, _ = setup(runtime)
    result = commit(store, proposal(runtime, conclusion(runtime), conclusions=()))
    assert isinstance(result, Rejected)
    assert "at least one conclusion" in result.detail
    assert_empty(store)


def test_a_missing_frame_is_rejected(runtime):
    store, _ = setup(runtime)
    result = commit(
        store, proposal(runtime, conclusion(runtime), frame=FrameId(10_000))
    )
    assert isinstance(result, Rejected)
    assert "frame" in result.detail
    assert_empty(store)


def test_an_unsupported_checker_outcome_is_rejected(runtime):
    store, checker = setup(runtime)
    checker.outcome = object()
    result = commit(store, proposal(runtime, conclusion(runtime)))
    assert isinstance(result, Rejected)
    assert "unsupported outcome" in result.detail
    assert_empty(store)


def test_missing_premises_are_rejected_before_the_checker_runs(runtime):
    store, checker = setup(runtime)
    result = commit(
        store,
        proposal(runtime, conclusion(runtime), premises=(JudgmentId(10_000),)),
    )
    assert isinstance(result, Rejected)
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
    first = commit(
        store, proposal(runtime, child_proposition, frame=child.id)
    )
    assert isinstance(first, Committed)
    checker.outcome = Verified((conclusion(runtime),))
    result = commit(
        store, proposal(runtime, conclusion(runtime), premises=first.judgments)
    )
    assert isinstance(result, Rejected)
    assert "premise is outside" in result.detail
    assert store.stats()["judgments"] == 1


def test_an_ancestor_premise_is_visible_and_is_resolved_for_the_checker(runtime):
    store, checker = setup(runtime)
    proposition = conclusion(runtime)
    checker.outcome = Verified((proposition,))
    first = commit(store, proposal(runtime, proposition))
    assert isinstance(first, Committed)
    child = runtime.frames.create(runtime.frame.id)
    child_proposition = equation(
        runtime, variable(runtime), T.number(2), child.id
    )
    checker.outcome = Verified(
        (child_proposition,), used_premises=(0,)
    )
    second = commit(
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
    result = commit(store, proposal(runtime, child_proposition))
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
    deferred = commit(store, proposal(runtime, proposition))
    assert isinstance(deferred, Deferred)
    assert deferred.reason is Reason.GUARDED
    assert deferred.conditions == (condition,)
    assert_empty(store)

    cases = commit(
        store,
        proposal(runtime, proposition, policy=ConditionPolicy.REQUEST_CASES),
    )
    assert isinstance(cases, Deferred)
    assert cases.reason is Reason.GUARDED
    assert cases.conditions == (condition,)
    assert_empty(store)

    committed = commit(
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
    committed = commit(
        store,
        proposal(
            runtime, proposition, policy=ConditionPolicy.ALLOW_CONDITIONAL
        ),
    )
    assert isinstance(committed, Committed)
    checker.outcome = Verified((condition,))
    proof = commit(store, proposal(runtime, condition))
    assert isinstance(proof, Committed)
    store.discharge(
        committed.obligations[0], proof.judgments[0], runtime.frame.id
    )
    assert store.applicability(
        committed.judgments[0], runtime.frame.id
    ).is_applicable()


def test_inherited_conditions_are_carried_and_counted_by_the_policy(runtime):
    store, checker = setup(runtime)
    first_proposition = conclusion(runtime, 1)
    second_proposition = conclusion(runtime, 2)
    condition = conclusion(runtime, 0)
    checker.outcome = Verified(
        (first_proposition,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    first = commit(
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
    deferred = commit(
        store,
        proposal(runtime, second_proposition, premises=first.judgments),
    )
    assert isinstance(deferred, Deferred)
    assert deferred.conditions == (condition,)
    assert store.stats()["judgments"] == 1

    checker.outcome = Verified(
        (second_proposition,), used_premises=(0,)
    )
    committed = commit(
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
    first = commit(
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
    committed = commit(
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
    first = commit(
        store,
        proposal(
            runtime,
            first_proposition,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(first, Committed)

    checker.outcome = Verified((second_proposition,))
    second = commit(
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
    first = commit(store, proposal(runtime, first_proposition))
    assert isinstance(first, Committed)

    second_proposition = conclusion(runtime, 2)
    checker.outcome = Verified((second_proposition,), used_premises=(1,))
    result = commit(
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
    result = commit(store, proposal(runtime, proposition))
    assert isinstance(result, Rejected)
    assert "obligation was read outside" in result.detail
    assert_empty(store)
