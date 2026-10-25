"""The ledger through its only write boundary: commit, support, discharge."""

import pytest
from support import equation, head_app, runtime_proposition, variable

from cas.foundation.ids import InferenceId, JudgmentId
from cas.kernel.commit import (
    CommitProposal,
    Committed,
    ConditionPolicy,
    Rejected,
    commit,
)
from cas.kernel.evidence import (
    CheckerRegistry,
    CheckerSpec,
    ObligationReport,
    Verified,
)
from cas.kernel.model import (
    Blocked,
    Conditional,
    ObligationReason,
    OutOfScope,
)
from cas.kernel.store import KernelStore
from cas.kernel.trust import CertificateSchema
from cas.language.signatures import StructuralHead
from cas.syntax import term as T


class StubChecker:
    id = "test.checker"
    version = "1"

    def __init__(self) -> None:
        self.used_premises: tuple[int, ...] = ()
        self.conditions: tuple = ()

    def check(self, request):
        return Verified(
            tuple(request.conclusions),
            tuple(
                ObligationReport(condition, ObligationReason.DEFINEDNESS)
                for condition in self.conditions
            ),
            (),
            tuple(self.used_premises),
        )


def setup(runtime):
    checker = StubChecker()
    registration = CheckerSpec(
        checker,
        CertificateSchema("test", "1", type(None)),
        frozenset({"test.problem"}),
        frozenset({"test.specification"}),
        runtime.world.id,
    )
    store = KernelStore(
        runtime.frames, CheckerRegistry({checker.id: registration})
    )
    return store, checker


def commit_one(
    store,
    checker,
    frame,
    proposition,
    *,
    premises=(),
    conditions=(),
    policy=ConditionPolicy.REQUIRE_PROVED,
    used=(),
    discharge=(),
):
    checker.conditions = tuple(conditions)
    checker.used_premises = tuple(used)
    result = commit(
        store,
        CommitProposal(
            frame=frame,
            conclusions=(proposition,),
            checker_id=checker.id,
            problem_kind="test.problem",
            specification_kind="test.specification",
            premises=tuple(premises),
            certificate=None,
            policy=policy,
            discharge_obligations=tuple(discharge),
        ),
    )
    assert isinstance(result, Committed), result
    return result, store.get_judgment(result.judgments[0])


def test_commit_inserts_and_can_be_queried(runtime):
    store, checker = setup(runtime)
    proposition = equation(runtime, variable(runtime), T.number(1))
    result, judgment = commit_one(
        store, checker, runtime.frame.id, proposition
    )
    assert store.get_judgment(judgment.id) is judgment
    assert store.inference_of(judgment.id).conclusions == (judgment.id,)
    assert store.inference_of(judgment.id).premises == ()
    assert store.stats()["judgments"] == 1
    assert store.stats()["inferences"] == 1


def test_support_is_the_transitive_premise_set(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    first_result, first = commit_one(
        store, checker, base, equation(runtime, x, T.number(1))
    )
    second_result, second = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(2)),
        premises=first_result.judgments,
        used=(0,),
    )
    third_result, third = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(3)),
        premises=second_result.judgments,
        used=(0,),
    )
    assert store.support(third.id) == frozenset({first.id, second.id})
    assert store.support(first.id) == frozenset()
    assert store.inference_of(third.id).premises == (second.id,)


def test_applicability_is_out_of_scope_towards_an_ancestor(runtime):
    store, checker = setup(runtime)
    child = runtime.frames.create(runtime.frame.id)
    proposition = equation(
        runtime, variable(runtime), T.number(1), child.id
    )
    _, judgment = commit_one(store, checker, child.id, proposition)
    assert store.applicability(judgment.id, runtime.frame.id) == OutOfScope(
        child.id, runtime.frame.id
    )
    assert store.applicability(judgment.id, child.id).is_applicable()


def test_an_open_obligation_makes_a_judgment_conditional(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0))
    result, judgment = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    assert len(result.obligations) == 1
    application = store.applicability(judgment.id, base)
    assert isinstance(application, Conditional)
    assert application.obligations == result.obligations
    child = runtime.frames.create(base)
    assert store.applicability(judgment.id, child.id).is_conditional()


def test_discharge_is_recorded_and_visible_to_descendants(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0))
    result, judgment = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    obligation_id = result.obligations[0]
    child = runtime.frames.create(base)
    sibling = runtime.frames.create(base)
    grandchild = runtime.frames.create(child.id)
    proof, _ = commit_one(
        store,
        checker,
        child.id,
        condition,
        discharge=(obligation_id,),
    )
    assert proof.discharged == (obligation_id,)
    assert store.is_discharged(obligation_id, child.id)
    assert store.is_discharged(obligation_id, grandchild.id)
    assert not store.is_discharged(obligation_id, base)
    assert not store.is_discharged(obligation_id, sibling.id)
    assert store.applicability(judgment.id, child.id).is_applicable()
    assert store.applicability(judgment.id, sibling.id).is_conditional()
    assert store.stats()["discharges"] == 1


def test_discharge_requires_the_exact_proposition(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0))
    result, _ = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    obligation_id = result.obligations[0]
    checker.conditions = ()
    checker.used_premises = ()
    outcome = commit(
        store,
        CommitProposal(
            base,
            (equation(runtime, x, T.number(2)),),
            checker.id,
            "test.problem",
            "test.specification",
            certificate=None,
            discharge_obligations=(obligation_id,),
        ),
    )
    assert isinstance(outcome, Rejected)
    assert "no new judgment proves" in outcome.detail
    assert not store.is_discharged(obligation_id, base)


def test_discharge_requires_a_visible_proof(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    child = runtime.frames.create(base)
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0))
    result, _ = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    obligation_id = result.obligations[0]
    checker.conditions = ()
    checker.used_premises = ()
    outcome = commit(
        store,
        CommitProposal(
            base,
            (equation(runtime, x, T.number(0), child.id),),
            checker.id,
            "test.problem",
            "test.specification",
            certificate=None,
            discharge_obligations=(obligation_id,),
        ),
    )
    assert isinstance(outcome, Rejected)
    assert "outside" in outcome.detail
    assert not store.is_discharged(obligation_id, base)


def test_discharge_refuses_a_conditional_proof(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    target_condition = equation(runtime, x, T.number(0))
    other_condition = equation(runtime, x, T.number(3))
    first_result, _ = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(target_condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    obligation_id = first_result.obligations[0]
    checker.conditions = (other_condition,)
    checker.used_premises = ()
    outcome = commit(
        store,
        CommitProposal(
            base,
            (target_condition,),
            checker.id,
            "test.problem",
            "test.specification",
            certificate=None,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
            discharge_obligations=(obligation_id,),
        ),
    )
    assert isinstance(outcome, Rejected)
    assert "open conditions" in outcome.detail
    assert not store.is_discharged(obligation_id, base)


def test_discharge_is_not_recorded_twice(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0))
    result, _ = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    obligation_id = result.obligations[0]
    first, _ = commit_one(
        store,
        checker,
        base,
        condition,
        discharge=(obligation_id,),
    )
    assert first.discharged == (obligation_id,)
    checker.conditions = ()
    checker.used_premises = ()
    second = commit(
        store,
        CommitProposal(
            base,
            (condition,),
            checker.id,
            "test.problem",
            "test.specification",
            certificate=None,
            discharge_obligations=(obligation_id,),
        ),
    )
    assert isinstance(second, Rejected)
    assert "already discharged" in second.detail
    assert store.stats()["discharges"] == 1


def test_unknown_ids_are_reported(runtime):
    store, _ = setup(runtime)
    with pytest.raises(KeyError):
        store.get_judgment(JudgmentId(10_000))
    with pytest.raises(KeyError):
        store.get_inference(InferenceId(10_000))


def negate(runtime, proposition, frame):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NOT,
            proposition.term,
        ),
        frame,
    )


def test_a_refuted_obligation_blocks_applicability(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0))
    _, target = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    _, refutation = commit_one(
        store, checker, base, negate(runtime, condition, base)
    )
    application = store.applicability(target.id, base)
    assert isinstance(application, Blocked)
    assert application.refuted == target.obligations
    assert application.unresolved == ()
    assert application.witnesses == (refutation.id,)
    assert application.is_blocked()


def test_a_blocked_judgment_keeps_its_unresolved_obligations(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    first = equation(runtime, x, T.number(0))
    second = equation(runtime, x, T.number(2))
    _, target = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(first, second),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    commit_one(store, checker, base, negate(runtime, first, base))
    application = store.applicability(target.id, base)
    assert isinstance(application, Blocked)
    assert application.refuted == (target.obligations[0],)
    assert application.unresolved == (target.obligations[1],)


def test_a_conditional_judgment_is_not_a_refutation(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0))
    other = equation(runtime, x, T.number(2))
    _, target = commit_one(
        store,
        checker,
        base,
        equation(runtime, x, T.number(1)),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    commit_one(
        store,
        checker,
        base,
        negate(runtime, condition, base),
        conditions=(other,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    assert store.applicability(target.id, base).is_conditional()


def test_a_refutation_in_an_ancestor_blocks_a_descendant(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    child = runtime.frames.create(base)
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0), child.id)
    _, target = commit_one(
        store,
        checker,
        child.id,
        equation(runtime, x, T.number(1), child.id),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    commit_one(store, checker, base, negate(runtime, condition, base))
    application = store.applicability(target.id, child.id)
    assert isinstance(application, Blocked)


def test_a_refutation_in_a_sibling_is_not_visible(runtime):
    store, checker = setup(runtime)
    base = runtime.frame.id
    left = runtime.frames.create(base)
    right = runtime.frames.create(base)
    x = variable(runtime)
    condition = equation(runtime, x, T.number(0), left.id)
    _, target = commit_one(
        store,
        checker,
        left.id,
        equation(runtime, x, T.number(1), left.id),
        conditions=(condition,),
        policy=ConditionPolicy.ALLOW_CONDITIONAL,
    )
    commit_one(
        store, checker, right.id, negate(runtime, condition, right.id)
    )
    assert store.applicability(target.id, left.id).is_conditional()
