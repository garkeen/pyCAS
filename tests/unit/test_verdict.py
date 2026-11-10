"""Verdict: checked receipts, refutations and non-publishing decisions."""

from dataclasses import replace

import pytest
from support import (
    commit_now,
    equation,
    head_app,
    runtime_proposition,
    variable,
)

from cas.foundation.ids import CandidateId
from cas.kernel.commit import CommitProposal, Committed
from cas.kernel.evidence import (
    AlgebraService,
    CheckerRegistry,
    CheckerSpec,
    DefinednessService,
    ObligationReport,
    Verified,
)
from cas.kernel.model import ObligationReason
from cas.kernel.store import KernelStore
from cas.kernel.trust import CertificateSchema
from cas.kernel.verdict import (
    LocalReceipt,
    RefutationReceipt,
    VerdictNo,
    VerdictUnknown,
    VerdictYes,
    decide,
)
from cas.language.decisions import Blocker, Reason
from cas.language.execution import (
    BudgetTicket,
    ConditionPolicy,
    ExecutionBudget,
)
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.specification import has_derivative
from cas.runtime.bootstrap import new_workspace
from cas.syntax import term as T


class StubChecker:
    id = "test.decide"
    version = "7"

    def __init__(self) -> None:
        self.outcome = None

    def check(self, request):
        return self.outcome


def _store(runtime):
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


def _proposal(runtime, proposition, **overrides):
    values = dict(
        frame=runtime.frame.id,
        conclusions=(proposition,),
        checker_id=StubChecker.id,
        problem_kind="test.problem",
        specification_kind="test.specification",
        certificate="certificate",
    )
    values.update(overrides)
    return CommitProposal(**values)


def _candidate_proposal(candidate):
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
        structured=candidate.structured,
        algebra=candidate.algebra,
    )


def source_term(runtime):
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature, StructuralHead.POWER, x, T.number(3)
        ),
        head_app(
            runtime.signature, StructuralHead.TIMES, T.number(-3), x
        ),
    )


def test_decide_returns_a_checked_receipt_without_publishing(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    candidate = result.candidate
    before = runtime.store.stats()

    verdict = decide(runtime.store, _candidate_proposal(candidate))

    assert isinstance(verdict, VerdictYes)
    receipt = verdict.receipt
    assert isinstance(receipt, LocalReceipt)
    assert receipt.proposition == candidate.specifications[0]
    assert receipt.checker_id == candidate.checker_id
    assert receipt.checker_version == "1"
    assert receipt.frame == candidate.frame
    assert receipt.batch.frame == candidate.frame
    assert receipt.batch.conclusions == candidate.specifications
    assert receipt.context.world == runtime.world.id
    assert receipt.context.frame == candidate.frame
    assert runtime.store.stats() == before
    with pytest.raises(KeyError):
        runtime.store.get_judgment(receipt.batch.committed.judgments[0])


def test_a_decided_receipt_context_carries_the_proposal_budget(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    budget = ExecutionBudget(max_nodes=100, max_depth=10)
    proposal = replace(
        _candidate_proposal(result.candidate), budget=budget
    )

    verdict = decide(runtime.store, proposal)

    assert isinstance(verdict, VerdictYes)
    context = verdict.receipt.context
    assert context.budget is not None
    assert context.budget.budget is budget
    assert isinstance(context.budget.ticket, BudgetTicket)
    assert context.budget.ticket.budget == budget
    assert context.budget.ticket.consumed_nodes == 0
    assert context.budget.ticket.consumed_depth == 0
    assert context.decision is not None
    assert context.supports is not None


def test_a_decided_receipt_context_carries_the_definedness_service(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    verdict = decide(runtime.store, _candidate_proposal(result.candidate))

    assert isinstance(verdict, VerdictYes)
    context = verdict.receipt.context
    service = context.definedness
    assert isinstance(service, DefinednessService)
    assert service.decision is context.decision
    assert service.frames is runtime.frames
    assert service.frame == context.frame


def test_a_decided_receipt_context_carries_the_proposal_algebra(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    proposal = replace(
        _candidate_proposal(result.candidate), algebra=runtime.request
    )

    verdict = decide(runtime.store, proposal)

    assert isinstance(verdict, VerdictYes)
    context = verdict.receipt.context
    assert isinstance(context.algebra, AlgebraService)
    assert context.algebra.request is runtime.request


def test_decide_refutes_a_false_derivative_without_publishing(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    candidate = result.candidate
    wrong = T.number(12345)
    claim = runtime_proposition(
        runtime,
        has_derivative(
            runtime.vocabulary,
            T.TRUE,
            source.term,
            variable(runtime),
            wrong,
        ),
    )
    certificate = DerivativeCertificate(
        T.TRUE, source.term, runtime.variable, wrong
    )
    before = runtime.store.stats()

    verdict = decide(
        runtime.store,
        CommitProposal(
            candidate.frame,
            (claim,),
            candidate.checker_id,
            candidate.problem.operation,
            candidate.specification_kind,
            certificate=certificate,
            problem=candidate.problem,
            candidate=wrong,
            candidate_role=candidate.candidate_role,
            algebra=candidate.algebra,
        ),
    )

    assert isinstance(verdict, VerdictNo)
    receipt = verdict.receipt
    assert isinstance(receipt, RefutationReceipt)
    assert receipt.proposition == claim
    assert receipt.witnesses == (source.term, wrong)
    assert receipt.detail
    assert receipt.checker_id == candidate.checker_id
    assert receipt.checker_version == "1"
    assert runtime.store.stats() == before


def test_decide_reports_a_deferred_checker_as_unknown(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    candidate = result.candidate
    budget = ExecutionBudget(max_nodes=5)
    before = runtime.store.stats()

    verdict = decide(
        runtime.store,
        CommitProposal(
            candidate.frame,
            candidate.specifications,
            "missing.checker",
            candidate.problem.operation,
            candidate.specification_kind,
            certificate=candidate.certificate,
            problem=candidate.problem,
            candidate=candidate.term,
            candidate_role=candidate.candidate_role,
            budget=budget,
            algebra=candidate.algebra,
        ),
    )

    assert isinstance(verdict, VerdictUnknown)
    assert len(verdict.blockers) == 1
    blocker = verdict.blockers[0]
    assert blocker.reason is Reason.FRAGMENT
    assert "not registered" in blocker.detail
    assert blocker.target == candidate.specifications[0]
    assert blocker.budget == budget
    assert runtime.store.stats() == before


def test_a_refuted_necessary_condition_is_guarded_not_no(runtime):
    store, checker = _store(runtime)
    condition = equation(runtime, variable(runtime), T.number(0))
    target = equation(runtime, variable(runtime), T.number(1))
    not_condition = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.NOT,
            condition.term,
        ),
    )
    checker.outcome = Verified((not_condition,))
    refutation = commit_now(store, _proposal(runtime, not_condition))
    assert isinstance(refutation, Committed)
    before = store.stats()

    checker.outcome = Verified(
        (target,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    verdict = decide(
        store,
        _proposal(
            runtime,
            target,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )

    assert isinstance(verdict, VerdictUnknown)
    assert not isinstance(verdict, VerdictNo)
    blocker = verdict.blockers[0]
    assert blocker.reason is Reason.GUARDED
    assert blocker.conditions == (condition,)
    assert blocker.target == target
    assert store.stats() == before


def test_an_open_condition_in_a_validated_batch_is_guarded(runtime):
    store, checker = _store(runtime)
    condition = equation(runtime, variable(runtime), T.number(0))
    target = equation(runtime, variable(runtime), T.number(1))
    checker.outcome = Verified(
        (target,),
        (ObligationReport(condition, ObligationReason.DEFINEDNESS),),
    )
    before = store.stats()

    verdict = decide(
        store,
        _proposal(
            runtime,
            target,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )

    assert isinstance(verdict, VerdictUnknown)
    blocker = verdict.blockers[0]
    assert blocker.reason is Reason.GUARDED
    assert blocker.conditions == (condition,)
    assert store.stats() == before


def test_a_verdict_is_not_implicitly_boolean(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    verdict = decide(
        runtime.store, _candidate_proposal(result.candidate)
    )
    assert isinstance(verdict, VerdictYes)
    with pytest.raises(TypeError, match="three-valued"):
        bool(verdict)
    with pytest.raises(TypeError, match="three-valued"):
        bool(VerdictUnknown((_blocker(),)))


def _blocker():
    return Blocker(Reason.FRAGMENT, "no fragment")


def test_receipt_variants_validate_their_payloads(runtime):
    proposition = runtime_proposition(runtime, T.TRUE)
    with pytest.raises(ValueError, match="witness"):
        RefutationReceipt(proposition, (), "detail", "checker", "1")
    with pytest.raises(ValueError, match="blocker"):
        VerdictUnknown(())
    with pytest.raises(TypeError, match="local receipt"):
        VerdictYes("not a receipt")


def test_workspace_decide_candidate_records_nothing(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    revision = workspace.revision
    events = workspace.events()
    before = runtime.store.stats()

    verdict = workspace.decide_candidate(result.candidate.id)

    assert isinstance(verdict, VerdictYes)
    assert workspace.revision is revision
    assert workspace.candidates() == revision.candidate_records
    assert workspace.tasks() == revision.task_records
    assert workspace.events() == events
    assert runtime.store.stats() == before


def test_workspace_decide_candidate_refuses_a_missing_candidate(runtime):
    workspace = new_workspace(runtime)
    with pytest.raises(ValueError, match="not visible"):
        workspace.decide_candidate(CandidateId(999))


def test_workspace_decide_candidate_refuses_a_hidden_candidate(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.candidate is not None
    assert workspace.undo()
    with pytest.raises(ValueError, match="not visible"):
        workspace.decide_candidate(result.candidate.id)
