"""Kernel case-analysis merge: two branch judgments issue one base judgment."""

from support import commit_now, head_app, runtime_proposition, variable

from cas.frontend import parse
from cas.language.signatures import StructuralHead
from cas.runtime.bootstrap import new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus


def positive_assumption(runtime):
    return runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )


def branch_derivative(workspace, runtime):
    source = workspace.intake(variable(runtime), "branch x")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.verifications
    judgment = result.verifications[0].judgment
    assert judgment is not None
    return result, judgment


def test_two_branch_judgments_issue_a_base_conclusion(runtime):
    workspace = new_workspace(runtime)
    assumption = positive_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None
    workspace.switch_to(split.split.positive_revision)
    positive_result, positive_judgment = branch_derivative(
        workspace, runtime
    )
    workspace.switch_to(split.split.negative_revision)
    negative_result, negative_judgment = branch_derivative(
        workspace, runtime
    )
    assert (
        positive_result.verifications[0].specification.term
        == negative_result.verifications[0].specification.term
    )
    workspace.switch_to(base.id)
    conclusion = workspace.merge_case_conclusion(
        split.split, positive_judgment, negative_judgment
    )
    assert conclusion.status is OperationStatus.VERIFIED
    assert conclusion.judgment is not None
    assert conclusion.proposition is not None
    assert (
        conclusion.proposition.term
        == positive_result.verifications[0].specification.term
    )
    judgment = runtime.store.get_judgment(conclusion.judgment)
    assert judgment.frame == base.frame
    visible = runtime.store.judgments_visible(base.frame)
    assert judgment in visible


def test_case_merge_reads_branch_judgments_through_the_context(runtime):
    from cas.kernel.case_merge import CaseMergeCertificate, CaseMergeChecker
    from cas.kernel.evidence import (
        CheckRequest,
        InvalidEvidence,
        SupportsService,
        VerificationContext,
        Verified,
    )

    workspace = new_workspace(runtime)
    assumption = positive_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None
    workspace.switch_to(split.split.positive_revision)
    positive_result, positive_judgment = branch_derivative(
        workspace, runtime
    )
    workspace.switch_to(split.split.negative_revision)
    negative_result, negative_judgment = branch_derivative(
        workspace, runtime
    )
    assert (
        positive_result.verifications[0].specification.term
        == negative_result.verifications[0].specification.term
    )
    workspace.switch_to(base.id)
    conclusion = runtime_proposition(
        runtime,
        positive_result.verifications[0].specification.term,
        base.frame,
    )
    positive = runtime.store.get_judgment(positive_judgment)
    negative = runtime.store.get_judgment(negative_judgment)
    calls = {"judgments": 0}

    def judgment(identifier):
        calls["judgments"] += 1
        return runtime.store.get_judgment(identifier)

    supports = SupportsService(
        judgment,
        runtime.store.judgments_visible,
        runtime.store.is_discharged,
    )
    context = VerificationContext(
        runtime.world.id,
        base.frame,
        runtime.frames,
        supports=supports,
    )
    checker = runtime.store.checkers.get("kernel.case_merge")
    assert isinstance(checker, CaseMergeChecker)
    certificate = CaseMergeCertificate(
        assumption,
        split.split.positive_frame,
        split.split.negative_frame,
        positive_judgment,
        negative_judgment,
    )
    premises = (positive.proposition, negative.proposition)

    outcome = checker.check(
        CheckRequest(
            base.frame,
            (conclusion,),
            premises,
            certificate,
            context=context,
        )
    )

    assert isinstance(outcome, Verified)
    assert outcome.used_premises == (0, 1)
    assert calls["judgments"] == 2

    unsupported = checker.check(
        CheckRequest(
            base.frame,
            (conclusion,),
            premises,
            certificate,
            context=VerificationContext(
                runtime.world.id, base.frame, runtime.frames
            ),
        )
    )
    assert isinstance(unsupported, InvalidEvidence)
    assert "support" in unsupported.detail


def test_case_merge_refuses_a_non_branch_judgment(runtime):
    workspace = new_workspace(runtime)
    assumption = positive_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None
    source = workspace.intake(variable(runtime), "base x")
    result = workspace.differentiate(source, runtime.variable)
    assert result.verifications
    base_judgment = result.verifications[0].judgment
    assert base_judgment is not None
    workspace.switch_to(base.id)
    conclusion = workspace.merge_case_conclusion(
        split.split, base_judgment, base_judgment
    )
    assert conclusion.status is OperationStatus.INVALID
    assert "branch" in conclusion.detail


def test_case_split_is_atomic_when_a_branch_commit_fails(runtime, monkeypatch):
    import cas.workflow.workspace as workspace_module
    from cas.kernel.commit import Rejected

    real_validate = workspace_module.validate_commit
    calls = {"count": 0}

    def fail_second(store, proposal):
        calls["count"] += 1
        if calls["count"] == 2:
            return Rejected("forced branch failure")
        return real_validate(store, proposal)

    monkeypatch.setattr(workspace_module, "validate_commit", fail_second)
    workspace = new_workspace(runtime)
    before = runtime.store.stats()
    result = workspace.case_split(positive_assumption(runtime).term)
    assert result.status is OperationStatus.INVALID
    assert runtime.store.stats() == before


def _branch_hypothesis(runtime, frame):
    judgments = tuple(
        judgment
        for judgment in runtime.store.judgments_visible(frame)
        if judgment.frame == frame
    )
    assert len(judgments) == 1
    return judgments[0].id


def test_case_merge_refuses_a_conclusion_assumed_in_a_branch(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(variable(runtime), "x")
    result = workspace.differentiate(source, runtime.variable)
    assert result.verifications
    assumption = result.verifications[0].specification
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None
    positive = _branch_hypothesis(runtime, split.split.positive_frame)
    workspace.switch_to(split.split.negative_revision)
    negative_source = workspace.intake(variable(runtime), "x")
    negative_result = workspace.differentiate(
        negative_source, runtime.variable
    )
    assert negative_result.verifications
    negative = negative_result.verifications[0].judgment
    assert negative is not None
    workspace.switch_to(base.id)
    conclusion = workspace.merge_case_conclusion(
        split.split, positive, negative
    )
    assert conclusion.status is not OperationStatus.VERIFIED
    assert "assumed" in conclusion.detail


def test_case_merge_refuses_open_branch_obligations(runtime):
    from cas.kernel.case_merge import (
        CaseMergeCertificate,
        CaseMergeChecker,
        JudgmentLookup,
    )
    from cas.kernel.commit import (
        CommitProposal,
        Committed,
    )
    from cas.kernel.evidence import (
        CheckerRegistry,
        CheckerSpec,
        CheckRequest,
        ObligationReport,
        Unverified,
        Verified,
    )
    from cas.kernel.model import ObligationReason
    from cas.kernel.store import KernelStore
    from cas.kernel.trust import CertificateSchema
    from cas.language.execution import ConditionPolicy
    from cas.semantics.frames import Hypothesis

    class StubChecker:
        version = "1"

        def __init__(self, identifier, obligations=()):
            self.id = identifier
            self.obligations = obligations

        def check(self, request):
            return Verified(
                tuple(request.conclusions),
                obligations=self.obligations,
            )

    p_term = parse("x > 0", runtime.table, runtime.signature)
    p = runtime_proposition(runtime, p_term)
    not_p = runtime_proposition(
        runtime,
        head_app(runtime.signature, StructuralHead.NOT, p_term),
    )
    q = runtime_proposition(runtime, T.TRUE)
    positive_frame = runtime.frames.create(
        runtime.frame.id, hypotheses=(Hypothesis(p),)
    )
    negative_frame = runtime.frames.create(
        runtime.frame.id, hypotheses=(Hypothesis(not_p),)
    )
    obligation = runtime_proposition(
        runtime,
        parse("x > 1", runtime.table, runtime.signature),
    )
    positive_checker = StubChecker(
        "test.case_stub.positive",
        (ObligationReport(obligation, ObligationReason.DEFINEDNESS),),
    )
    negative_checker = StubChecker("test.case_stub.negative")
    store = KernelStore(
        runtime.frames,
        CheckerRegistry(
            {
                positive_checker.id: CheckerSpec(
                    positive_checker,
                    CertificateSchema("case_stub", "1", type(None)),
                    frozenset({"case_stub"}),
                    frozenset({"CaseStub"}),
                    runtime.world.id,
                ),
                negative_checker.id: CheckerSpec(
                    negative_checker,
                    CertificateSchema("case_stub", "1", type(None)),
                    frozenset({"case_stub"}),
                    frozenset({"CaseStub"}),
                    runtime.world.id,
                ),
            }
        ),
    )
    positive = commit_now(
        store,
        CommitProposal(
            positive_frame.id,
            (q,),
            positive_checker.id,
            "case_stub",
            "CaseStub",
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    negative = commit_now(
        store,
        CommitProposal(
            negative_frame.id,
            (q,),
            negative_checker.id,
            "case_stub",
            "CaseStub",
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(positive, Committed)
    assert isinstance(negative, Committed)
    lookup = JudgmentLookup()
    lookup.bind(store)
    checker = CaseMergeChecker(
        runtime.frames, runtime.signature, lookup
    )
    positive_record = store.get_judgment(positive.judgments[0])
    negative_record = store.get_judgment(negative.judgments[0])
    outcome = checker.check(
        CheckRequest(
            runtime.frame.id,
            (q,),
            (positive_record.proposition, negative_record.proposition),
            CaseMergeCertificate(
                p,
                positive_frame.id,
                negative_frame.id,
                positive.judgments[0],
                negative.judgments[0],
            ),
        )
    )
    assert isinstance(outcome, Unverified)
    assert "open conditions" in outcome.detail


def test_case_merge_refuses_a_branch_with_extra_declarations(runtime):
    from cas.kernel.case_merge import (
        CaseMergeCertificate,
        CaseMergeChecker,
        JudgmentLookup,
    )
    from cas.kernel.commit import CommitProposal, Committed
    from cas.kernel.evidence import (
        CheckerRegistry,
        CheckerSpec,
        CheckRequest,
        InvalidEvidence,
        Verified,
    )
    from cas.kernel.store import KernelStore
    from cas.kernel.trust import CertificateSchema
    from cas.language import sorts as S
    from cas.semantics.frames import Declaration, Hypothesis

    class StubChecker:
        id = "test.case_stub"
        version = "1"

        def check(self, request):
            return Verified(tuple(request.conclusions))

    p_term = parse("x > 0", runtime.table, runtime.signature)
    p = runtime_proposition(runtime, p_term)
    not_p = runtime_proposition(
        runtime,
        head_app(runtime.signature, StructuralHead.NOT, p_term),
    )
    q = runtime_proposition(runtime, T.TRUE)
    extra = runtime.table.intern("case_extra")
    positive_frame = runtime.frames.create(
        runtime.frame.id,
        declarations=(Declaration(extra, "case_extra", S.REAL),),
        hypotheses=(Hypothesis(p),),
    )
    negative_frame = runtime.frames.create(
        runtime.frame.id, hypotheses=(Hypothesis(not_p),)
    )
    checker = StubChecker()
    store = KernelStore(
        runtime.frames,
        CheckerRegistry(
            {
                checker.id: CheckerSpec(
                    checker,
                    CertificateSchema("case_stub", "1", type(None)),
                    frozenset({"case_stub"}),
                    frozenset({"CaseStub"}),
                    runtime.world.id,
                )
            }
        ),
    )
    positive = commit_now(
        store,
        CommitProposal(
            positive_frame.id,
            (q,),
            checker.id,
            "case_stub",
            "CaseStub",
        ),
    )
    negative = commit_now(
        store,
        CommitProposal(
            negative_frame.id,
            (q,),
            checker.id,
            "case_stub",
            "CaseStub",
        ),
    )
    assert isinstance(positive, Committed)
    assert isinstance(negative, Committed)
    lookup = JudgmentLookup()
    lookup.bind(store)
    case_checker = CaseMergeChecker(
        runtime.frames, runtime.signature, lookup
    )
    outcome = case_checker.check(
        CheckRequest(
            runtime.frame.id,
            (q,),
            (),
            CaseMergeCertificate(
                p,
                positive_frame.id,
                negative_frame.id,
                positive.judgments[0],
                negative.judgments[0],
            ),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "pure hypothesis" in outcome.detail


def test_case_merge_refuses_a_non_direct_branch(runtime):
    from cas.foundation.ids import JudgmentId
    from cas.kernel.case_merge import (
        CaseMergeCertificate,
        CaseMergeChecker,
        JudgmentLookup,
    )
    from cas.kernel.evidence import (
        CheckerRegistry,
        CheckRequest,
        InvalidEvidence,
    )
    from cas.kernel.store import KernelStore
    from cas.semantics.frames import Hypothesis

    p_term = parse("x > 0", runtime.table, runtime.signature)
    p = runtime_proposition(runtime, p_term)
    not_p = runtime_proposition(
        runtime,
        head_app(runtime.signature, StructuralHead.NOT, p_term),
    )
    q = runtime_proposition(runtime, T.TRUE)
    positive = runtime.frames.create(
        runtime.frame.id, hypotheses=(Hypothesis(p),)
    )
    negative = runtime.frames.create(
        positive.id, hypotheses=(Hypothesis(not_p),)
    )
    lookup = JudgmentLookup()
    lookup.bind(
        KernelStore(runtime.frames, CheckerRegistry({}))
    )
    checker = CaseMergeChecker(
        runtime.frames, runtime.signature, lookup
    )
    outcome = checker.check(
        CheckRequest(
            runtime.frame.id,
            (q,),
            (),
            CaseMergeCertificate(
                p,
                positive.id,
                negative.id,
                JudgmentId(0),
                JudgmentId(0),
            ),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "direct children" in outcome.detail


def test_case_merge_refuses_different_branch_conclusions(runtime):
    workspace = new_workspace(runtime)
    assumption = positive_assumption(runtime)
    base = workspace.revision
    split = workspace.case_split(assumption.term)
    assert split.split is not None
    workspace.switch_to(split.split.positive_revision)
    positive_source = workspace.intake(
        parse("x^2", runtime.table, runtime.signature)
    )
    positive_result = workspace.differentiate(
        positive_source, runtime.variable
    )
    assert positive_result.verifications
    positive = positive_result.verifications[0].judgment
    assert positive is not None
    workspace.switch_to(split.split.negative_revision)
    negative_source = workspace.intake(
        parse("x^3", runtime.table, runtime.signature)
    )
    negative_result = workspace.differentiate(
        negative_source, runtime.variable
    )
    assert negative_result.verifications
    negative = negative_result.verifications[0].judgment
    assert negative is not None
    workspace.switch_to(base.id)
    conclusion = workspace.merge_case_conclusion(
        split.split, positive, negative
    )
    assert conclusion.status is not OperationStatus.VERIFIED


def test_case_merge_requires_exactly_the_two_branch_premises(runtime):
    from cas.kernel.case_merge import (
        CaseMergeCertificate,
        CaseMergeChecker,
        JudgmentLookup,
    )
    from cas.kernel.commit import CommitProposal, Committed
    from cas.kernel.evidence import (
        CheckerRegistry,
        CheckerSpec,
        CheckRequest,
        InvalidEvidence,
        Verified,
    )
    from cas.kernel.store import KernelStore
    from cas.kernel.trust import CertificateSchema
    from cas.semantics.frames import Hypothesis

    class StubChecker:
        id = "test.case_premise"
        version = "1"

        def check(self, request):
            return Verified(tuple(request.conclusions))

    p_term = parse("x > 0", runtime.table, runtime.signature)
    p = runtime_proposition(runtime, p_term)
    not_p = runtime_proposition(
        runtime,
        head_app(runtime.signature, StructuralHead.NOT, p_term),
    )
    q = runtime_proposition(runtime, T.TRUE)
    positive_frame = runtime.frames.create(
        runtime.frame.id, hypotheses=(Hypothesis(p),)
    )
    negative_frame = runtime.frames.create(
        runtime.frame.id, hypotheses=(Hypothesis(not_p),)
    )
    positive_q = runtime_proposition(runtime, T.TRUE, positive_frame.id)
    negative_q = runtime_proposition(runtime, T.TRUE, negative_frame.id)
    checker = StubChecker()
    store = KernelStore(
        runtime.frames,
        CheckerRegistry(
            {
                checker.id: CheckerSpec(
                    checker,
                    CertificateSchema("case_premise", "1", type(None)),
                    frozenset({"case_stub"}),
                    frozenset({"CaseStub"}),
                    runtime.world.id,
                )
            }
        ),
    )
    positive = commit_now(
        store,
        CommitProposal(
            positive_frame.id,
            (positive_q,),
            checker.id,
            "case_stub",
            "CaseStub",
        ),
    )
    negative = commit_now(
        store,
        CommitProposal(
            negative_frame.id,
            (negative_q,),
            checker.id,
            "case_stub",
            "CaseStub",
        ),
    )
    assert isinstance(positive, Committed)
    assert isinstance(negative, Committed)
    positive_proposition = store.get_judgment(
        positive.judgments[0]
    ).proposition
    negative_proposition = store.get_judgment(
        negative.judgments[0]
    ).proposition
    assert positive_proposition != negative_proposition
    lookup = JudgmentLookup()
    lookup.bind(store)
    case_checker = CaseMergeChecker(
        runtime.frames, runtime.signature, lookup
    )
    certificate = CaseMergeCertificate(
        p,
        positive_frame.id,
        negative_frame.id,
        positive.judgments[0],
        negative.judgments[0],
    )

    missing = case_checker.check(
        CheckRequest(runtime.frame.id, (q,), (), certificate)
    )
    assert isinstance(missing, InvalidEvidence)
    assert "two branch judgment premises" in missing.detail

    wrong = case_checker.check(
        CheckRequest(
            runtime.frame.id,
            (q,),
            (positive_proposition, positive_proposition),
            certificate,
        )
    )
    assert isinstance(wrong, InvalidEvidence)
    assert "same terms and frames" in wrong.detail

    verified = case_checker.check(
        CheckRequest(
            runtime.frame.id,
            (q,),
            (positive_proposition, negative_proposition),
            certificate,
        )
    )
    assert isinstance(verified, Verified)
    assert verified.checked == (q,)
    assert verified.used_premises == (0, 1)

    reversed_order = case_checker.check(
        CheckRequest(
            runtime.frame.id,
            (q,),
            (negative_proposition, positive_proposition),
            certificate,
        )
    )
    assert isinstance(reversed_order, Verified)
    assert reversed_order.used_premises == (0, 1)
