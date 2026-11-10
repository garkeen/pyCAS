"""Condition checking and automatic applicability resolution."""

from support import commit_now, head_app, proposition_in

from cas.foundation.ids import WorldId
from cas.kernel.applicability import resolve_applicability
from cas.kernel.commit import CommitProposal, Committed
from cas.kernel.condition_checker import ConditionChecker
from cas.kernel.context_rules import HypothesisChecker
from cas.kernel.evidence import (
    CheckerRegistry,
    CheckerSpec,
    CheckRequest,
    ObligationReport,
    Unverified,
    Verified,
)
from cas.kernel.model import (
    Applicable,
    Blocked,
    Conditional,
    ObligationReason,
    OutOfScope,
)
from cas.kernel.store import KernelStore
from cas.kernel.trust import CertificateSchema
from cas.language import sorts as S
from cas.language.execution import ConditionPolicy
from cas.language.signatures import StructuralHead
from cas.semantics.frames import Declaration, FrameStore, Hypothesis, World
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T


class ObligationChecker:
    """A test checker that reports one fixed obligation."""

    id = "test.obligation"
    version = "1"

    def __init__(self, obligation):
        self._obligation = obligation

    def check(self, request):
        return Verified(
            tuple(request.conclusions),
            obligations=(
                ObligationReport(
                    self._obligation, ObligationReason.RULE_GUARD
                ),
            ),
        )


class AnythingChecker:
    """A test checker that verifies exactly what it is asked to verify."""

    id = "test.anything"
    version = "1"

    def check(self, request):
        return Verified(tuple(request.conclusions))


def setup(*, hypotheses=()):
    table = SymbolTable()
    signature = standard_language(table)
    frames = FrameStore(World(WorldId(0), signature))
    x = table.intern("x")
    y = table.intern("y")
    base = frames.create(
        frames.root.id,
        declarations=(
            Declaration(x, "x", S.REAL),
            Declaration(y, "y", S.REAL),
        ),
    )
    x_term = T.symbol(x, "x")
    y_term = T.symbol(y, "y")
    assumptions = tuple(
        proposition_in(
            frames,
            base.id,
            signature,
            head_app(signature, head, x_term, T.number(bound)),
        )
        for head, bound in hypotheses
    )
    child = frames.create(
        base.id,
        hypotheses=tuple(Hypothesis(item) for item in assumptions),
    )
    target_proposition = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.GT, x_term, T.number(1)),
    )
    condition = ConditionChecker(frames, signature)
    hypothesis = HypothesisChecker(frames)
    obligation = ObligationChecker(
        proposition_in(
            frames,
            base.id,
            signature,
            head_app(
                signature,
                StructuralHead.GT,
                x_term,
                T.number(0),
            ),
        )
    )
    store = KernelStore(
        frames,
        CheckerRegistry(
            {
                condition.id: CheckerSpec(
                    condition,
                    CertificateSchema("condition", "1", type(None)),
                    frozenset({"discharge"}),
                    frozenset({"Condition"}),
                    frames.world.id,
                ),
                hypothesis.id: CheckerSpec(
                    hypothesis,
                    CertificateSchema("hypothesis", "1", type(None)),
                    frozenset({"assume"}),
                    frozenset({"Hypothesis"}),
                    frames.world.id,
                ),
                obligation.id: CheckerSpec(
                    obligation,
                    CertificateSchema("test", "1", type(None)),
                    frozenset({"test.problem"}),
                    frozenset({"test.specification"}),
                    frames.world.id,
                ),
                AnythingChecker.id: CheckerSpec(
                    AnythingChecker(),
                    CertificateSchema("test", "1", type(None)),
                    frozenset({"test.problem"}),
                    frozenset({"test.specification"}),
                    frames.world.id,
                ),
            }
        ),
    )
    return (
        frames,
        signature,
        store,
        child,
        target_proposition,
        x_term,
        y_term,
    )


def conditional_target(store, frame, proposition):
    outcome = commit_now(
        store,
        CommitProposal(
            frame.id,
            (proposition,),
            ObligationChecker.id,
            "test.problem",
            "test.specification",
            certificate=None,
            policy=ConditionPolicy.ALLOW_CONDITIONAL,
        ),
    )
    assert isinstance(outcome, Committed)
    return outcome.judgments[0]


def commit_hypothesis(store, frame, proposition):
    outcome = commit_now(
        store,
        CommitProposal(
            frame.id,
            (proposition,),
            HypothesisChecker.id,
            "assume",
            "Hypothesis",
            certificate=None,
        ),
    )
    assert isinstance(outcome, Committed)
    return outcome.judgments[0]


def test_the_condition_checker_reports_the_premises_it_needs():
    frames, signature, store, child, _, x_term, _ = setup()
    weaker = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.GT, x_term, T.number(0)),
    )
    stronger = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.GT, x_term, T.number(1)),
    )
    outcome = ConditionChecker(frames, signature).check(
        CheckRequest(child.id, (weaker,), (stronger,), None)
    )
    assert isinstance(outcome, Verified)
    assert outcome.used_premises == (0,)

    not_enough = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.GE, x_term, T.number(0)),
    )
    outcome = ConditionChecker(frames, signature).check(
        CheckRequest(child.id, (weaker,), (not_enough,), None)
    )
    assert isinstance(outcome, Unverified)


def test_resolution_discharges_a_proved_obligation():
    frames, _, store, child, target, _, _ = setup(
        hypotheses=((StructuralHead.GT, 0),)
    )
    hypothesis = commit_hypothesis(
        store, child, frames.assumptions(child.id)[0]
    )
    target_judgment = conditional_target(store, child, target)
    obligation = store.get_judgment(target_judgment).obligations[0]
    assert store.applicability(target_judgment, child.id).is_conditional()

    outcome = resolve_applicability(store, target_judgment, child.id)
    assert isinstance(outcome, Applicable)
    assert store.is_discharged(obligation, child.id)
    proofs = [
        judgment
        for judgment in store.judgments_visible(child.id)
        if judgment.id not in {target_judgment, hypothesis}
    ]
    assert len(proofs) == 1
    inference = store.inference_of(proofs[0].id)
    assert inference.checker_id == "logic.condition"
    assert inference.premises == (hypothesis,)


def test_a_stronger_hypothesis_can_prove_a_weaker_obligation():
    frames, _, store, child, target, _, _ = setup(
        hypotheses=((StructuralHead.GT, 1),)
    )
    commit_hypothesis(store, child, frames.assumptions(child.id)[0])
    target_judgment = conditional_target(store, child, target)
    outcome = resolve_applicability(store, target_judgment, child.id)
    assert isinstance(outcome, Applicable)


def test_an_insufficient_hypothesis_leaves_the_judgment_conditional():
    frames, _, store, child, target, _, _ = setup(
        hypotheses=((StructuralHead.GE, 0),)
    )
    commit_hypothesis(
        store, child, frames.assumptions(child.id)[0]
    )
    target_judgment = conditional_target(store, child, target)
    outcome = resolve_applicability(store, target_judgment, child.id)
    assert isinstance(outcome, Conditional)
    assert outcome.obligations


def test_resolution_out_of_scope_and_without_candidates():
    frames, _, store, child, target, _, _ = setup()
    target_judgment = conditional_target(store, child, target)
    sibling = frames.create(frames.get(child.id).parent)
    assert isinstance(
        resolve_applicability(store, target_judgment, sibling.id),
        OutOfScope,
    )
    assert isinstance(
        resolve_applicability(store, target_judgment, child.id),
        Conditional,
    )


def test_resolution_returns_blocked_for_a_refuted_obligation():
    frames, signature, store, child, target, _, _ = setup()
    target_judgment = conditional_target(store, child, target)
    obligation = store.get_judgment(target_judgment).obligations[0]
    proposition = store.get_obligation(obligation).proposition
    refutation = proposition_in(
        frames,
        child.id,
        signature,
        head_app(signature, StructuralHead.NOT, proposition.term),
    )
    outcome = commit_now(
        store,
        CommitProposal(
            child.id,
            (refutation,),
            AnythingChecker.id,
            "test.problem",
            "test.specification",
            certificate=None,
        ),
    )
    assert isinstance(outcome, Committed)

    application = store.applicability(target_judgment, child.id)
    assert isinstance(application, Blocked)
    assert application.refuted == (obligation,)
    assert not store.is_discharged(obligation, child.id)

    resolved = resolve_applicability(store, target_judgment, child.id)
    assert isinstance(resolved, Blocked)
    assert not store.is_discharged(obligation, child.id)
