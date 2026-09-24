"""Claim assumptions register only after commit."""

from cas.kernel.model import Declaration
from cas.runtime import Runtime, new_workflow
from cas.syntax import term as T
from cas.syntax.term import S
from cas.workflow.command import Claim

X = S("x")
A = S("a")
REAL = S("Real")


def _has_positive_x(assumptions) -> bool:
    return any(item.proposition is T.gt(X, T.ZERO) for item in assumptions)


def _has_positive_a(assumptions) -> bool:
    return any(item.proposition is T.gt(A, T.ZERO) for item in assumptions)


def test_committed_claim_registers_assumption_after_commit(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    workflow.declare(X, REAL)
    step = workflow.add(T.gt(X, T.ZERO), Claim())
    assert step.status == "committed"
    assert step.judgment is not None
    assert _has_positive_x(workflow.store.scopes.assumptions(workflow.scope))


def test_refused_claim_does_not_pollute_scope(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    root = workflow.scope
    child = workflow.store.scopes.child(
        workflow.store.scopes.get(root),
        declarations=(Declaration(A, REAL),),
    )
    assert child.id != root
    workflow.enter(root)
    step = workflow.add(T.gt(A, T.ZERO), Claim())
    assert step.status == "refused"
    assert step.judgment is None
    assert not _has_positive_a(workflow.store.scopes.assumptions(root))


def test_claim_checker_rejects_non_claim_command(runtime: Runtime) -> None:
    from cas.kernel.commit import GuardPolicy, StepProposal, commit
    from cas.kernel.context import TrackedContext
    from cas.kernel.evidence import Evidence
    from cas.kernel.services import NullServices, register_core_checkers
    from cas.kernel.store import KernelStore
    from cas.math.base.checkers import ClaimChecker

    store = KernelStore()
    register_core_checkers(store)
    store.checkers.register("assumption.entry", ClaimChecker(runtime.math))

    class NonClaim:
        pass

    proposal = StepProposal(
        scope=store.scopes.create().id,
        conclusions=(T.gt(X, T.ZERO),),
        evidence=Evidence("assumption.entry", NonClaim()),
        guard_policy=GuardPolicy.ALLOW_CONDITIONAL,
    )
    result = commit(
        store,
        proposal,
        context=TrackedContext(store.scopes, NullServices(), proposal.scope),
        services=NullServices(),
    )
    assert result.is_refused()
