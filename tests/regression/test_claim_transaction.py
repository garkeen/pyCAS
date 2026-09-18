# -*- coding: utf-8 -*-
"""Nail tests for the claim transaction order.

A claim's proposition becomes a scope assumption only after its commit succeeds,
so a refused claim never pollutes the scope's assumptions and later decisions.
The checker verifies the claim from the command payload, not from the scope.
"""

from cas.runtime import new_workflow
from cas.syntax import term as T
from cas.syntax.term import S
from cas.kernel.model import Assumption, Declaration
from cas.workflow.command import Claim

X = S("x")
A = S("a")
REAL = S("Real")


def _assume_eq_x_0(s):
    return any(asm.proposition is T.gt(X, T.ZERO) for asm in s)


def _assume_eq_a_0(s):
    return any(asm.proposition is T.gt(A, T.ZERO) for asm in s)


def test_committed_claim_registers_assumption_after_commit():
    wf = new_workflow()
    wf.declare(X, REAL)
    step = wf.add(T.gt(X, T.ZERO), Claim())
    assert step.status == "committed"
    assert step.judgment is not None
    # the assumption landed only because the commit succeeded
    assert _assume_eq_x_0(wf.store.scopes.assumptions(wf.scope))


def test_refused_claim_does_not_pollute_scope():
    wf = new_workflow()
    root = wf.scope
    # declare `a` in a child scope, so `a` is local there and escapes the root
    child = wf.store.scopes.child(
        wf.store.scopes.get(root), declarations=(Declaration(A, REAL),))
    assert child.id != root
    # stay at root and claim a proposition mentioning the escaped `a`
    wf.enter(root)
    step = wf.add(T.gt(A, T.ZERO), Claim())
    assert step.status == "refused", step.note
    assert step.judgment is None
    # the refused claim must not have registered its assumption at the root
    assert not _assume_eq_a_0(wf.store.scopes.assumptions(root))


def test_claim_checker_rejects_non_claim_command():
    # a command that does not declare registers_assumption cannot use the
    # assumption.entry checker; this pins the payload check (the checker no
    # longer reads the scope).
    from cas.kernel.evidence import Evidence
    from cas.kernel.commit import StepProposal, GuardPolicy
    from cas.kernel.store import KernelStore
    from cas.kernel.services import register_core_checkers
    from cas.runtime import get_runtime
    from cas.math.base.checkers import ClaimChecker

    store = KernelStore()
    register_core_checkers(store)
    # wire the claim checker directly so a non-claim payload is rejected
    store.checkers.register("assumption.entry", ClaimChecker())

    class NonClaim:
        # no registers_assumption attribute
        pass

    proposal = StepProposal(
        scope=store.scopes.create().id, conclusions=(T.gt(X, T.ZERO),),
        evidence=Evidence("assumption.entry", NonClaim()),
        guard_policy=GuardPolicy.ALLOW_CONDITIONAL)
    from cas.kernel.context import TrackedContext
    from cas.kernel.services import NullServices
    from cas.kernel.commit import commit
    res = commit(store, proposal,
                 context=TrackedContext(store.scopes, NullServices(),
                                        proposal.scope),
                 services=NullServices())
    assert res.is_refused()
