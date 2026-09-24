# -*- coding: utf-8 -*-
"""Kernel model and commit-protocol acceptance.

These tests nail down that committing is a boundary operation and that conditions and
scopes are the kernel's only substantive responsibility: an undecided candidate does
not land, a refuted condition refuses, discharge only records and never touches the
original conclusion, and a scope cannot overreach.
"""


from cas.kernel.commit import (
    GuardPolicy,
    StepProposal,
    commit,
)
from cas.kernel.evidence import Accepted, Evidence, UnknownResult
from cas.kernel.mode import ExecutionMode
from cas.kernel.model import (
    ContextReadSet,
    RequirementReason,
)
from cas.kernel.services import NullServices, register_core_checkers
from cas.kernel.store import KernelStore
from cas.kernel.verdict import YES, Reason, RefutationChannel, refute, unknown
from cas.syntax.term import N, S, mk, not_

# --- test checkers / services ---

class AlwaysOk:
    def check(self, proposal, context, services):
        return Accepted()


class Demands:
    """Accepts and declares one direct requirement (simulating a needed guard)."""
    def __init__(self, cond):
        self.cond = cond

    def check(self, proposal, context, services):
        return Accepted(direct_requirements=(self.cond,))


class Never:
    """Undecided (simulating outside the fragment / budget exhausted)."""
    def check(self, proposal, context, services):
        return UnknownResult(Reason.BUDGET, "test-only undecided")


class StubServices:
    """Decides from a given truth table (the kernel does not know it, calling only
    through the interface)."""

    def __init__(self, true=(), false=()):
        self.true = set(true)
        self.false = set(false)

    def decide(self, proposition, scope_id):
        if proposition in self.true:
            return YES
        if proposition in self.false:
            return refute(
                RefutationChannel.EXACT_COMPARISON, proposition, proposition,
                detail="test false-table entry")
        return unknown(Reason.GUARDED)


def _store(*checkers):
    st = KernelStore()
    register_core_checkers(st)
    for cid, ck in checkers:
        st.checkers.register(cid, ck)
    return st


# --- unconditional conclusions ---

def test_unconditional_conclusion_commits():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.ok")))
    assert r.is_committed()
    j = st.get_judgment(r.judgments[0])
    assert j.requirements == ()
    assert st.applicability(j.id, root.id).is_applicable()


# --- undecided candidates: policy is the only handling point ---

def test_undecided_candidate_not_committed_under_require_proved():
    """The kernel mechanism behind "an unverified candidate cannot take part in a
    trusted derivation": undecided writes nothing, no fail-open."""
    st = _store(("t.never", Never()))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.never"),
                                guard_policy=GuardPolicy.REQUIRE_PROVED))
    assert r.is_undecided()
    assert st.stats()["judgments"] == 0
    assert st.stats()["steps"] == 0
    assert st.stats()["requirements"] == 0


def test_checker_unknown_never_commits():
    """The core of the invariant: GuardPolicy governs condition discharge, not "let an
    unverified conclusion through"."""
    st = _store(("t.never", Never()))
    root = st.scopes.create()
    for policy in GuardPolicy:
        r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                    evidence=Evidence("t.never"),
                                    guard_policy=policy))
        assert r.is_undecided(), policy
    assert st.stats()["steps"] == 0


def test_unknown_condition_commits_with_condition_under_allow_conditional():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands"),
                                guard_policy=GuardPolicy.ALLOW_CONDITIONAL),
               services=StubServices())
    assert r.is_committed()
    j = st.get_judgment(r.judgments[0])
    assert len(j.requirements) == 1
    assert st.applicability(j.id, root.id).is_conditional()


def test_unknown_condition_not_committed_under_require_proved():
    """The automatic-simplification default: an undecided guard does not land
    silently."""
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands")),
               services=StubServices())
    assert r.is_undecided()
    assert st.stats()["steps"] == 0


def test_request_split_policy_returns_pending_condition():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands"),
                                guard_policy=GuardPolicy.REQUEST_SPLIT),
               services=StubServices())
    assert r.is_needs_split()
    assert r.conditions == (cond,)
    assert st.stats()["steps"] == 0


# --- conditions: recording, discharge, refutation ---

def test_undecided_condition_carried_on_conclusion():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands"),
                                guard_policy=GuardPolicy.ALLOW_CONDITIONAL),
               services=StubServices())
    assert r.is_committed()
    j = st.get_judgment(r.judgments[0])
    assert len(j.requirements) == 1
    req = st.get_requirement(j.requirements[0])
    assert req.proposition is cond
    assert req.reason is RequirementReason.RULE_GUARD
    assert st.applicability(j.id, root.id).is_conditional()


def test_refuted_condition_refuses_and_writes_nothing():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands")),
               services=StubServices(false=(cond,)))
    assert r.is_refused()
    assert r.reason is Reason.GUARDED
    assert st.stats()["steps"] == 0
    assert st.stats()["judgments"] == 0


def test_proved_condition_records_discharge_and_applies():
    """Recording a discharge needs a non-interactive mode: interactive defers
    discharge."""
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands")),
               services=StubServices(true=(cond,)),
               mode=ExecutionMode.DERIVATION)
    assert r.is_committed()
    j = st.get_judgment(r.judgments[0])
    rid = j.requirements[0]
    assert st.is_discharged(rid, root.id)
    d = st.discharges_of(rid)[0]
    proof = st.get_judgment(d.by_judgment)
    assert proof.proposition is cond
    assert st.applicability(j.id, root.id).is_applicable()


# --- execution modes ---

def test_execution_mode_does_not_change_conclusion():
    """A mode may only change bookkeeping granularity, never the return value."""
    cond = mk(S("Ne"), (S("x"), N(0)))
    seen = {}
    for mode in ExecutionMode:
        st = _store(("t.demands", Demands(cond)))
        root = st.scopes.create()
        r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                    evidence=Evidence("t.demands"),
                                    guard_policy=GuardPolicy.ALLOW_CONDITIONAL),
                   services=StubServices(), mode=mode)
        assert r.is_committed(), mode
        j = st.get_judgment(r.judgments[0])
        seen[mode] = (j.proposition, j.requirements)
    assert len(set(seen.values())) == 1, seen


def test_interactive_records_no_reads_or_discharge():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands")),
               services=StubServices(true=(cond,)),
               mode=ExecutionMode.INTERACTIVE)
    step = st.get_step(r.step)
    assert step.reads == ContextReadSet(), "interactive must not record read dependencies"
    j = st.get_judgment(r.judgments[0])
    # conditions are still decided (otherwise a refuted guard would slip through), only
    # the discharge is not recorded
    assert not st.is_discharged(j.requirements[0], root.id)
    assert st.applicability(j.id, root.id).is_conditional()


def test_audit_keeps_every_read_derivation_dedupes():
    cond = mk(S("Ne"), (S("x"), N(0)))
    reads = {}
    for mode in (ExecutionMode.DERIVATION, ExecutionMode.AUDIT):
        st = _store(("t.demands", Demands(cond)))
        root = st.scopes.create()
        r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                    evidence=Evidence("t.demands"),
                                    guard_policy=GuardPolicy.ALLOW_CONDITIONAL),
                   services=StubServices(), mode=mode)
        reads[mode] = st.get_step(r.step).reads.entries
    assert reads[ExecutionMode.DERIVATION], "derivation should record read dependencies"
    assert len(reads[ExecutionMode.AUDIT]) >= len(reads[ExecutionMode.DERIVATION])


def test_refuted_condition_refused_in_all_modes():
    """Condition decision is mode independent: a refutation always refuses the commit,
    since soundness does not depend on the mode."""
    cond = mk(S("Ne"), (S("x"), N(0)))
    for mode in ExecutionMode:
        st = _store(("t.demands", Demands(cond)))
        root = st.scopes.create()
        r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                    evidence=Evidence("t.demands")),
                   services=StubServices(false=(cond,)), mode=mode)
        assert r.is_refused(), mode
        assert st.stats()["steps"] == 0, mode


def test_refutation_makes_inapplicable_without_deleting():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)), ("t.ok", AlwaysOk()))
    root = st.scopes.create()
    r1 = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                 evidence=Evidence("t.demands"),
                                 guard_policy=GuardPolicy.ALLOW_CONDITIONAL),
                services=StubServices())
    jid = r1.judgments[0]
    assert st.applicability(jid, root.id).is_conditional()

    r2 = commit(st, StepProposal(scope=root.id, conclusions=(not_(cond),),
                                 evidence=Evidence("t.ok")))
    assert r2.is_committed()
    app = st.applicability(jid, root.id)
    assert app.is_inapplicable(), app
    # the original conclusion is still in the ledger: no physical deletion, no cascade
    assert st.get_judgment(jid).proposition is S("p")


# --- scopes: visibility and hygiene ---

def test_child_scope_conclusion_not_usable_in_parent():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    child = st.scopes.child(root)
    r1 = commit(st, StepProposal(scope=child.id, conclusions=(S("p"),),
                                 evidence=Evidence("t.ok")))
    assert r1.is_committed()
    # back in the parent scope, referencing a child-scope conclusion is refused
    r2 = commit(st, StepProposal(scope=root.id, premises=(r1.judgments[0],),
                                 conclusions=(S("q"),),
                                 evidence=Evidence("t.ok")))
    assert r2.is_refused()
    assert "not visible" in r2.detail


def test_sibling_branches_invisible():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    a = st.scopes.child(root)
    b = st.scopes.child(root)
    ja = commit(st, StepProposal(scope=a.id, conclusions=(S("p"),),
                                 evidence=Evidence("t.ok"))).judgments[0]
    rb = commit(st, StepProposal(scope=b.id, premises=(ja,),
                                 conclusions=(S("q"),), evidence=Evidence("t.ok")))
    assert rb.is_refused()


def test_ancestor_conclusion_visible_to_descendant():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    jr = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                 evidence=Evidence("t.ok"))).judgments[0]
    child = st.scopes.child(root)
    r = commit(st, StepProposal(scope=child.id, premises=(jr,),
                                conclusions=(S("q"),), evidence=Evidence("t.ok")))
    assert r.is_committed()


# --- boundary: no fail-open ---

def test_unregistered_checker_not_committed():
    st = KernelStore()
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.missing")),
               services=NullServices())
    assert r.is_undecided()
    assert st.stats()["steps"] == 0


def test_missing_scope_refused():
    st = KernelStore()
    register_core_checkers(st)
    st.checkers.register("t.ok", AlwaysOk())
    r = commit(st, StepProposal(scope=999, conclusions=(S("p"),),
                                evidence=Evidence("t.ok")))
    assert r.is_refused()


def test_null_services_decide_nothing():
    """NullServices is an honest default: no decider attached is not the same as
    decided true."""
    assert NullServices().decide(S("anything"), 0).is_unknown()
