# -*- coding: utf-8 -*-
"""Branch merging (the five checks) and read-dependency union.

`split_on` only performed "coverage"; merging was not implemented, so
`ContextReadSet.merge` had no consumer. This file pins the behaviour once merging is
wired up: each of the five checks can refuse, a successful merge commits at the
parent scope, and inherited read dependencies are unioned per branch.
"""

import pytest

from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.errors import BranchError
from cas.frontend.parser import parse
from cas.syntax import term as T
from cas.syntax.term import S, N
from cas.workflow.command import Claim, Diff, Rewrite
from cas.workflow.branch import BranchStore
from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Evidence
from cas.kernel.mode import ExecutionMode
from cas.kernel.model import ContextReadSet

install(bootstrap())

X = S("x")


def _two_branch_derivatives(wf):
    """Build two branches, each differentiating the same predecessor (same request)."""
    s0 = wf.add(parse("x^2"), Claim())
    group = wf.split_on(parse("x > 0"))
    results = []
    for case in group.cases:
        wf.enter(case.scope)
        results.append(wf.add(parse("2*x"), Diff(pred=s0.id, var=X)))
    return group, s0, tuple(results)


# ---------------------------------------------------------------------------
# Success path: all five checks pass
# ---------------------------------------------------------------------------

def test_merge_commits_at_parent_scope():
    wf = new_workflow()
    root = wf.scope
    group, _s0, results = _two_branch_derivatives(wf)
    assert all(st.status == "committed" for st in results)
    wf.enter(root)
    m = wf.merge_branches(group, parse("2*x"), results)
    assert m.status == "committed", m.note
    assert m.judgment is not None
    merged = wf.store.get_judgment(m.judgment).scope
    assert merged == wf.scope
    assert wf.store.scopes.lineage_of(merged) == wf.store.scopes.lineage_of(root)


def test_merge_records_branch_steps_as_event_inputs():
    """A merge is an operation: the event records the branch steps it consumed as
    inputs."""
    wf = new_workflow()
    group, _s0, results = _two_branch_derivatives(wf)
    wf.enter(group.parent_lineage)
    m = wf.merge_branches(group, parse("2*x"), results)
    ids = wf.events.producers_of("artifact", m.artifact)
    assert ids, "the merge step should produce an artifact and attach it to the event"
    ev = wf.events.events()[ids[0]]
    assert set(ev.inputs) == {st.id for st in results}


# ---------------------------------------------------------------------------
# Each of the five checks can refuse
# ---------------------------------------------------------------------------

def test_merge_requires_coverage():
    """1. An unproved cover may not be merged."""
    wf = new_workflow()
    empty = BranchStore().create(wf.scope, ())
    with pytest.raises(BranchError):
        wf.merge_branches(empty, parse("2*x"), ())


def test_merge_requires_parent_scope():
    """Merging happens at the parent scope; merging inside a branch is misuse."""
    wf = new_workflow()
    group, _s0, results = _two_branch_derivatives(wf)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("2*x"), results)


def test_merge_rejects_different_requests():
    """2. Every branch must answer the same task (judged by request term)."""
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    group = wf.split_on(parse("x > 0"))
    wf.enter(group.cases[0].scope)
    a = wf.add(parse("2*x"), Diff(pred=s0.id, var=X))       # Differentiate
    wf.enter(group.cases[1].scope)
    b = wf.add(parse("x^2"), Rewrite(pred=s0.id))           # Simplify
    wf.enter(group.parent_lineage)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("2*x"), (a, b))


def test_merge_rejects_branch_without_conclusion():
    """3. Each branch result must be a dependable conclusion in its own scope."""
    wf = new_workflow()
    s0 = wf.add(parse("Log(x)"), Claim())      # differentiation not built: undecided, no conclusion
    group = wf.split_on(parse("x > 0"))
    results = []
    for case in group.cases:
        wf.enter(case.scope)
        results.append(wf.add(parse("1/x"), Diff(pred=s0.id, var=X)))
    assert all(st.judgment is None for st in results)
    wf.enter(group.parent_lineage)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("1/x"), tuple(results))


def test_merge_rejects_escaped_local_symbol():
    """4. A branch-local symbol must not escape into the parent scope with the merged
    conclusion."""
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    group = wf.split_on(parse("x > 0"))
    results = []
    for case in group.cases:
        wf.enter(case.scope)
        wf.define(S("u"), parse("x^2"))
        results.append(wf.add(parse("2*x"), Diff(pred=s0.id, var=X)))
    wf.enter(group.parent_lineage)
    with pytest.raises(BranchError):
        wf.merge_branches(group, T.times(S("u"), N(2)), tuple(results))


def test_merge_rejects_result_count_mismatch():
    wf = new_workflow()
    group, _s0, results = _two_branch_derivatives(wf)
    wf.enter(group.parent_lineage)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("2*x"), results[:1])


# ---------------------------------------------------------------------------
# Read-dependency union
# ---------------------------------------------------------------------------

def test_commit_merges_inherited_reads():
    """`commit` merges inherited read dependencies into this step's read set: the
    conclusion of a branch merge depends on the facts each branch read, which is
    exactly the consumer of `ContextReadSet.merge`."""
    wf = new_workflow(mode=ExecutionMode.DERIVATION)
    cond = parse("x > 0")
    inherited = ContextReadSet((("assumption", "x != 0"),))
    res = commit(wf.store,
                 StepProposal(scope=wf.scope,
                              conclusions=(T.or_(cond, T.not_(cond)),),
                              evidence=Evidence("branch.coverage", 0),
                              guard_policy=GuardPolicy.REQUIRE_PROVED),
                 services=wf.services, mode=ExecutionMode.DERIVATION,
                 inherited_reads=inherited)
    assert res.is_committed(), res
    assert ("assumption", "x != 0") in wf.store.get_step(res.step).reads.entries


def test_read_set_merge_is_union():
    a = ContextReadSet((("assumption", "p"), ("decide", "q")))
    b = ContextReadSet((("decide", "r"),))
    assert a.merge(b).entries == (("assumption", "p"), ("decide", "q"),
                                 ("decide", "r"))


# ---------------------------------------------------------------------------
# Entering a branch is an operation; a merge survives an undo that forks
# ---------------------------------------------------------------------------

def test_enter_is_recorded_and_undo_redo_move_through_it():
    """Entering a branch is a navigation operation: it produces no conclusion,
    task or artifact, but it takes its place in the event view, so undo leaves
    the branch again and redo enters it."""
    wf = new_workflow()
    group = wf.split_on(parse("x > 0"))
    parent = wf.scope
    case = group.cases[0]
    wf.enter(case.scope)
    assert wf.scope == case.scope
    last = wf.events.visible()[-1]
    assert last.command == "Enter"
    assert last.outputs == (), "entering produces no object"
    wf.undo()
    assert wf.scope == parent
    assert all(ev.command != "Enter" for ev in wf.events.visible())
    wf.redo()
    assert wf.scope == case.scope
    assert wf.events.visible()[-1].command == "Enter"


def test_merge_after_an_undo_forks_the_chain_and_still_commits():
    """The group names its parent by lineage, so a merge resolves again after an
    undo forked a new version chain from the parent version.

    Sequence: create the branches, enter a branch and produce a step, let the
    parent context grow, undo that growth twice (the restored parent version is
    no longer its lineage head), grow it again -- which forks a fresh chain
    under it -- and merge.
    """
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    parent = wf.scope
    group = wf.split_on(parse("x > 0"))
    results = []
    for case in group.cases:
        wf.enter(case.scope)
        results.append(wf.add(parse("2*x"), Diff(pred=s0.id, var=X)))
    scopes = wf.store.scopes
    wf.enter(group.parent_lineage)
    wf.add(parse("y > 0"), Claim())
    wf.add(parse("w > 0"), Claim())
    wf.undo()
    wf.undo()
    assert wf.scope == parent
    assert scopes.head_of(parent) != parent, "the restored version is not the head"
    # growing again forks a fresh chain under the restored version
    wf.add(parse("z > 0"), Claim())
    assert scopes.lineage_of(wf.scope) != group.parent_lineage
    m = wf.merge_branches(group, parse("2*x"), tuple(results))
    assert m.status == "committed", m.note
    merged = wf.store.get_judgment(m.judgment).scope
    assert scopes.lineage_of(merged) == group.parent_lineage
    assert scopes.lineage_of(merged) != scopes.lineage_of(wf.scope)
