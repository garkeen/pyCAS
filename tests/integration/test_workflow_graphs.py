# -*- coding: utf-8 -*-
"""Stage 4 acceptance: three separate graphs.

The artifact graph, task graph, and operation-history graph are independent; an
Artifact has no truth value and cannot serve as a mathematical premise; Event.outputs
is the only exit connecting an operation to a kernel conclusion; and undo/redo only
move pointers, never delete events.
"""

from cas.runtime import new_workflow
from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Evidence
from cas.syntax import term as T
from cas.frontend.parser import parse
from cas.syntax.term import S, N
from cas.workflow.command import Claim, Diff, Solve, BothSides


def test_artifact_separate_from_conclusion_cannot_be_premise():
    """An Artifact cannot be a mathematical premise."""
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    art = wf.artifacts.get(s0.artifact)
    assert art.value is parse("x^2")
    # submitting an ArtifactId as a premise: the kernel finds no such Judgment and refuses
    r = commit(wf.store,
               StepProposal(scope=wf.scope, premises=(art.id,),
                            conclusions=(parse("x"),),
                            evidence=Evidence("assumption.entry"),
                            guard_policy=GuardPolicy.ALLOW_CONDITIONAL),
               services=wf.services)
    assert r.is_refused()


def test_each_step_produces_artifact_attached_to_event():
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    s1 = wf.add(parse("2*x"), Diff(pred=s0.id, var=S("x")))
    assert wf.artifacts.get(s1.artifact).value is parse("2*x")
    ev = wf.events.events()[-1]
    assert wf.artifacts.get(s1.artifact).produced_by == ev.id
    kinds = [r.kind for r in ev.outputs]
    assert "artifact" in kinds and "judgment" in kinds and "task" in kinds


def test_history_separate_from_proof_undo_moves_pointer():
    wf = new_workflow()
    wf.add(parse("x^2"), Claim())
    wf.add(parse("2*x"), Diff(pred=0, var=S("x")))
    n_events = len(wf.events)
    n_steps = len(wf.all_steps())
    assert n_events == 2
    wf.undo()
    assert len(wf.events.visible()) == 1
    assert len(wf.events) == n_events, "undo must not delete events"
    assert len(wf.all_steps()) == n_steps, "undo must not delete steps/conclusions"
    wf.redo()
    assert len(wf.events.visible()) == 2


def test_provenance_chain_judgment_to_event():
    """Judgment -> Step -> Event: the reverse query is answered by the Event side's
    inverted index."""
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    s1 = wf.add(parse("2*x"), Diff(pred=s0.id, var=S("x")))
    assert s1.judgment is not None
    producers = wf.events.producers_of("judgment", s1.judgment)
    assert len(producers) == 1
    ev = wf.events.events()[producers[0]]
    assert ev.command == "Diff"
    # the kernel side holds no reverse reference: Step has no event field
    step = wf.store.get_step(s1.judgment and wf.store.get_judgment(s1.judgment).producer)
    assert not hasattr(step, "event")


def test_task_and_candidate_state_derived_from_data():
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    s1 = wf.add(parse("2*x"), Diff(pred=s0.id, var=S("x")))
    task = wf.tasks.get_task(s1.task)
    assert task.request is T.mk(S("Differentiate"), (parse("x^2"), S("x")))
    cands = wf.tasks.candidates_of(task.id)
    assert len(cands) == 1
    c = cands[0]
    assert c.artifact == s1.artifact
    assert c.validation == s1.judgment
    assert c.is_validated()
    assert c.state(wf.tasks, wf.scope) == "validated"


def test_command_without_request_opens_no_task():
    wf = new_workflow()
    s0 = wf.add(parse("x == 1"), Claim())
    assert s0.task is None, "Claim has no request shape"
    s1 = wf.add(parse("x + 1 == 2"), BothSides(pred=s0.id, op="add", operand=N(1)))
    assert s1.task is None, "BothSides has no request shape"


def test_applicability_is_queryable():
    """Query semantics: the kernel computes, the workflow asks."""
    wf = new_workflow()
    s0 = wf.add(parse("1/(x-1)"), Claim())          # carries the condition x-1 != 0
    app = wf.applicability_of(s0)
    assert app is not None
    assert app.is_conditional(), app
    s1 = wf.add(parse("x^2"), Claim())              # unconditional
    assert wf.applicability_of(s1).is_applicable()


def test_candidate_state_is_relative_to_the_query_scope():
    """A validation produced inside a branch does not read as validated outside.

    The guard of `x/x` is discharged by the branch assumption, so the same
    judgment is applicable inside the branch and only conditional in the parent
    scope. Candidate state is a query in a scope, not a stored flag, which is
    why the scope is passed in: otherwise a branch-local proof would be reported
    as a verified candidate where it does not hold.
    """
    from cas.kernel.mode import ExecutionMode
    wf = new_workflow(mode=ExecutionMode.DERIVATION)
    root = wf.scope
    wf.add(parse("x/x"), Claim())                # carries the condition x != 0
    group = wf.split_on(parse("x != 0"))
    case = group.cases[0]
    wf.enter(case.scope)
    s = wf.add(parse("x/x"), Claim())            # the branch assumption discharges it
    assert s.status == "committed", s.note
    task = wf.tasks.open_task(root, parse("x/x"))
    cand = wf.tasks.propose(task.id, s.artifact, validation=s.judgment)
    assert wf.tasks.is_applicable(s.judgment, case.scope)
    assert not wf.tasks.is_applicable(s.judgment, root)
    assert cand.state(wf.tasks, case.scope) == "validated"
    assert cand.state(wf.tasks, root) == "conditional"


def test_branch_local_unconditional_claim_is_not_applicable_outside_the_branch():
    """Usability needs both the condition question and the scope relation.

    A branch-local claim that carries no requirement at all has its conditions
    trivially discharged, so the kernel's `applicability` alone would report it
    applicable in the parent scope -- while `commit` refuses to use that same
    judgment as a premise there. `TaskStore.is_applicable` therefore also
    requires the judgment's own scope to be visible from the query scope: the
    candidate is validated inside the branch and only conditional outside it.
    """
    from cas.kernel.mode import ExecutionMode
    wf = new_workflow(mode=ExecutionMode.DERIVATION)
    root = wf.scope
    group = wf.split_on(parse("x != 0"))
    case = group.cases[0]
    wf.enter(case.scope)
    s = wf.add(parse("x^2"), Claim())            # unconditional: nothing to discharge
    assert s.status == "committed", s.note
    jid = s.judgment
    assert wf.store.requirements_of(jid) == (), "the nail needs the unconditional case"
    assert wf.tasks.is_applicable(jid, case.scope)
    assert not wf.tasks.is_applicable(jid, root)
    task = wf.tasks.open_task(root, parse("x^2"))
    cand = wf.tasks.propose(task.id, s.artifact, validation=jid)
    assert cand.state(wf.tasks, case.scope) == "validated"
    assert cand.state(wf.tasks, root) == "conditional"


def test_step_without_conclusion_has_no_applicability():
    wf = new_workflow()
    wf.add(parse("sin(x) == 1/2"), Claim())
    s = wf.add(parse("x == 1"), Solve(pred=0, var=S("x"), solution=N(1)))
    assert s.status == "undecided"
    assert wf.applicability_of(s) is None


# ---------------------------------------------------------------------------
# Branch
# ---------------------------------------------------------------------------

def test_split_builds_complementary_pair_with_coverage():
    from cas.kernel.mode import ExecutionMode
    wf = new_workflow(mode=ExecutionMode.DERIVATION)
    cond = parse("x != 0")
    g = wf.split_on(cond)
    assert len(g.cases) == 2
    assert g.cases[0].condition is cond
    assert g.cases[1].condition is T.not_(cond)
    assert g.cases[0].scope != g.cases[1].scope
    # coverage is registered after an independent checker re-check: what is recorded is
    # the **verified proposition** (the complementary disjunction itself), rather than
    # collapsing c or not-c to true at construction time
    assert g.coverage is not None
    cov = wf.store.get_judgment(g.coverage)
    assert cov.proposition is T.or_(cond, T.not_(cond))


def test_branch_scope_carries_condition_assumption():
    wf = new_workflow()
    cond = parse("x != 0")
    g = wf.split_on(cond)
    pos, neg = g.cases[0].scope, g.cases[1].scope
    props = [a.proposition for a in wf.store.scopes.assumptions(pos)]
    assert cond in props
    nprops = [a.proposition for a in wf.store.scopes.assumptions(neg)]
    assert T.not_(cond) in nprops


def test_sibling_branches_invisible():
    from cas.kernel.mode import ExecutionMode
    wf = new_workflow(mode=ExecutionMode.DERIVATION)
    g = wf.split_on(parse("x != 0"))
    a, b = g.cases[0].scope, g.cases[1].scope
    wf.enter(a)
    sa = wf.add(parse("x^2"), Claim())
    assert sa.judgment is not None
    wf.enter(b)
    # referencing a's conclusion from b: invisible, so refused
    from cas.workflow.command import BothSides
    sb = wf.add(parse("x^2 + 1"), BothSides(pred=sa.id, op="add", operand=N(1)))
    assert sb.status != "committed", sb.status


def test_promote_guard_lifts_guard_to_implication():
    wf = new_workflow()
    g = wf.split_on(parse("x != 0"))
    case = g.cases[0]
    elevated = wf.promote_guard(case, parse("y > 0"))
    assert elevated == T.mk(T.S("Implies"), (case.condition, parse("y > 0")))


def test_needs_split_status_wired_to_split():
    """Under the REQUEST_SPLIT policy a pending condition is handed back to the caller;
    after the branch opens, the condition is discharged through the assumptions."""
    from cas.kernel.commit import GuardPolicy
    from cas.kernel.mode import ExecutionMode
    wf = new_workflow(policy=GuardPolicy.REQUEST_SPLIT,
                  mode=ExecutionMode.DERIVATION)
    s0 = wf.add(parse("x/x"), Claim())
    assert s0.status == "needs_split", (s0.status, s0.note)
    cond = s0.guards[0]
    assert cond == parse("x != 0")
    assert s0.judgment is None

    g = wf.split_on(cond)
    wf.enter(g.cases[0].scope)                 # enter the x != 0 branch
    s1 = wf.add(parse("x/x"), Claim())
    assert s1.status == "committed", (s1.status, s1.note)
    assert wf.applicability_of(s1).is_applicable(), wf.applicability_of(s1)


# ---------------------------------------------------------------------------
# Constraint: a cycle in the candidate/constraint subgraph
# ---------------------------------------------------------------------------

def test_constraint_may_reference_candidates_and_cycle():
    """Loop integration: two construction constraints define each other. The task tree
    stays acyclic while the candidate graph becomes cyclic."""
    from cas.workflow.constraint import CandidateRef
    wf = new_workflow()
    # two candidates: T0 and T1 each with their own task and artifact
    s0 = wf.add(parse("i"), Claim())
    s1 = wf.add(parse("j"), Claim())
    ref0 = CandidateRef(task=s0.task, artifact=s0.artifact)
    ref1 = CandidateRef(task=s1.task, artifact=s1.artifact)

    u, v = S("_u"), S("_v")                     # subterm abstraction freezes the candidates into symbols
    a = parse("exp(x)*sin(x)")
    b = parse("exp(x)*cos(x)")
    c1 = wf.add_constraint(T.eq(u, T.plus(a, T.neg(v))), sources=(ref0, ref1))
    c2 = wf.add_constraint(T.eq(v, T.plus(T.plus(b, N(-1)), u)),
                           sources=(ref1, ref0))

    # candidate graph: ref0 -> c1, ref0 -> c2, ref1 -> c1, ref1 -> c2, mutually dependent
    edges = wf.constraints.dependency_edges()
    assert (ref0, c1.id) in edges and (ref1, c1.id) in edges
    assert (ref0, c2.id) in edges and (ref1, c2.id) in edges
    assert wf.constraints.involving(ref0) == (c1, c2)

    # the task tree is still acyclic: a tree edge only goes from an existing parent to a
    # child created later (increasing id)
    for parent, child in wf.tasks.task_tree_edges():
        assert parent < child, "the task tree has a backward edge"

    # the kernel proof graph is still acyclic: each Step's premises come from an earlier Step
    for step in wf.store.all_steps():
        for p in step.premises:
            assert wf.store.get_judgment(p).producer < step.id, "the proof graph has a backward edge"


def test_constraint_is_not_a_conclusion_automatically():
    """A Constraint may merely be an algorithmic construction, not necessarily a
    Judgment that can take part in a proof."""
    wf = new_workflow()
    before = wf.store.stats()["judgments"]
    c = wf.add_constraint(parse("_u == 1"))
    assert wf.store.stats()["judgments"] == before, "registering a constraint must not produce a conclusion"
    assert c.proposed_evidence is None
    # the constraint appears in the operation history (outputs carry a kind tag)
    kinds = [r.kind for r in wf.events.events()[-1].outputs]
    assert kinds == ["constraint"]


def test_constraint_valuation_verified_by_checker():
    """A linear constraint system of the loop-integration shape: the solver hands over a
    valuation and the checker re-checks it line by line without rerunning the solve.

    Rational rather than transcendental coefficients are used so the decision pipeline
    closes inside the algebraic fragment; a transcendental fragment is honestly
    undecided, which is a completeness boundary rather than a defect.
    """
    wf = new_workflow()
    u, v = S("_u"), S("_v")
    X = S("x")
    a = T.pw(X, N(2))                     # a = x^2
    b = X                                 # b = x
    wf.add_constraint(T.eq(u, T.plus(a, T.neg(v))))          # u = a - v
    wf.add_constraint(T.eq(v, T.plus(T.plus(b, N(-1)), u)))  # v = b - 1 + u

    # solution: u = (x^2 - x + 1)/2, v = (x^2 + x - 1)/2
    good = {u: parse("(x^2 - x + 1)/2"), v: parse("(x^2 + x - 1)/2")}
    steps = wf.verify_valuation(good)
    assert len(steps) == 2
    assert all(s.status == "committed" for s in steps), [(s.status, s.note) for s in steps]
    assert all(s.judgment is not None for s in steps)

    # wrong valuation: the constraint does not hold, so it is rejected
    wf2 = new_workflow()
    u2, v2 = S("_u"), S("_v")
    wf2.add_constraint(T.eq(u2, T.plus(a, T.neg(v2))))
    bad = wf2.verify_valuation({u2: N(0), v2: N(0)})
    assert bad[0].status == "refused", (bad[0].status, bad[0].note)
    assert bad[0].judgment is None
