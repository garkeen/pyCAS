"""Workflow engine: submission boundary plus presentation records.

**The workflow is not a truth kernel.** It verifies nothing itself: `add`
assembles a StepProposal and hands it to `kernel.commit`, where a registered
checker re-checks it and the kernel records it. What the workflow owns is what
problem the user is solving, where the focus is, and the operation history,
together with mapping kernel conclusions into frontend-readable step records.

Four states, named after the kernel commit result ADT rather than invented
vocabulary:

    committed    submitted (possibly with undischarged conditions)
    refused      refuted (Refused)
    undecided    not re-checked (Undecided); must not enter later trusted
                 reasoning
    needs_split  the policy requests a case split (NeedsSplit)

"An unverified candidate cannot enter trusted reasoning" lands on the
`undecided` state: the old implementation recorded every non-NO result as open,
which was fail-open.

A step has no subclasses and there is no per-type isinstance dispatch: checkers
are looked up by id in the registry. A command is a pure data record and the
kind of claim is declared by its `checker_id`; the closed Derivation ADT and the
"command class -> verifier" mapping table are gone.

Guards are not extracted by the workflow and attached to steps: the checker
reports direct conditions, the kernel builds Requirements, attempts discharge
and inherits from premises. `WorkflowStep.guards` here is only the frontend
projection of the kernel's undischarged requirements.

Removed: cascade destruction of descendants when a predecessor is dead. The
original conclusion is kept and applicability is computed by the kernel per
scope.

Domain membership: a step's domain is recorded through the projection layer's
membership test, never by leaf sniffing.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.syntax.term import S
from cas.errors import BranchError, ScopeError
from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Evidence
from cas.kernel.model import (Assumption, ContextReadSet, Declaration,
                              Definition)
from cas.workflow.artifact import ArtifactStore
from cas.workflow.branch import BranchCase, BranchStore, promote_guard
from cas.workflow.command import Command, ValuationCheck
from cas.workflow.constraint import ConstraintStore
from cas.workflow.event import EventLog, Ref
from cas.workflow.ids import RevisionId
from cas.workflow.task import TaskStore

# ---------------------------------------------------------------------------
# Command shapes live in cas/workflow/command.py: a command is a pure data
# record whose claim kind is declared by `checker_id`, with no functional
# subclasses and no dispatch table.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Step: an immutable presentation record (trusted conclusions live in the kernel
# ledger)
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class WorkflowStep:
    """A workflow step record (the presentation layer, not the kernel
    model.Step).

    The kernel Step is a mathematical dependency edge; this class records what
    the user did and carries presentation data (domain, target, command). The
    two used to share a name, hence the explicit naming here.
    """
    id: int
    content: object                 # Term
    command: Command                # command; the claim kind is in its checker_id
    guards: tuple = ()              # undischarged conditions (projection of kernel Requirements)
    status: str = "undecided"       # "committed"|"refused"|"undecided"|"needs_split"
    note: str = ""
    target: tuple = ()
    domain: str = ""                # domain of the content, assigned by projection
    judgment: object = None         # kernel JudgmentId; None when not committed
    artifact: object = None         # artifact id
    task: object = None             # TaskId of the computation problem, if any


# The manual/interactive channel: explicit rule application may produce
# conditional conclusions. Automatic simplification uses REQUIRE_PROVED and does
# not go through this workflow.
_POLICY = GuardPolicy.ALLOW_CONDITIONAL


class Workflow:
    """Submission boundary plus presentation records."""

    def __init__(self, store, services, algorithms=None, mode=None, policy=None):
        """The ledger and the decision services are injected by the runtime.

        The workflow does not know `cas.math`, so the mathematical checkers, the
        decision services and the few algorithms it occasionally needs are all
        injected by `cas.runtime.new_workflow()`. That makes "the workflow does
        not know which checkers exist or how algorithms are implemented" a
        structural fact rather than a convention.
        """
        from cas.kernel.mode import DEFAULT_MODE
        if store is None or services is None:
            raise RuntimeError(
                "Workflow needs a ledger and decision services: construct it "
                "with cas.runtime.new_workflow()")
        self.store = store
        self.services = services
        self.algorithms = algorithms
        self.mode = mode if mode is not None else DEFAULT_MODE
        self.policy = policy if policy is not None else _POLICY
        self._root = self.store.scopes.create()
        self.scope = self._root.id
        # Three separated graphs: artifacts, tasks, operation history.
        self.artifacts = ArtifactStore()
        self.tasks = TaskStore(kernel=self.store)
        self.events = EventLog()
        self.branches = BranchStore()
        self.constraints = ConstraintStore()
        self._steps: dict = {}
        self._next_id = 0
        # Undo/redo state: which scope version was current at each revision in
        # view, and which event produced each step record. Both are written at
        # the single site that appends an event / creates a step and are never
        # removed: moving the pointer back never deletes history.
        self._scope_at = {RevisionId(0): self.scope}
        self._event_of_step: dict = {}

    def get(self, sid) -> WorkflowStep:
        return self._steps[sid]

    def all_steps(self):
        """Every step ever recorded, in recording order: the audit/history view
        (`visible_steps` is what the current revision shows)."""
        return [self._steps[i] for i in range(self._next_id)]

    def visible_steps(self):
        """The steps whose operation is in the current event view, in view order.

        A step stays in `_steps` after an undo; it drops out of this list
        because its event is no longer visible, while `all_steps()` still holds
        it for history.
        """
        view = {ev.id for ev in self.events.visible()}
        return [self._steps[i] for i in range(self._next_id)
                if self._event_of_step.get(i) in view]

    def add(self, content, command, note="", target=()) -> WorkflowStep:
        # The context a step is submitted in is the current scope version. A
        # committed claim afterwards grows the scope by appending the
        # assumption, and this step keeps the version it was checked in.
        submitted = self.scope
        pred_id = command.pred
        premises = ()
        if pred_id is not None:
            pstep = self._steps.get(pred_id)
            if pstep is None or pstep.judgment is None:
                return self._record(content, command, "undecided",
                                    note or "predecessor has no dependable conclusion",
                                    target, (), scope=submitted)
            premises = (pstep.judgment,)

        # The proposal is committed first; a claim's proposition becomes a scope
        # assumption only once the commit succeeds. Registering before commit
        # would leave a refused or undecided claim polluting later decisions in
        # this scope. The checker verifies the claim from the command payload
        # (registers_assumption), not from the scope, so it does not need the
        # assumption to be present at check time.
        proposal = StepProposal(scope=submitted, premises=premises,
                                conclusions=(content,),
                                evidence=Evidence(command.checker_id, command),
                                guard_policy=self.policy)
        res = commit(self.store, proposal, services=self.services,
                     mode=self.mode)

        if res.is_committed():
            if command.registers_assumption:
                # The conclusion keeps the context it was checked in; later
                # submissions see the assumption because the scope grows into a
                # new version rather than the old id changing under its readers.
                self.scope = self._grow_scope(
                    submitted, assumptions=(Assumption(content),)).id
            j = self.store.get_judgment(res.judgments[0])
            guards = tuple(self.store.get_requirement(r).proposition
                           for r in j.requirements)
            return self._record(content, command, "committed", note, target,
                                guards, j.id, scope=submitted)
        if res.is_refused():
            return self._record(content, command, "refused",
                                res.detail or note, target, (), scope=submitted)
        if res.is_needs_split():
            # The policy requests a case split: hand the pending condition back
            # to the caller, which opens branches via split_on.
            return self._record(content, command, "needs_split",
                                "case split required", target,
                                tuple(res.conditions), scope=submitted)
        return self._record(content, command, "undecided",
                            getattr(res, "detail", "") or "not re-checked",
                            target, (), scope=submitted)

    def _append_event(self, command, inputs=(), outputs=()):
        """Record one operation and note the scope version the new revision
        starts from.

        Undo and redo move the pointer by revision, so the version that was
        current at each revision has to be remembered; doing it here, at the
        single site that appends an event, keeps the mapping complete for every
        operation (a step record, a split, a constraint, a declaration,
        entering a scope).
        """
        ev = self.events.append(command=command, inputs=tuple(inputs),
                                outputs=tuple(outputs))
        self._scope_at[self.events.current_revision()] = self.scope
        return ev

    def _record(self, content, command, status, note, target, guards,
                judgment=None, inputs=None, scope=None) -> WorkflowStep:
        # The records below belong to the version the step was submitted in; the
        # workflow's current scope may already be a later version (a claim grew
        # it), so the caller passes the version explicitly.
        scope = self.scope if scope is None else scope
        # 1. computation product (no truth value)
        artifact = self.artifacts.create(scope, content)
        # 2. computation problem plus candidate (commands with no request head
        #    open no task)
        task = self._open_task(command, artifact, judgment, scope)
        # 3. operation history: outputs is the only exit connecting an operation
        #    to kernel conclusions
        if inputs is None:
            pred_id = command.pred
            inputs = () if pred_id is None else (pred_id,)
        ev = self._append_event(
            command=command.name,
            inputs=tuple(inputs),
            outputs=tuple(
                Ref(kind, ident)
                for kind, ident in (("artifact", artifact.id),
                                    ("task", task and task.id),
                                    ("judgment", judgment))
                if ident is not None))
        self.artifacts.attach(artifact.id, ev.id)

        s = WorkflowStep(id=self._next_id, content=content, command=command,
                         guards=tuple(guards), status=status, note=note,
                         target=tuple(target), domain=self._domain_of(content),
                         judgment=judgment, artifact=artifact.id,
                         task=None if task is None else task.id)
        self._steps[self._next_id] = s
        self._event_of_step[self._next_id] = ev.id
        self._next_id += 1
        return s

    def _open_task(self, command, artifact, judgment, scope):
        """Open a task by the request head the command declares and register the
        candidate. Returns None for commands with no request head.

        A request is an ordinary term, not a closed TaskKind enum; the head
        string comes from the command and the workflow does not know its
        mathematical meaning.
        """
        head = command.request
        if not head:
            return None
        pred_id = command.pred
        pstep = self._steps.get(pred_id) if pred_id is not None else None
        pred = pstep.content if pstep is not None else artifact.value
        var = command.var
        args = (pred, var) if var is not None else (pred,)
        task = self.tasks.open_task(scope, T.mk(S(head), args))
        self.tasks.propose(task.id, artifact.id, judgment)
        return task

    # --- constraints (equations constructed by computation; the cycle lives in
    #     the candidate <-> constraint subgraph) ---

    def add_constraint(self, relation, sources=(), proposed_evidence=None):
        """Register a construction relation. This produces no Judgment: a
        constraint is an artifact-level construction, and becoming a conclusion
        still requires commit and an accepting checker."""
        c = self.constraints.add(self.scope, relation, sources,
                                 proposed_evidence)
        self._append_event(command="AddConstraint", inputs=(),
                           outputs=(Ref("constraint", c.id),))
        return c

    def solve_constraints(self, unknowns):
        """Solve the constraint system and re-check it. The solver is
        untrusted and may hand over a wrong candidate; re-checking belongs to a
        checker.

        Returns `(valuation, steps, complete)`; a solver refusal returns
        `(None, (), False)`.
        """
        if self.algorithms is None:
            raise RuntimeError(
                "no algorithm facade injected: construct with "
                "cas.runtime.new_workflow()")
        rels = tuple(c.relation for c in self.constraints.all())
        res = self.algorithms.solve_linear_constraints(rels, unknowns)
        if res is None:
            return None, (), False
        valuation, complete = res
        return valuation, self.verify_valuation(valuation), complete

    def verify_valuation(self, valuation):
        """Re-check "this assignment satisfies the constraint system" item by
        item.

        `valuation` is a certificate handed over by the solver, which is
        untrusted and may be wrong. Each constraint is submitted separately and
        re-checked by the `constraint.satisfied` checker for its instance and
        vanishing; the solver's own report does not count.
        """
        out = []
        for c in self.constraints.all():
            inst = T.subst(c.relation, dict(valuation))
            out.append(self.add(inst, ValuationCheck(constraint=c,
                                                     valuation=valuation)))
        return tuple(out)

    # --- branching ---

    def split_on(self, condition):
        """Build a pair of branch scopes for `condition` and `not condition` and
        try to prove coverage.

        Sibling branches cannot see each other, and branch contexts cannot be
        merged directly; merging is performed by `merge_branches` under its five
        checks. This method only lands the coverage part (the law of excluded
        middle, a syntactic tautology decided on the verification side).
        """
        scopes = self.store.scopes
        parent = scopes.get(self.scope)
        cases = []
        for cond, label in ((condition, "+"), (T.not_(condition), "-")):
            child = scopes.child(parent, assumptions=(Assumption(cond),))
            cases.append(BranchCase(condition=cond, scope=child.id, label=label))
        # The group names its parent by lineage, not by version: the version the
        # branches forked from stays frozen while the parent context may grow,
        # and merge resolves the lineage's current version as the scope the
        # merged conclusion lands in.
        group = self.branches.create(scopes.lineage_of(self.scope), cases)

        # Coverage: the disjunction of the conditions, independently re-checked
        # by a checker. The decision is made on the verification side rather
        # than by construction-time collapse.
        prop = T.or_(*[c.condition for c in cases])
        r = commit(self.store,
                   StepProposal(scope=self.scope, conclusions=(prop,),
                                evidence=Evidence("branch.coverage", group.id),
                                guard_policy=GuardPolicy.REQUIRE_PROVED),
                   services=self.services, mode=self.mode)
        self.branches.set_coverage(group.id, r.judgments[0] if r.is_committed()
                                   else None)
        self._append_event(command="Split", inputs=(),
                           outputs=(Ref("branch", group.id),))
        return self.branches.get(group.id)

    def enter(self, scope):
        """Enter a scope lineage at its current version: later submissions
        happen in that context.

        An id naming an older version resolves to the lineage's head, since
        entries only ever append on top of the current version. Entering is an
        operation of its own and is recorded in the event view -- it produces
        no conclusion, task or artifact; what it changes is the context later
        submissions use. Undo and redo therefore move through it like through
        any other operation.
        """
        self.scope = self.store.scopes.head_of(scope)
        self._append_event(command="Enter")
        return self.scope

    def promote_guard(self, case, guard):
        """Promote an undischarged guard from inside a branch to the parent as
        `C_i => G_i`."""
        return promote_guard(case.condition, guard)

    def merge_branches(self, group, proposition, results):
        """Merge branches: reason by cases.

        `results` is ordered like `group.cases` and holds the step that answers
        in each branch. A merge does not union the branch contexts. Rather, each
        branch concludes the same proposition and the branch conditions cover
        the parent problem, so the proposition holds in the parent scope; each
        branch's open guards are promoted to `C_i => G_i`. The read dependencies
        of the merge step are the union of the branches' read sets.

        The group names its parent by lineage, not by version. The merge
        resolves that lineage's current version as the scope the conclusion
        lands in, so an undo that later forked the version chain does not
        strand the group on an abandoned version. It must be called from a
        scope that descends from the parent lineage and is not inside one of
        the branches being merged.

        Five checks: (1) coverage holds; (2) every branch answers the same task
        (compared by request term: each branch opens its own task, so ids differ
        but the request must match); (3) each branch result holds in its own
        scope; (4) no helper symbol escaped; (5) open conditions were promoted
        correctly (the checker recomputes, the kernel decides and discharges).
        Failure raises BranchError rather than guessing or degrading.

        Branch conclusions are not premises of this step because a child-scope
        conclusion must not be used in a parent scope, so the only premise is
        the coverage conclusion in the parent. The branch conclusions are read
        from the kernel record for checks (2) and (3) and handed to the checker
        in the payload for consistency checking. Making that loop independently
        re-checked by the kernel would require commit to support implication
        introduction, which is a design decision not yet taken.
        """
        scopes = self.store.scopes
        parent = scopes.head_of(group.parent_lineage)
        chain = scopes.chain(self.scope)
        if not any(s.lineage == group.parent_lineage for s in chain):
            raise BranchError("merge must happen in the branch's parent scope "
                              "(call enter first)")
        if any(s.id == case.scope for s in chain for case in group.cases):
            raise BranchError("merge must not be performed inside one of the "
                              "branches being merged")
        if len(results) != len(group.cases):
            raise BranchError("number of branch results does not match the "
                              "number of cases")
        if group.coverage is None:                       # (1) coverage
            raise BranchError("branch coverage was not proved; cannot merge")
        answers = []                                     # (3) each holds in its scope
        for case, st in zip(group.cases, results):
            if st.judgment is None:
                raise BranchError(f"branch result has no dependable conclusion: #{st.id}")
            j = self.store.get_judgment(st.judgment)
            if scopes.lineage_of(j.scope) != scopes.lineage_of(case.scope):
                raise BranchError(f"branch result #{st.id} is not in its branch scope")
            answers.append(j.proposition)
        requests = []                                    # (2) the same task
        for st in results:
            if st.task is None:
                raise BranchError(f"branch result #{st.id} answered no request-shaped task")
            requests.append(self.tasks.get_task(st.task).request)
        if any(r is not requests[0] for r in requests):
            raise BranchError("the branches did not answer the same task")
        escaped = scopes.escapes(                         # (4) no symbol escapes
            parent, proposition)
        if escaped:
            raise BranchError(f"merge conclusion contains an escaped local symbol: {escaped!r}")
        conditions = tuple(c.condition for c in group.cases)
        guards = tuple(tuple(st.guards) for st in results)
        for g in (g for gs in guards for g in gs):       # (4) promoted guards must not escape either
            esc = scopes.escapes(parent, g)
            if esc:
                raise BranchError(f"promoted guard contains an escaped local symbol: {esc!r}")

        merged_reads = ContextReadSet()                  # read deps: union over branches
        for st in results:
            producer = self.store.get_judgment(st.judgment).producer
            merged_reads = merged_reads.merge(self.store.get_step(producer).reads)

        cmd = Command(name="MergeBranches", checker_id="branch.merge",
                      conditions=conditions, guards=guards,
                      answers=tuple(answers))
        proposal = StepProposal(
            scope=parent,
            premises=(group.coverage,),                  # the only parent-visible premise
            conclusions=(proposition,),
            evidence=Evidence("branch.merge", cmd),
            guard_policy=self.policy)
        res = commit(self.store, proposal, services=self.services,
                     mode=self.mode, inherited_reads=merged_reads)
        inputs = tuple(st.id for st in results)
        if res.is_committed():                           # (5) promoted conditions recorded by the kernel
            j = self.store.get_judgment(res.judgments[0])
            out = tuple(self.store.get_requirement(r).proposition
                        for r in j.requirements)
            return self._record(proposition, cmd, "committed", "", (), out, j.id,
                                inputs=inputs)
        if res.is_refused():
            return self._record(proposition, cmd, "refused", res.detail, (), (),
                                inputs=inputs)
        if res.is_needs_split():
            return self._record(proposition, cmd, "needs_split",
                                "case split required", (),
                                tuple(res.conditions), inputs=inputs)
        return self._record(proposition, cmd, "undecided",
                            getattr(res, "detail", "") or "not re-checked", (), (),
                            inputs=inputs)

    # --- applicability query (the kernel computes, the workflow asks) ---

    def applicability_of(self, step):
        """Applicability of this step's conclusion in the current scope, or None
        when it has no conclusion."""
        if step.judgment is None:
            return None
        return self.store.applicability(step.judgment, self.scope)

    # --- declare / define ---

    def _grow_scope(self, parent_id, *, declarations=(), definitions=(),
                    assumptions=()):
        """Append entries on top of `parent_id` and return the new version.

        The scope store only extends the head of a version chain, because
        extending an older version in place would leave which version new
        entries land on ambiguous. After an undo the workflow pointer
        deliberately names an older version again, so a new entry starts a new
        chain under that version with the fork constructor; both histories stay
        addressable and no kernel record is rewritten. Without an undo the
        ordinary extension keeps the session on one lineage.
        """
        scopes = self.store.scopes
        parent = scopes.get(parent_id)
        if scopes.head_of(parent_id) == parent_id:
            return scopes.extend(parent, declarations=declarations,
                                 definitions=definitions,
                                 assumptions=assumptions)
        return scopes.child(parent, declarations=declarations,
                            definitions=definitions, assumptions=assumptions)

    def declare(self, symbol, sort):
        """Declare `symbol : sort`.

        The symbol must be fresh: neither declared nor defined along the chain.
        A declaration is not a proposition and does not enter the decision
        channel; it records which class the symbol belongs to, for consumers
        such as the type/domain layer. The declaration is recorded as an
        operation, so undo moves the scope pointer back to the version without
        it and redo re-applies it. Returns the new scope version, which also
        becomes the workflow's current scope: entries append on top of the
        previous version, so later steps must be submitted in the new one to see
        the declaration.
        """
        self._require_fresh(symbol, "declaration")
        new = self._grow_scope(self.scope,
                               declarations=(Declaration(symbol, sort),))
        self.scope = new.id
        self._append_event(command="Declare",
                           outputs=(Ref("scope", new.id),))
        return new

    def define(self, symbol, body):
        """Define `symbol := body`: a local alias, not an equation to prove.

        The kernel checks four things; the first three are checked here at
        definition time and the fourth is enforced at the scope boundary:

        1. the left-hand symbol is fresh: neither declared nor defined along
           the chain;
        2. no illegal recursion: after alias expansion `body` must not contain
           `symbol` (mutual recursion included);
        3. the right-hand side is well bound in scope: it may use earlier
           entries of this scope and entries of ancestors, but must not
           reference a local symbol of another scope (a sibling branch, say);
        4. a local symbol must not leak into a conclusion outside the scope,
           enforced by commit's first step via ScopeStore.escapes.

        Point 3 is "sequentially visible": a later definition in the same scope
        may reference an earlier alias. Reference implementations agree -- for
        example Maxima's `block([expr, W_subst], expr: ..., W_subst: ..., ...)`,
        FriCAS function bodies `delta := p2-p1; len := arrowScale * length
        delta`, Reduce and yacas. Their hygiene discipline targets escaping
        (Maxima restores on block exit, Mathematica renames in Module), not
        same-scope references. Definitions here are lazy aliases, closer to
        Mathematica's SetDelayed/Module, so the expanded reference graph must be
        acyclic.

        Returns the new scope version; the symbol can afterwards be resolved
        through ScopeStore.lookup_definition, and the new version becomes the
        workflow's current scope. The definition is recorded as an operation,
        so undo removes it from view and redo re-applies it.
        """
        self._require_fresh(symbol, "definition")
        if self._alias_cycle(symbol, body):
            raise ScopeError(f"illegal recursive definition: {symbol!r} appears "
                             "in its own right-hand side after alias expansion")
        bad = self.store.scopes.escapes(self.scope, body)
        if bad:
            raise ScopeError(f"definition right-hand side references a local "
                             f"symbol of another scope: {bad!r}")
        new = self._grow_scope(self.scope,
                               definitions=(Definition(symbol, body),))
        self.scope = new.id
        self._append_event(command="Define",
                           outputs=(Ref("scope", new.id),))
        return new

    def _alias_cycle(self, symbol, body, seen=None) -> bool:
        """Whether `symbol` appears in `body` after alias expansion.

        Checking direct self-reference is not enough: `u := v` (where v is free
        at that point) followed by `v := u` creates an alias cycle that no one
        can expand, which is infinite expansion semantically. Expansion uses the
        definition table along the current scope chain, and `seen` stops
        existing cycles, so termination is guaranteed.
        """
        fv = T.free_vars(body)
        if symbol in fv:
            return True
        seen = set() if seen is None else seen
        for f in fv:
            if f in seen:
                continue
            inner = self.store.scopes.lookup_definition(self.scope, f)
            if inner is None:
                continue
            seen.add(f)
            if self._alias_cycle(symbol, inner, seen):
                return True
        return False

    def _require_fresh(self, symbol, what):
        """The symbol must be fresh: neither defined nor declared along the
        chain."""
        scopes = self.store.scopes
        if scopes.lookup_definition(self.scope, symbol) is not None:
            raise ScopeError(f"{what} symbol already defined along the chain: {symbol!r}")
        if any(d.symbol is symbol for d in scopes.declarations(self.scope)):
            raise ScopeError(f"{what} symbol already declared along the chain: {symbol!r}")

    # --- undo / redo: the view, the visible steps and the scope version move
    #     together ---

    def undo(self):
        """Move the revision pointer one step back and restore the scope pointer
        to the version that was current at the resulting revision.

        The event view and the visible step set follow the revision because they
        are read through the log's view; nothing is deleted, so a redo can put
        the operation back. A pointer that cannot move (already at the first
        revision) leaves the scope pointer untouched.
        """
        before = self.events.current_revision()
        rev = self.events.undo()
        if rev != before:
            self.scope = self._scope_at[rev]
        return rev

    def redo(self):
        """Move the revision pointer one step forward, if an operation is on the
        redo stack, restoring the scope pointer the same way `undo` does."""
        before = self.events.current_revision()
        rev = self.events.redo()
        if rev != before:
            self.scope = self._scope_at[rev]
        return rev

    def _domain_of(self, content) -> str:
        """The domain of a step, assigned by the projection layer through the
        injected facade, never by leaf sniffing."""
        if self.algorithms is None:
            return ""
        return self.algorithms.domain_of(content)
