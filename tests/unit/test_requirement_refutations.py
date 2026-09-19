# -*- coding: utf-8 -*-
"""Refutation recording through the store's reverse index.

Refutations used to be found by scanning every requirement on every commit. The
index is a pure data structure over the same syntactic-negation relation: these
tests pin that the recorded refutations and the applicability results are what
the scan produced, including the scope-visibility case where a requirement is
only refuted in a child scope.
"""

from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Accepted, Evidence
from cas.kernel.mode import ExecutionMode
from cas.kernel.services import register_core_checkers
from cas.kernel.store import KernelStore
from cas.kernel.verdict import YES
from cas.syntax import term as T
from cas.syntax.term import N, S, mk, not_


class AlwaysOk:
    def check(self, proposal, context, services):
        return Accepted()


class Demands:
    """Accepts and declares one direct requirement (simulating a needed guard)."""

    def __init__(self, cond):
        self.cond = cond

    def check(self, proposal, context, services):
        return Accepted(direct_requirements=(self.cond,))


class DecidesTrue:
    def decide(self, proposition, scope_id):
        return YES


def _store(*checkers):
    st = KernelStore()
    register_core_checkers(st)
    for cid, ck in checkers:
        st.checkers.register(cid, ck)
    return st


def _full_scan(store, proposition):
    """The removed per-commit scan over every requirement, as the reference."""
    def negated(p):
        if isinstance(p, T.Expr) and p.head.name == "Not":
            return p.args[0]
        return None

    neg = negated(proposition)
    return tuple(req.id for req in store.all_requirements()
                 if (neg is not None and req.proposition is neg)
                 or negated(req.proposition) is proposition)


def _commit_conditional(st, scope, proposition, checker):
    r = commit(st, StepProposal(scope=scope, conclusions=(proposition,),
                                evidence=Evidence(checker),
                                guard_policy=GuardPolicy.ALLOW_CONDITIONAL))
    assert r.is_committed(), r
    return r.judgments[0]


def test_reverse_index_recorded_refutations_match_the_full_scan():
    c1 = mk(S("Gt"), (S("x"), N(0)))
    c2 = mk(S("Ne"), (S("y"), N(0)))
    c3 = mk(S("Lt"), (S("z"), N(1)))
    st = _store(("t.d1", Demands(c1)), ("t.d2", Demands(c2)),
                ("t.d3", Demands(c3)), ("t.dneg", Demands(not_(c2))),
                ("t.ok", AlwaysOk()))
    root = st.scopes.create()

    jids = [_commit_conditional(st, root.id, S(f"p{i}"), f"t.d{i + 1}")
            for i in range(3)]
    jq = _commit_conditional(st, root.id, S("q"), "t.dneg")
    rids = [st.get_judgment(j).requirements[0] for j in jids + [jq]]
    assert rids == [0, 1, 2, 3]
    assert st.get_requirement(rids[3]).proposition is not_(c2)

    # Not(c1) refutes the first requirement, Not(c3) the third, c2 the
    # requirement whose own proposition is Not(c2).
    refuters = {}
    for prop in (not_(c1), not_(c3), c2):
        r = commit(st, StepProposal(scope=root.id, conclusions=(prop,),
                                    evidence=Evidence("t.ok")))
        assert r.is_committed(), r
        refuters[prop] = r.judgments[0]

    assert st.refutations_of(rids[0]) == (refuters[not_(c1)],)
    assert st.refutations_of(rids[1]) == ()
    assert st.refutations_of(rids[2]) == (refuters[not_(c3)],)
    assert st.refutations_of(rids[3]) == (refuters[c2],)
    apps = [st.applicability(j, root.id) for j in jids + [jq]]
    assert [a.is_inapplicable() for a in apps] == [True, False, True, True]
    assert apps[1].is_conditional()

    # The index answers exactly what the full scan would have found.
    for prop in (c1, c2, c3, not_(c1), not_(c2), not_(c3), S("p")):
        assert st.requirements_refuted_by(prop) == _full_scan(st, prop)


def test_discharged_requirement_is_not_refuted():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.d", Demands(cond)), ("t.ok", AlwaysOk()))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.d")),
               services=DecidesTrue(), mode=ExecutionMode.DERIVATION)
    assert r.is_committed()
    jid = r.judgments[0]
    rid = st.get_judgment(jid).requirements[0]
    assert st.is_discharged(rid, root.id)

    r2 = commit(st, StepProposal(scope=root.id, conclusions=(not_(cond),),
                                 evidence=Evidence("t.ok")))
    assert r2.is_committed()
    assert st.refutations_of(rid) == ()
    assert st.applicability(jid, root.id).is_applicable()


def test_refutation_in_a_child_scope_is_only_visible_there():
    cond = mk(S("Eq"), (S("u"), N(1)))
    st = _store(("t.d", Demands(cond)), ("t.ok", AlwaysOk()))
    root = st.scopes.create()
    child = st.scopes.child(root)
    jid = _commit_conditional(st, root.id, S("p"), "t.d")
    rid = st.get_judgment(jid).requirements[0]

    r2 = commit(st, StepProposal(scope=child.id, conclusions=(not_(cond),),
                                 evidence=Evidence("t.ok")))
    assert r2.is_committed()
    assert st.is_refuted(rid, child.id)
    assert not st.is_refuted(rid, root.id)
    assert st.applicability(jid, child.id).is_inapplicable()
    assert st.applicability(jid, root.id).is_conditional()
    assert st.refutations_of(rid) == (r2.judgments[0],)
