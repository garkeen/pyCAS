# -*- coding: utf-8 -*-
"""内核模型与提交协议验收（v4 §6.2–§6.10）。

这些测试把「提交是边界操作、条件与作用域是内核唯一实质职责」钉成钉子：
未决候选不落地、条件被否证即拒绝、清偿只登记不动原结论、作用域不可越权。
"""

import pytest

from cas.syntax.term import S, N, not_, mk
from cas.syntax import term as T
from cas.kernel.commit import (
    Committed, GuardPolicy, NeedsSplit, Refused, StepProposal, Undecided, commit,
)
from cas.kernel.evidence import Accepted, Evidence, UnknownResult
from cas.kernel.model import (
    Applicable, Conditional, Inapplicable, RequirementReason,
)
from cas.kernel.services import NullServices, register_core_checkers
from cas.kernel.store import KernelStore
from cas.kernel.verdict import NO, YES, Reason, unknown


# --- 测试用 checker / services ---

class AlwaysOk:
    def check(self, proposal, context, services):
        return Accepted()


class Demands:
    """通过，并声明一条直接条件（模拟需要的守卫）。"""
    def __init__(self, cond):
        self.cond = cond

    def check(self, proposal, context, services):
        return Accepted(direct_requirements=(self.cond,))


class Never:
    """未决（模拟片段外 / 预算耗尽）。"""
    def check(self, proposal, context, services):
        return UnknownResult(Reason.BUDGET, "测试用未决")


class StubServices:
    """按给定真值表判定的判定器（内核不知道它，只经接口调用）。"""

    def __init__(self, true=(), false=()):
        self.true = set(true)
        self.false = set(false)

    def decide(self, proposition, scope_id):
        if proposition in self.true:
            return YES
        if proposition in self.false:
            return NO
        return unknown(Reason.GUARDED)


def _store(*checkers):
    st = KernelStore()
    register_core_checkers(st)
    for cid, ck in checkers:
        st.checkers.register(cid, ck)
    return st


# --- 无条件结论 ---

def test_无条件结论落地():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.ok")))
    assert r.is_committed()
    j = st.get_judgment(r.judgments[0])
    assert j.requirements == ()
    assert st.applicability(j.id, root.id).is_applicable()


# --- 未决候选：策略是唯一处置点 ---

def test_未决候选在REQUIRE_PROVED下不落地():
    """v4 不变量 16 的内核机制：未决 → 什么都不写，不 fail-open。"""
    st = _store(("t.never", Never()))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.never"),
                                guard_policy=GuardPolicy.REQUIRE_PROVED))
    assert r.is_undecided()
    assert st.stats()["judgments"] == 0
    assert st.stats()["steps"] == 0
    assert st.stats()["requirements"] == 0


def test_checker未决在任何策略下都不落地():
    """不变量 16 的核心：GuardPolicy 管条件清偿，不管「结论没验过也放行」。"""
    st = _store(("t.never", Never()))
    root = st.scopes.create()
    for policy in GuardPolicy:
        r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                    evidence=Evidence("t.never"),
                                    guard_policy=policy))
        assert r.is_undecided(), policy
    assert st.stats()["steps"] == 0


def test_条件未决在ALLOW_CONDITIONAL下带条件落地():
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


def test_条件未决在REQUIRE_PROVED下不落地():
    """自动化简默认：守卫未决不静默落地（v3 的安全行为保留）。"""
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands")),
               services=StubServices())
    assert r.is_undecided()
    assert st.stats()["steps"] == 0


def test_策略REQUEST_SPLIT交回待决条件():
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


# --- 条件：登记、清偿、否证 ---

def test_条件未决则结论带条件():
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


def test_条件被否证则拒绝提交且不写账():
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


def test_条件已证则登记清偿且结论可应用():
    cond = mk(S("Ne"), (S("x"), N(0)))
    st = _store(("t.demands", Demands(cond)))
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.demands")),
               services=StubServices(true=(cond,)))
    assert r.is_committed()
    j = st.get_judgment(r.judgments[0])
    rid = j.requirements[0]
    assert st.is_discharged(rid, root.id)
    d = st.discharges_of(rid)[0]
    proof = st.get_judgment(d.by_judgment)
    assert proof.proposition is cond
    assert st.applicability(j.id, root.id).is_applicable()


def test_否证使原结论不适用但不删除():
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
    # 原结论仍在账本里（不物理删除、不级联销毁）
    assert st.get_judgment(jid).proposition is S("p")


# --- 作用域：可见性与卫生 ---

def test_子作用域结论不可反向用于父作用域():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    child = st.scopes.child(root)
    r1 = commit(st, StepProposal(scope=child.id, conclusions=(S("p"),),
                                 evidence=Evidence("t.ok")))
    assert r1.is_committed()
    # 回到父作用域引用子作用域结论 → 拒绝
    r2 = commit(st, StepProposal(scope=root.id, premises=(r1.judgments[0],),
                                 conclusions=(S("q"),),
                                 evidence=Evidence("t.ok")))
    assert r2.is_refused()
    assert "不可见" in r2.detail


def test_兄弟分支互不可见():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    a = st.scopes.child(root)
    b = st.scopes.child(root)
    ja = commit(st, StepProposal(scope=a.id, conclusions=(S("p"),),
                                 evidence=Evidence("t.ok"))).judgments[0]
    rb = commit(st, StepProposal(scope=b.id, premises=(ja,),
                                 conclusions=(S("q"),), evidence=Evidence("t.ok")))
    assert rb.is_refused()


def test_祖先作用域结论对后代可见():
    st = _store(("t.ok", AlwaysOk()))
    root = st.scopes.create()
    jr = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                 evidence=Evidence("t.ok"))).judgments[0]
    child = st.scopes.child(root)
    r = commit(st, StepProposal(scope=child.id, premises=(jr,),
                                conclusions=(S("q"),), evidence=Evidence("t.ok")))
    assert r.is_committed()


# --- 边界：不 fail-open ---

def test_checker未注册即未决不落地():
    st = KernelStore()
    root = st.scopes.create()
    r = commit(st, StepProposal(scope=root.id, conclusions=(S("p"),),
                                evidence=Evidence("t.missing")),
               services=NullServices())
    assert r.is_undecided()
    assert st.stats()["steps"] == 0


def test_scope不存在即拒绝():
    st = KernelStore()
    register_core_checkers(st)
    st.checkers.register("t.ok", AlwaysOk())
    r = commit(st, StepProposal(scope=999, conclusions=(S("p"),),
                                evidence=Evidence("t.ok")))
    assert r.is_refused()


def test_默认服务不判定任何命题():
    """NullServices 是诚实缺省：没接判定器 ≠ 判定为真。"""
    assert NullServices().decide(S("anything"), 0).is_unknown()
