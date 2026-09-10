# -*- coding: utf-8 -*-
"""分支合并（v4 §8.8 五条检查）与读依赖归并（§6.11）。

`split_on` 只落「覆盖」一条，合并没有实现——`ContextReadSet.merge` 因此没有
消费者。本文件钉住合并接通后的行为：五条检查各自可拒、成功时在父作用域落地、
读依赖按各支取并。
"""

import pytest

from cas.runtime import bootstrap, new_workflow
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

bootstrap()

X = S("x")


def _two_branch_derivatives(wf):
    """建一对分支，各支对同一前驱求导（请求项相同）。"""
    s0 = wf.add(parse("x^2"), Claim())
    group = wf.split_on(parse("x > 0"))
    results = []
    for case in group.cases:
        wf.enter(case.scope)
        results.append(wf.add(parse("2*x"), Diff(pred=s0.id, var=X)))
    return group, s0, tuple(results)


# ---------------------------------------------------------------------------
# 成功路径：五条检查全过
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
    assert wf.store.get_judgment(m.judgment).scope == root


def test_merge_records_branch_steps_as_event_inputs():
    """合并是操作：事件把它消费的分支步骤记为 inputs（§8.9）。"""
    wf = new_workflow()
    group, _s0, results = _two_branch_derivatives(wf)
    wf.enter(group.parent_scope)
    m = wf.merge_branches(group, parse("2*x"), results)
    ids = wf.events.producers_of("artifact", m.artifact)
    assert ids, "合并步应产出产物并挂到事件"
    ev = wf.events.events()[ids[0]]
    assert set(ev.inputs) == {st.id for st in results}


# ---------------------------------------------------------------------------
# 五条检查各自可拒
# ---------------------------------------------------------------------------

def test_merge_requires_coverage():
    """① 未证覆盖不得合并。"""
    wf = new_workflow()
    empty = BranchStore().create(wf.scope, ())
    with pytest.raises(BranchError):
        wf.merge_branches(empty, parse("2*x"), ())


def test_merge_requires_parent_scope():
    """合并必须在父作用域做——在分支里合并是误用。"""
    wf = new_workflow()
    group, _s0, results = _two_branch_derivatives(wf)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("2*x"), results)


def test_merge_rejects_different_requests():
    """② 各支必须回答同一个任务（按请求项判）。"""
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    group = wf.split_on(parse("x > 0"))
    wf.enter(group.cases[0].scope)
    a = wf.add(parse("2*x"), Diff(pred=s0.id, var=X))       # Differentiate
    wf.enter(group.cases[1].scope)
    b = wf.add(parse("x^2"), Rewrite(pred=s0.id))           # Simplify
    wf.enter(group.parent_scope)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("2*x"), (a, b))


def test_merge_rejects_branch_without_conclusion():
    """③ 分支结果必须各自在其 scope 中有可依赖结论。"""
    wf = new_workflow()
    s0 = wf.add(parse("Log(x)"), Claim())      # 微分未建：结果未决，无结论
    group = wf.split_on(parse("x > 0"))
    results = []
    for case in group.cases:
        wf.enter(case.scope)
        results.append(wf.add(parse("1/x"), Diff(pred=s0.id, var=X)))
    assert all(st.judgment is None for st in results)
    wf.enter(group.parent_scope)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("1/x"), tuple(results))


def test_merge_rejects_escaped_local_symbol():
    """④ 分支局部符号不得随合并结论逃逸到父作用域。"""
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    group = wf.split_on(parse("x > 0"))
    results = []
    for case in group.cases:
        wf.enter(case.scope)
        wf.define(S("u"), parse("x^2"))
        results.append(wf.add(parse("2*x"), Diff(pred=s0.id, var=X)))
    wf.enter(group.parent_scope)
    with pytest.raises(BranchError):
        wf.merge_branches(group, T.times(S("u"), N(2)), tuple(results))


def test_merge_rejects_result_count_mismatch():
    wf = new_workflow()
    group, _s0, results = _two_branch_derivatives(wf)
    wf.enter(group.parent_scope)
    with pytest.raises(BranchError):
        wf.merge_branches(group, parse("2*x"), results[:1])


# ---------------------------------------------------------------------------
# 读依赖归并（§6.11）
# ---------------------------------------------------------------------------

def test_commit_merges_inherited_reads():
    """`commit` 把继承的读依赖并入本步读集——分支合并的结论依赖各支读过的
    事实，这正是 `ContextReadSet.merge` 的消费者。"""
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
