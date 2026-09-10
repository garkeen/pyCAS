# -*- coding: utf-8 -*-
"""阶段4 验收：三图分离（v4 §8.2–§8.5、§8.9）。

产物图 / 任务图 / 操作历史图各自独立；Artifact 无真假、不能当数学前提；
Event.outputs 是连接操作与内核结论的唯一出口；undo/redo 只移指针不删事件。
"""

from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Evidence
from cas.syntax import term as T
from cas.frontend.parser import parse
from cas.syntax.term import S, N
from cas.workflow.workflow import Workflow, Claim, Diff, Solve, BothSides


def test_产物与结论分离_Artifact不能作为前提():
    """v4 不变量 4：Artifact 不能作为数学前提。"""
    wf = Workflow()
    s0 = wf.add(parse("x^2"), Claim())
    art = wf.artifacts.get(s0.artifact)
    assert art.value is parse("x^2")
    # 把 ArtifactId 当前提提交 → 内核查不到该 Judgment，拒绝
    r = commit(wf.store,
               StepProposal(scope=wf.scope, premises=(art.id,),
                            conclusions=(parse("x"),),
                            evidence=Evidence("assumption.entry"),
                            guard_policy=GuardPolicy.ALLOW_CONDITIONAL),
               services=wf.services)
    assert r.is_refused()


def test_每步产出一个产物且挂到产出事件():
    wf = Workflow()
    s0 = wf.add(parse("x^2"), Claim())
    s1 = wf.add(parse("2*x"), Diff(pred=s0.id, var=S("x")))
    assert wf.artifacts.get(s1.artifact).value is parse("2*x")
    ev = wf.events.events()[-1]
    assert wf.artifacts.get(s1.artifact).produced_by == ev.id
    kinds = [r.kind for r in ev.outputs]
    assert "artifact" in kinds and "judgment" in kinds and "task" in kinds


def test_操作历史与证明分离_undo只移指针():
    wf = Workflow()
    wf.add(parse("x^2"), Claim())
    wf.add(parse("2*x"), Diff(pred=0, var=S("x")))
    n_events = len(wf.events)
    n_steps = len(wf.all_steps())
    assert n_events == 2
    wf.undo()
    assert len(wf.events.visible()) == 1
    assert len(wf.events) == n_events, "undo 不得删除事件"
    assert len(wf.all_steps()) == n_steps, "undo 不得删除步骤/结论"
    wf.redo()
    assert len(wf.events.visible()) == 2


def test_溯源链_结论到事件():
    """Judgment → Step → Event：反向查询由 Event 侧倒排索引回答。"""
    wf = Workflow()
    s0 = wf.add(parse("x^2"), Claim())
    s1 = wf.add(parse("2*x"), Diff(pred=s0.id, var=S("x")))
    assert s1.judgment is not None
    producers = wf.events.producers_of("judgment", s1.judgment)
    assert len(producers) == 1
    ev = wf.events.events()[producers[0]]
    assert ev.command == "Diff"
    # 内核侧不反向引用：Step 里没有 event 字段
    step = wf.store.get_step(s1.judgment and wf.store.get_judgment(s1.judgment).producer)
    assert not hasattr(step, "event")


def test_任务与候选由数据推导状态():
    wf = Workflow()
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
    assert c.state(wf.tasks) in ("validated", "conditional")


def test_无请求形状的命令不开任务():
    wf = Workflow()
    s0 = wf.add(parse("x == 1"), Claim())
    assert s0.task is None, "Claim 无请求形状"
    s1 = wf.add(parse("x + 1 == 2"), BothSides(pred=s0.id, op="add", operand=N(1)))
    assert s1.task is None, "BothSides 无请求形状"


def test_适用性可被查询():
    """v4 §6.10 的查询语义：内核算，工作流问。"""
    wf = Workflow()
    s0 = wf.add(parse("1/(x-1)"), Claim())          # 带条件 x-1 != 0
    app = wf.applicability_of(s0)
    assert app is not None
    assert app.is_conditional(), app
    s1 = wf.add(parse("x^2"), Claim())              # 无条件
    assert wf.applicability_of(s1).is_applicable()


def test_无结论的步骤没有适用性():
    wf = Workflow()
    wf.add(parse("sin(x) == 1/2"), Claim())
    s = wf.add(parse("x == 1"), Solve(pred=0, var=S("x"), solution=N(1)))
    assert s.status == "unverified"
    assert wf.applicability_of(s) is None
