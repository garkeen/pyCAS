# -*- coding: utf-8 -*-
"""阶段4 验收：三图分离（v4 §8.2–§8.5、§8.9）。

产物图 / 任务图 / 操作历史图各自独立；Artifact 无真假、不能当数学前提；
Event.outputs 是连接操作与内核结论的唯一出口；undo/redo 只移指针不删事件。
"""

from cas.runtime import new_workflow
from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Evidence
from cas.syntax import term as T
from cas.frontend.parser import parse
from cas.syntax.term import S, N
from cas.workflow.workflow import Claim, Diff, Solve, BothSides


def test_产物与结论分离_Artifact不能作为前提():
    """v4 不变量 4：Artifact 不能作为数学前提。"""
    wf = new_workflow()
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
    wf = new_workflow()
    s0 = wf.add(parse("x^2"), Claim())
    s1 = wf.add(parse("2*x"), Diff(pred=s0.id, var=S("x")))
    assert wf.artifacts.get(s1.artifact).value is parse("2*x")
    ev = wf.events.events()[-1]
    assert wf.artifacts.get(s1.artifact).produced_by == ev.id
    kinds = [r.kind for r in ev.outputs]
    assert "artifact" in kinds and "judgment" in kinds and "task" in kinds


def test_操作历史与证明分离_undo只移指针():
    wf = new_workflow()
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
    wf = new_workflow()
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
    assert c.state(wf.tasks) in ("validated", "conditional")


def test_无请求形状的命令不开任务():
    wf = new_workflow()
    s0 = wf.add(parse("x == 1"), Claim())
    assert s0.task is None, "Claim 无请求形状"
    s1 = wf.add(parse("x + 1 == 2"), BothSides(pred=s0.id, op="add", operand=N(1)))
    assert s1.task is None, "BothSides 无请求形状"


def test_适用性可被查询():
    """v4 §6.10 的查询语义：内核算，工作流问。"""
    wf = new_workflow()
    s0 = wf.add(parse("1/(x-1)"), Claim())          # 带条件 x-1 != 0
    app = wf.applicability_of(s0)
    assert app is not None
    assert app.is_conditional(), app
    s1 = wf.add(parse("x^2"), Claim())              # 无条件
    assert wf.applicability_of(s1).is_applicable()


def test_无结论的步骤没有适用性():
    wf = new_workflow()
    wf.add(parse("sin(x) == 1/2"), Claim())
    s = wf.add(parse("x == 1"), Solve(pred=0, var=S("x"), solution=N(1)))
    assert s.status == "unverified"
    assert wf.applicability_of(s) is None


# ---------------------------------------------------------------------------
# §8.8 Branch
# ---------------------------------------------------------------------------

def test_split建一对互补分支且覆盖成立():
    from cas.kernel.mode import ExecutionMode
    wf = new_workflow(mode=ExecutionMode.DERIVATION)
    cond = parse("x != 0")
    g = wf.split_on(cond)
    assert len(g.cases) == 2
    assert g.cases[0].condition is cond
    assert g.cases[1].condition is T.not_(cond)
    assert g.cases[0].scope != g.cases[1].scope
    # 覆盖经 checker 独立复核后登记：记录的是**被验证的那个命题**
    # （互补析取本身；不靠构造期把 c ∨ ¬c 坍缩成 ⊤，v4 §2.1）
    assert g.coverage is not None
    cov = wf.store.get_judgment(g.coverage)
    assert cov.proposition is T.or_(cond, T.not_(cond))


def test_分支作用域携带条件假设():
    wf = new_workflow()
    cond = parse("x != 0")
    g = wf.split_on(cond)
    pos, neg = g.cases[0].scope, g.cases[1].scope
    props = [a.proposition for a in wf.store.scopes.assumptions(pos)]
    assert cond in props
    nprops = [a.proposition for a in wf.store.scopes.assumptions(neg)]
    assert T.not_(cond) in nprops


def test_兄弟分支互不可见():
    from cas.kernel.mode import ExecutionMode
    wf = new_workflow(mode=ExecutionMode.DERIVATION)
    g = wf.split_on(parse("x != 0"))
    a, b = g.cases[0].scope, g.cases[1].scope
    wf.enter(a)
    sa = wf.add(parse("x^2"), Claim())
    assert sa.judgment is not None
    wf.enter(b)
    # 在 b 里引用 a 的结论 → 不可见，拒绝
    from cas.workflow.workflow import BothSides
    sb = wf.add(parse("x^2 + 1"), BothSides(pred=sa.id, op="add", operand=N(1)))
    assert sb.status != "open", sb.status


def test_promote_guard提升守卫为蕴含():
    wf = new_workflow()
    g = wf.split_on(parse("x != 0"))
    case = g.cases[0]
    elevated = wf.promote_guard(case, parse("y > 0"))
    assert elevated == T.mk(T.S("Implies"), (case.condition, parse("y > 0")))


def test_needs_split状态与开分支接线():
    """REQUEST_SPLIT 策略下待决条件交回调用方；开分支后条件经假设被清偿。"""
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
    wf.enter(g.cases[0].scope)                 # 进入 x != 0 分支
    s1 = wf.add(parse("x/x"), Claim())
    assert s1.status == "open", (s1.status, s1.note)
    assert wf.applicability_of(s1).is_applicable(), wf.applicability_of(s1)


# ---------------------------------------------------------------------------
# §8.6 Constraint：环在候选↔约束子图
# ---------------------------------------------------------------------------

def test_约束可引用候选且允许成环():
    """§9.6 循环积分：两条构造约束互为对方的定义。任务树无环，候选图成环。"""
    from cas.workflow.constraint import CandidateRef
    wf = new_workflow()
    # 两个候选：T0 与 T1 各自的任务 + 产物
    s0 = wf.add(parse("i"), Claim())
    s1 = wf.add(parse("j"), Claim())
    ref0 = CandidateRef(task=s0.task, artifact=s0.artifact)
    ref1 = CandidateRef(task=s1.task, artifact=s1.artifact)

    u, v = S("_u"), S("_v")                     # 子项抽象把候选冻成符号（§5.4）
    a = parse("exp(x)*sin(x)")
    b = parse("exp(x)*cos(x)")
    c1 = wf.add_constraint(T.eq(u, T.plus(a, T.neg(v))), sources=(ref0, ref1))
    c2 = wf.add_constraint(T.eq(v, T.plus(T.plus(b, N(-1)), u)),
                           sources=(ref1, ref0))

    # 候选图：ref0 → c1, ref0 → c2, ref1 → c1, ref1 → c2 —— 互为依赖
    edges = wf.constraints.dependency_edges()
    assert (ref0, c1.id) in edges and (ref1, c1.id) in edges
    assert (ref0, c2.id) in edges and (ref1, c2.id) in edges
    assert wf.constraints.involving(ref0) == (c1, c2)

    # 任务树仍然无环：树边只能从已存在的父指向后创建的子（id 递增）
    for parent, child in wf.tasks.task_tree_edges():
        assert parent < child, "任务树出现回指"

    # 内核证明图仍无环：每个 Step 的前提都由更早的 Step 产出
    for step in wf.store.all_steps():
        for p in step.premises:
            assert wf.store.get_judgment(p).producer < step.id, "证明图出现回指"


def test_约束不自动成为结论():
    """§8.6：Constraint 可能只是算法构造，不一定是可参与证明的 Judgment。"""
    wf = new_workflow()
    before = wf.store.stats()["judgments"]
    c = wf.add_constraint(parse("_u == 1"))
    assert wf.store.stats()["judgments"] == before, "登记约束不得产生结论"
    assert c.proposed_evidence is None
    # 约束出现在操作历史里（outputs 带 kind 标签）
    kinds = [r.kind for r in wf.events.events()[-1].outputs]
    assert kinds == ["constraint"]


def test_约束赋值经checker复核():
    """§9.6 形态的线性约束系统：求解器交赋值，checker 逐条复核（不重跑求解）。

    用有理式而非超越式作系数——判定管线在代数片段内能闭合，超越片段会诚实
    未决（那是完整性边界，不是缺陷）。
    """
    wf = new_workflow()
    u, v = S("_u"), S("_v")
    X = S("x")
    a = T.pw(X, N(2))                     # a = x^2
    b = X                                 # b = x
    wf.add_constraint(T.eq(u, T.plus(a, T.neg(v))))          # u = a - v
    wf.add_constraint(T.eq(v, T.plus(T.plus(b, N(-1)), u)))  # v = b - 1 + u

    # 解：u = (x^2 - x + 1)/2, v = (x^2 + x - 1)/2
    good = {u: parse("(x^2 - x + 1)/2"), v: parse("(x^2 + x - 1)/2")}
    steps = wf.verify_valuation(good)
    assert len(steps) == 2
    assert all(s.status == "open" for s in steps), [(s.status, s.note) for s in steps]
    assert all(s.judgment is not None for s in steps)

    # 错误赋值：约束不成立 → 否决
    wf2 = new_workflow()
    u2, v2 = S("_u"), S("_v")
    wf2.add_constraint(T.eq(u2, T.plus(a, T.neg(v2))))
    bad = wf2.verify_valuation({u2: N(0), v2: N(0)})
    assert bad[0].status == "dead", (bad[0].status, bad[0].note)
    assert bad[0].judgment is None
