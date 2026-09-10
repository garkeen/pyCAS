# -*- coding: utf-8 -*-
"""工作流引擎：提交边界 + 展示记录。

**工作流不是真理内核。** 它不自己验证任何东西：`add` 组装 `StepProposal` 交
`kernel.commit`，由注册的 checker 复核、内核记账。工作流负责的是「用户在解决
什么问题、当前焦点在哪、操作历史」，以及把内核结论映射成前端可读的步骤记录。

三个状态由提交结果决定：

    open        已提交（可能带未清偿条件）
    dead        被否证（Refused）
    unverified  未获复核（Undecided / NeedsSplit）——**不得参与后续可信推导**

「未验证候选不能参与可信推导」（v4 不变量 16）就落在 unverified 这个状态上：
旧实现把所有非 NO 的结果记成 open（fail-open），那是 v3 遗留。

步骤不再有子类，也不再有逐类型的 isinstance 分派：checker 由注册表按 id 取用
（v4 §6.6 / §十一）。下面的 `Derivation` 类型是**命令的形状**（前端命令携带的
参数），不是内核原语——阶段3 将把它压成普通数据结构并去掉功能特化。

守卫不再由工作流提取后挂在步骤上：checker 回报直接条件，内核建 Requirement、
尝试清偿、并负责从前驱继承（v4 §6.7）。这里的 `Step.guards` 只是内核未清偿
条件在前端的投影。

已删除（v4 反向修正）：前驱 dead 沿依赖边级联销毁。原结论保留，适用性由内核
按作用域计算（v4 §6.10）。

域归属：步骤创建时经投影层（cas/project）成员测试记录所属域——域由投影赋予，
不做叶嗅探。
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.syntax.term import Expr, S, Sym
from cas.math.project import project
from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Evidence
from cas.kernel.model import Assumption
from cas.kernel.services import register_core_checkers
from cas.kernel.store import KernelStore
from cas.workflow import checkers as _checkers
from cas.workflow.artifact import ArtifactStore
from cas.workflow.branch import BranchCase, BranchStore, promote_guard
from cas.workflow.constraint import ConstraintStore
from cas.workflow.event import EventLog, Ref
from cas.workflow.task import TaskStore


# ---------------------------------------------------------------------------
# 命令形状：命令只声明主张，不自带验证
#
# 每个命令给出 `checker_id()` —— **主张的种类**，而非「命令的类别」。内核按 id
# 从注册表取 checker，不存在 isinstance 分派表，也没有「命令类型 → 验证器」的
# 功能特化映射。同一条重写命令按是否指定规则给出两种不同主张（标准形 vs 规则
# 实例），这正是「步骤无子类、分派走注册表」的落点。
# ---------------------------------------------------------------------------

class Derivation:
    """命令携带的推导形状。**不是内核原语**，只是前端命令的参数包。"""
    pass


@dataclass(frozen=True, slots=True)
class Claim(Derivation):
    """断言入账——无前驱。命题登记为当前作用域假设（v4 §6.2）。"""
    pass

    def checker_id(self):
        return "assumption.entry"


@dataclass(frozen=True, slots=True)
class BothSides(Derivation):
    """等式两边同施加运算。
    可逆（add/sub、mul/div by ≠0）⟺ 等价；不可逆（mul by 0）⟹ 蕴含且信息丢失。"""
    pred: int
    op: str
    operand: object

    def checker_id(self):
        return "both_sides.operate"


@dataclass(frozen=True, slots=True)
class Rewrite(Derivation):
    """重写：前驱的域标准形（rule=""），或图书馆规则在 (path, substitution)
    处的一次实例（rule=规则 id）。

    实例数据（path + subst）由**提出方**（REPL 的候选搜索）给出；checker 只
    验证这一个实例，不搜索路径、不重跑规则搜索（v4 §7.3 / 不变量 14）。"""
    pred: int
    rule: str = ""
    path: tuple = ()
    substitution: object = None

    def checker_id(self):
        return "rule.instance" if self.rule else "equality.normalize"


@dataclass(frozen=True, slots=True)
class Solve(Derivation):
    """输入等式输出解。solution 是求解器交出的证书；checker 只做回代判官。"""
    pred: int
    var: Sym
    solution: object

    def checker_id(self):
        return "solve.back_substitute"


@dataclass(frozen=True, slots=True)
class Split(Derivation):
    """条件分支切割——一步析取为两步（condition 与 ¬condition）。"""
    pred: int
    condition: object
    negate: bool = False

    def checker_id(self):
        return "branch.split"


@dataclass(frozen=True, slots=True)
class Subst(Derivation):
    """代换——前驱中某变量替换为值，纯句法操作。蕴含。"""
    pred: int
    var: Sym
    value: object

    def checker_id(self):
        return "substitute"


@dataclass(frozen=True, slots=True)
class Diff(Derivation):
    """对前驱表达式求导。

    等式不是合法输入：等式两边求导不保真（点解方程 x=3 会「推出」1=0）。"""
    pred: int
    var: Sym

    def checker_id(self):
        return "calculus.derivative"


@dataclass(frozen=True, slots=True)
class ValuationCheck(Derivation):
    """约束系统的一组赋值（v4 §8.6）。

    载荷是求解器交出的**证书**，不是结论；checker 逐条复核实例与判零。"""
    constraint: object
    valuation: object

    def checker_id(self):
        return "constraint.satisfied"


@dataclass(frozen=True, slots=True)
class Integrate(Derivation):
    """积分——前驱被积式关于 var 求原函数，或定积分（bounds=(a,b)）。

    `antideriv` 是证书（Wit）；checker 独立于积分器，用微分层复核。"""
    pred: int
    var: Sym
    antideriv: object
    bounds: tuple = None

    def checker_id(self):
        return "calculus.antiderivative"


# ---------------------------------------------------------------------------
# 步骤：不可变展示记录（可信结论在内核账本）
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Step:
    id: int
    content: object                 # Term
    derivation: Derivation
    guards: tuple = ()              # 未清偿条件（内核 Requirement 的投影）
    status: str = "unverified"      # "open" | "dead" | "unverified" | "needs_split"
    note: str = ""
    target: tuple = ()
    domain: str = ""                # 内容所属域（投影赋予）
    judgment: object = None         # 内核 JudgmentId；未提交则 None
    artifact: object = None         # 产物 id（ArtifactId）
    task: object = None             # 本次计算问题的 TaskId；无请求形状者 None


# 手工/交互通道：显式应用规则允许产生条件性结论（v4 §6.9 ALLOW_CONDITIONAL）。
# 自动化简走 REQUIRE_PROVED（未决条件不落地），那是 simplify 的事，不经本工作流。
_POLICY = GuardPolicy.ALLOW_CONDITIONAL

# 命令 → 请求头（§8.3：请求是普通项，不是封闭 TaskKind 枚举；这张表属命令层，
# 不是内核枚举）。无请求形状的命令（Claim/BothSides/Split）不开任务。
_REQUEST_HEADS = {Diff: "Differentiate", Integrate: "Integrate",
                  Solve: "Solve", Rewrite: "Simplify", Subst: "Simplify"}


class Workflow:
    """提交边界 + 展示记录。"""

    def __init__(self, store=None, services=None, mode=None, policy=None):
        from cas.kernel.mode import DEFAULT_MODE
        self.store = store if store is not None else KernelStore()
        register_core_checkers(self.store)
        _checkers.register(self.store)
        self.services = services if services is not None \
            else _checkers.WorkflowServices(self.store.scopes)
        self.mode = mode if mode is not None else DEFAULT_MODE
        self.policy = policy if policy is not None else _POLICY
        self._root = self.store.scopes.create()
        self.scope = self._root.id
        # 三图分离（v4 §8.5）：产物图 / 任务图 / 操作历史图，各归其位。
        self.artifacts = ArtifactStore()
        self.tasks = TaskStore(kernel=self.store)
        self.events = EventLog()
        self.branches = BranchStore()
        self.constraints = ConstraintStore()
        self._steps: dict = {}
        self._next_id = 0

    def get(self, sid) -> Step:
        return self._steps[sid]

    def all_steps(self):
        return [self._steps[i] for i in range(self._next_id)]

    def add(self, content, derivation, note="", target=()) -> Step:
        pred_id = getattr(derivation, "pred", None)
        premises = ()
        if pred_id is not None:
            pstep = self._steps.get(pred_id)
            if pstep is None or pstep.judgment is None:
                return self._record(content, derivation, "unverified",
                                    note or "前驱无可依赖结论", target, ())
            premises = (pstep.judgment,)

        # Claim：命题先登记为作用域假设（假设是上下文条目，不是可信结论）
        if isinstance(derivation, Claim):
            self.store.scopes.extend(self.store.scopes.get(self.scope),
                                     assumptions=(Assumption(content),))

        cid = derivation.checker_id()
        proposal = StepProposal(scope=self.scope, premises=premises,
                                conclusions=(content,),
                                evidence=Evidence(cid, derivation),
                                guard_policy=self.policy)
        res = commit(self.store, proposal, services=self.services,
                     mode=self.mode)

        if res.is_committed():
            j = self.store.get_judgment(res.judgments[0])
            guards = tuple(self.store.get_requirement(r).proposition
                           for r in j.requirements)
            return self._record(content, derivation, "open", note, target,
                                guards, j.id)
        if res.is_refused():
            return self._record(content, derivation, "dead",
                                res.detail or note, target, ())
        if res.is_needs_split():
            # 策略要求分类讨论：把待决条件交回调用方，由 split_on 开分支。
            return self._record(content, derivation, "needs_split",
                                "需分类讨论", target, tuple(res.conditions))
        return self._record(content, derivation, "unverified",
                            getattr(res, "detail", "") or "未获复核",
                            target, ())

    def _record(self, content, derivation, status, note, target, guards,
                judgment=None) -> Step:
        # 1. 计算产物（无真假，§8.2）
        artifact = self.artifacts.create(self.scope, content)
        # 2. 计算问题 + 候选（§8.3/§8.4；命令无请求形状者不建任务）
        task = self._open_task(derivation, artifact, judgment)
        # 3. 操作历史（§8.9）：outputs 是连接操作与内核结论的唯一出口（§四）
        pred_id = getattr(derivation, "pred", None)
        ev = self.events.append(
            command=type(derivation).__name__,
            inputs=() if pred_id is None else (pred_id,),
            outputs=tuple(
                Ref(kind, ident)
                for kind, ident in (("artifact", artifact.id),
                                    ("task", task and task.id),
                                    ("judgment", judgment))
                if ident is not None))
        self.artifacts.attach(artifact.id, ev.id)

        s = Step(id=self._next_id, content=content, derivation=derivation,
                 guards=tuple(guards), status=status, note=note,
                 target=tuple(target), domain=self._domain_of(content),
                 judgment=judgment, artifact=artifact.id,
                 task=None if task is None else task.id)
        self._steps[self._next_id] = s
        self._next_id += 1
        return s

    def _open_task(self, derivation, artifact, judgment):
        """按命令的请求形状开一个任务并登记候选。无请求形状的命令返回 None。"""
        head = _REQUEST_HEADS.get(type(derivation))
        if head is None:
            return None
        pred_id = getattr(derivation, "pred", None)
        pstep = self._steps.get(pred_id) if pred_id is not None else None
        pred = pstep.content if pstep is not None else artifact.value
        var = getattr(derivation, "var", None)
        args = (pred, var) if var is not None else (pred,)
        task = self.tasks.open_task(self.scope, T.mk(S(head), args))
        self.tasks.propose(task.id, artifact.id, judgment)
        return task

    # --- 约束（v4 §8.6：计算构造出的方程，环在候选↔约束子图）---

    def add_constraint(self, relation, sources=(), proposed_evidence=None):
        """登记一条计算构造关系。**不产生 Judgment**——约束是 Artifact 级构造，
        要成为结论仍须经 commit 并由 checker 接受（§8.6）。"""
        c = self.constraints.add(self.scope, relation, sources,
                                 proposed_evidence)
        self.events.append(command="AddConstraint", inputs=(),
                           outputs=(Ref("constraint", c.id),))
        return c

    def verify_valuation(self, valuation):
        """逐条复核「这组赋值满足约束系统」。

        `valuation` 是**求解器交出的证书**（不可信侧，可以给错）。每条约束各
        提交一次，由 `constraint.satisfied` checker 复核实例与判零——求解器自报
        不算，这正是 §7.3「算法产生候选、checker 决定能声称什么」。
        """
        out = []
        for c in self.constraints.all():
            inst = T.subst(c.relation, dict(valuation))
            out.append(self.add(inst, ValuationCheck(constraint=c,
                                                     valuation=valuation)))
        return tuple(out)

    # --- 分支（v4 §8.8）---

    def split_on(self, condition):
        """按 `condition` 与 `¬condition` 建一对分支作用域，并尝试证覆盖。

        **兄弟分支互不可见**（不变量 9），且分支上下文不能直接合并——合并前必须
        验证 §8.8 的五条；此处只落「覆盖」这一条（排中律，句法重言式），其余
        四条由调用方在各自分支内提交结论时自然满足（作用域可见性 + 逃逸检查）。
        """
        parent = self.store.scopes.get(self.scope)
        cases = []
        for cond, label in ((condition, "+"), (T.not_(condition), "-")):
            child = self.store.scopes.child(parent,
                                            assumptions=(Assumption(cond),))
            cases.append(BranchCase(condition=cond, scope=child.id, label=label))
        group = self.branches.create(self.scope, cases)

        # 覆盖：条件之析取（排中律下 AC 折叠为 ⊤），经 checker 复核后登记
        prop = T.or_(*[c.condition for c in cases])
        r = commit(self.store,
                   StepProposal(scope=self.scope, conclusions=(prop,),
                                evidence=Evidence("branch.coverage", group.id),
                                guard_policy=GuardPolicy.REQUIRE_PROVED),
                   services=self.services, mode=self.mode)
        self.branches.set_coverage(group.id, r.judgments[0] if r.is_committed()
                                   else None)
        self.events.append(command="Split", inputs=(),
                           outputs=(Ref("branch", group.id),))
        return self.branches.get(group.id)

    def enter(self, scope):
        """进入分支作用域：其后提交发生在这里。"""
        self.store.scopes.get(scope)
        self.scope = scope
        return scope

    def promote_guard(self, case, guard):
        """把分支内未清偿的守卫提升到父层：`C_i ⇒ G_i`（§8.8 第 5 条）。"""
        return promote_guard(case.condition, guard)

    # --- 适用性查询（v4 §6.10：内核算，工作流问）---

    def applicability_of(self, step):
        """该步结论在**当前作用域**的适用性；无结论则 None。"""
        if step.judgment is None:
            return None
        return self.store.applicability(step.judgment, self.scope)

    # --- 撤销/重做：只移 revision 指针（§8.9）---

    def undo(self):
        return self.events.undo()

    def redo(self):
        return self.events.redo()

    def _domain_of(self, content) -> str:
        t = content
        if _is_eq(content):
            la, ra = content.args
            t = T.plus(la, T.neg(ra))
        hit = project(t)
        return hit.name if hit is not None else ""


def _is_eq(t) -> bool:
    return isinstance(t, Expr) and t.head.name == "Eq"
