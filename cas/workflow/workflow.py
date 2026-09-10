# -*- coding: utf-8 -*-
"""工作流引擎：提交边界 + 展示记录。

**工作流不是真理内核。** 它不自己验证任何东西：`add` 组装 `StepProposal` 交
`kernel.commit`，由注册的 checker 复核、内核记账。工作流负责的是「用户在解决
什么问题、当前焦点在哪、操作历史」，以及把内核结论映射成前端可读的步骤记录。

四个状态**取自内核提交结论 ADT 的名字**（v4 §6.9），不新造词汇：

    committed    已提交（可能带未清偿条件）
    refused      被否证（Refused）
    undecided    未获复核（Undecided）——**不得参与后续可信推导**
    needs_split  策略要求分类讨论（NeedsSplit）

「未验证候选不能参与可信推导」（v4 不变量 16）就落在 undecided 这个状态上：
旧实现把所有非 NO 的结果记成 open（fail-open），那是 v3 遗留。

步骤不再有子类，也不再有逐类型的 isinstance 分派：checker 由注册表按 id 取用
（v4 §6.6 / §十一）。命令是 `cas/workflow/command.py` 里的**纯数据记录**
（`Command`），主张种类由 `checker_id` 声明——封闭的 `Derivation` ADT 与
「命令类别 → 验证器」的映射表已拆除。

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
from cas.syntax.term import Expr, S
from cas.kernel.commit import GuardPolicy, StepProposal, commit
from cas.kernel.evidence import Evidence
from cas.kernel.model import Assumption
from cas.workflow.artifact import ArtifactStore
from cas.workflow.branch import BranchCase, BranchStore, promote_guard
from cas.workflow.command import Command, ValuationCheck
from cas.workflow.constraint import ConstraintStore
from cas.workflow.event import EventLog, Ref
from cas.workflow.task import TaskStore


# ---------------------------------------------------------------------------
# 命令形状见 cas/workflow/command.py：命令是**纯数据记录**（主张种类由
# `checker_id` 声明），不含功能子类，也没有按类型的分派表（v4 §十一 阶段3）。
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# 步骤：不可变展示记录（可信结论在内核账本）
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Step:
    id: int
    content: object                 # Term
    command: Command                # 命令（纯数据记录；主张种类在其 checker_id）
    guards: tuple = ()              # 未清偿条件（内核 Requirement 的投影）
    status: str = "undecided"       # "committed"|"refused"|"undecided"|"needs_split"
    note: str = ""
    target: tuple = ()
    domain: str = ""                # 内容所属域（投影赋予）
    judgment: object = None         # 内核 JudgmentId；未提交则 None
    artifact: object = None         # 产物 id（ArtifactId）
    task: object = None             # 本次计算问题的 TaskId；无请求形状者 None


# 手工/交互通道：显式应用规则允许产生条件性结论（v4 §6.9 ALLOW_CONDITIONAL）。
# 自动化简走 REQUIRE_PROVED（未决条件不落地），那是 simplify 的事，不经本工作流。
_POLICY = GuardPolicy.ALLOW_CONDITIONAL


class Workflow:
    """提交边界 + 展示记录。"""

    def __init__(self, store, services, algorithms=None, mode=None, policy=None):
        """账本与判定服务**由 runtime 装配后注入**（v4 §四）。

        workflow 不认识 `cas.math`，所以数学 checker、判定服务、以及它偶尔要用的
        数学算法（域投影 / 约束求解）都由 `cas.runtime.new_workflow()` 注入。这也让
        「workflow 不知道自己有哪些 checker、算法怎么实现」成为结构事实，而不是
        靠约定维持。
        """
        from cas.kernel.mode import DEFAULT_MODE
        if store is None or services is None:
            raise RuntimeError(
                "Workflow 需要账本与判定服务：用 cas.runtime.new_workflow() 构造"
                "（装配归 runtime；v4 §四 禁止 workflow 依赖 cas.math）")
        self.store = store
        self.services = services
        self.algorithms = algorithms
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

    def add(self, content, command, note="", target=()) -> Step:
        pred_id = command.pred
        premises = ()
        if pred_id is not None:
            pstep = self._steps.get(pred_id)
            if pstep is None or pstep.judgment is None:
                return self._record(content, command, "undecided",
                                    note or "前驱无可依赖结论", target, ())
            premises = (pstep.judgment,)

        # Claim：命题先登记为作用域假设（假设是上下文条目，不是可信结论）。
        # 登记是工作流的动作——命令用 `registers_assumption` 声明，checker 只验证。
        if command.registers_assumption:
            self.store.scopes.extend(self.store.scopes.get(self.scope),
                                     assumptions=(Assumption(content),))

        proposal = StepProposal(scope=self.scope, premises=premises,
                                conclusions=(content,),
                                evidence=Evidence(command.checker_id, command),
                                guard_policy=self.policy)
        res = commit(self.store, proposal, services=self.services,
                     mode=self.mode)

        if res.is_committed():
            j = self.store.get_judgment(res.judgments[0])
            guards = tuple(self.store.get_requirement(r).proposition
                           for r in j.requirements)
            return self._record(content, command, "committed", note, target,
                                guards, j.id)
        if res.is_refused():
            return self._record(content, command, "refused",
                                res.detail or note, target, ())
        if res.is_needs_split():
            # 策略要求分类讨论：把待决条件交回调用方，由 split_on 开分支。
            return self._record(content, command, "needs_split",
                                "需分类讨论", target, tuple(res.conditions))
        return self._record(content, command, "undecided",
                            getattr(res, "detail", "") or "未获复核",
                            target, ())

    def _record(self, content, command, status, note, target, guards,
                judgment=None) -> Step:
        # 1. 计算产物（无真假，§8.2）
        artifact = self.artifacts.create(self.scope, content)
        # 2. 计算问题 + 候选（§8.3/§8.4；命令无请求头者不建任务）
        task = self._open_task(command, artifact, judgment)
        # 3. 操作历史（§8.9）：outputs 是连接操作与内核结论的唯一出口（§四）
        pred_id = command.pred
        ev = self.events.append(
            command=command.name,
            inputs=() if pred_id is None else (pred_id,),
            outputs=tuple(
                Ref(kind, ident)
                for kind, ident in (("artifact", artifact.id),
                                    ("task", task and task.id),
                                    ("judgment", judgment))
                if ident is not None))
        self.artifacts.attach(artifact.id, ev.id)

        s = Step(id=self._next_id, content=content, command=command,
                 guards=tuple(guards), status=status, note=note,
                 target=tuple(target), domain=self._domain_of(content),
                 judgment=judgment, artifact=artifact.id,
                 task=None if task is None else task.id)
        self._steps[self._next_id] = s
        self._next_id += 1
        return s

    def _open_task(self, command, artifact, judgment):
        """按命令声明的请求头开一个任务并登记候选。无请求头者返回 None。

        请求是**普通项**（§8.3），不是封闭 TaskKind 枚举——头部字符串由命令
        自带（`Command.request`），工作流不认识这些 head 的数学含义。
        """
        head = command.request
        if not head:
            return None
        pred_id = command.pred
        pstep = self._steps.get(pred_id) if pred_id is not None else None
        pred = pstep.content if pstep is not None else artifact.value
        var = command.var
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

    def solve_constraints(self, unknowns):
        """求解约束系统并复核。求解器**不可信**（可以给错候选），复核归 checker。

        返回 `(valuation, steps, complete)`；求解器拒答返回 `(None, (), False)`。
        """
        if self.algorithms is None:
            raise RuntimeError(
                "未注入算法门面：用 cas.runtime.new_workflow() 构造"
                "（v4 §四 禁止 workflow 依赖 cas.math）")
        rels = tuple(c.relation for c in self.constraints.all())
        res = self.algorithms.solve_linear_constraints(rels, unknowns)
        if res is None:
            return None, (), False
        valuation, complete = res
        return valuation, self.verify_valuation(valuation), complete

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

        # 覆盖：条件之析取，交 checker 独立复核（互补对 ⇒ 句法重言式；
        # 判定在验证侧，不靠构造期坍缩，v4 §2.1）
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
        """步骤所属域（投影赋予，不做叶嗅探）——算法由注入的门面提供。"""
        if self.algorithms is None:
            return ""
        return self.algorithms.domain_of(content)


def _is_eq(t) -> bool:
    return isinstance(t, Expr) and t.head.name == "Eq"
