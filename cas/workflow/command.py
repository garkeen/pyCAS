# -*- coding: utf-8 -*-
"""命令：前端命令的形状（v4 §十一 阶段3 / §三 目标位置 `workflow/command.py`）。

**命令不是内核原语，也不构成功能封闭的 ADT。**

v3 的 `Derivation` 基类 + 八个功能子类（每个带自己的 `checker_id()` 方法，
再配一张「命令类型 → 验证器」的 `isinstance` 分派表）已拆除。命令只剩**一个
纯数据记录**：主张的种类由 `checker_id` **声明**，checker 由内核按 id 从注册表
取用。命令不携带验证逻辑，也不存在按类型的映射表。

对应 v4 §十一 阶段3：「替换为 `StepProposal` / `Evidence(checker_id, payload)` /
`CheckerRegistry`；先保留旧命令名称，但命令只负责生成 proposal」——下面的
命名构造函数保留了旧名字，调用面因此不变；`request` 字段（§8.3 请求头）
取代了原来按类型查的请求头表。
"""

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class Command:
    """一条命令：主张种类 + 载荷。纯数据、无方法（v4 §十一 阶段3）。"""
    name: str                       # 命令名（记入 Event.command）
    checker_id: str                 # 主张种类（CheckerRegistry 的键）
    pred: int | None = None         # 前驱步骤号；None 表示无前驱
    request: str = ""               # 请求头（§8.3）；空则本步不开任务

    # --- 载荷：各命令按需取用，未用者保持 None/空 ---
    op: str = ""
    operand: object = None
    var: object = None
    rule: str = ""
    path: tuple = ()
    substitution: object = None
    solution: object = None
    condition: object = None
    negate: bool = False
    value: object = None
    constraint: object = None
    valuation: object = None
    antideriv: object = None
    bounds: object = None
    registers_assumption: bool = False   # Claim：命题登记为当前作用域假设
    # 分支合并（v4 §8.8）：各支条件、各支开放守卫、各支给出的同一命题
    conditions: tuple = ()
    guards: tuple = ()
    answers: tuple = ()


# ---------------------------------------------------------------------------
# 命名构造函数：保留旧命令名，调用面不变（v4 §十一 阶段3「先保留旧命令名称」）
# ---------------------------------------------------------------------------

def Claim():
    """断言入账——无前驱。命题登记为当前作用域假设（v4 §6.2）。

    假设是上下文条目，不是可信结论；登记动作由工作流执行（checker 只验证）。
    """
    return Command(name="Claim", checker_id="assumption.entry",
                   registers_assumption=True)


def BothSides(pred, op, operand):
    """等式两边同施加运算。

    可逆（add/sub、mul/div by ≠0）⟺ 等价；不可逆（mul by 0）⟹ 蕴含且信息丢失。
    """
    return Command(name="BothSides", checker_id="both_sides.operate",
                   pred=pred, op=op, operand=operand)


def Rewrite(pred, rule="", path=(), substitution=None):
    """重写：前驱的域标准形（`rule=""`），或声明规则在 `(path, substitution)`
    处的一次实例（`rule=` 规则 id）。

    实例数据（path + subst）由**提出方**（REPL 的候选搜索）给出；checker 只
    验证这一个实例，不搜索路径、不重跑规则搜索（v4 §7.3 / 不变量 14）。
    """
    return Command(name="Rewrite",
                   checker_id="rule.instance" if rule else "equality.normalize",
                   pred=pred, request="Simplify", rule=rule, path=path,
                   substitution=substitution)


def Solve(pred, var, solution):
    """输入等式输出解。`solution` 是求解器交出的证书；checker 只做回代判官。"""
    return Command(name="Solve", checker_id="solve.back_substitute",
                   pred=pred, request="Solve", var=var, solution=solution)


def Split(pred, condition, negate=False):
    """条件分支切割——一步析取为两步（`condition` 与 `¬condition`）。"""
    return Command(name="Split", checker_id="branch.split", pred=pred,
                   condition=condition, negate=negate)


def Subst(pred, var, value):
    """代换——前驱中某变量替换为值，纯句法操作。蕴含。"""
    return Command(name="Subst", checker_id="substitute", pred=pred,
                   request="Simplify", var=var, value=value)


def Diff(pred, var):
    """对前驱表达式求导。

    等式不是合法输入：等式两边求导不保真（点解方程 `x=3` 会「推出」`1=0`）。
    """
    return Command(name="Diff", checker_id="calculus.derivative", pred=pred,
                   request="Differentiate", var=var)


def Integrate(pred, var, antideriv, bounds=None):
    """积分——前驱被积式关于 `var` 求原函数，或定积分（`bounds=(a,b)`）。

    `antideriv` 是证书；checker 独立于积分器，用微分层复核。
    """
    return Command(name="Integrate", checker_id="calculus.antiderivative",
                   pred=pred, request="Integrate", var=var,
                   antideriv=antideriv, bounds=bounds)


def ValuationCheck(constraint, valuation):
    """约束系统的一组赋值（v4 §8.6）。

    载荷是求解器交出的**证书**，不是结论；checker 逐条复核实例与判零。
    """
    return Command(name="ValuationCheck", checker_id="constraint.satisfied",
                   constraint=constraint, valuation=valuation)
