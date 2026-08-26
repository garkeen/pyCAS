# -*- coding: utf-8 -*-
"""结构分析层（统一管线地基，v1：Analysis 一等对象 + 域声明注册表）。

设计文档：docs/domain_env_design.md v3+。原则：
- parse/mk 保持 L0 安全交集不动；本层只做"一次分析、处处使用"
- 每个求解模块在此登记 DOMAIN 声明——隐藏的域约束上缴为数据
"""
from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Sym, S, N


class CoeffBase:
    """系数域枚举（数域轴）。"""
    Q = "Q"                       # 有理数（Fr）
    QI = "QI"                     # 高斯有理数（Ga）
    PARAMS = "PARAMS"             # 超越参数（SymRat 轨道）
    MIXED_QI_PARAMS = "MIXED"     # ℚ(i,params) 混合轨道
    AN = "AN"                     # 代数常数（ALG_MODULI 登记）


class Layer:
    """函数层枚举（函数域轴）。"""
    RING = "RING"
    EXPLOG = "EXPLOG"
    TRIG = "TRIG"
    ALGEBRAIC = "ALGEBRAIC"
    PIECEWISE = "PIECEWISE"


_TRIG_SET = {"Sin", "Cos", "Tan", "Cot", "Sec", "Csc",
             "Sinh", "Cosh", "Tanh"}
_EF_SET = {"Exp", "Log"}
_ALG_HEADS = ("Sin", "Cos", "Tan", "Atan")


class Analysis:
    """单次结构分析结果（一等对象，随调用链传递）。"""

    __slots__ = ("layers", "coeff", "pmap", "gens", "x")

    def __init__(self, layers, coeff, pmap=None, gens=(), x=None):
        self.layers = frozenset(layers)
        self.coeff = coeff
        self.pmap = pmap or {}
        self.gens = gens
        self.x = x

    def __str__(self):
        return (f"layers={sorted(self.layers)} coeff={self.coeff} "
                f"params={len(self.pmap)}")


def _coeff_of(t, x):
    """叶系数域检测。

    TODO: 系数域判定随域投影层重建——v3 裁定域由投影赋予而非叶嗅探，
    本函数是 v2 嗅探路线的遗留。当前仅保留符号参数检测，高斯/代数叶
    检测待新数域层就位后恢复。
    """
    from fractions import Fraction as Fr
    from cas.term import Sym

    seen_pr = False
    stack = [t]
    while stack:
        v = stack.pop()
        if isinstance(v, Sym):
            if v is not x and v.name != "i":
                seen_pr = True          # 参数符号
        elif isinstance(v, (Fr, int)):
            continue
        else:
            stack.extend(getattr(v, "args", ()) or ())
    if seen_pr:
        return CoeffBase.PARAMS
    return CoeffBase.Q


def analyze(t, x):
    """单遍扫描：函数层集合 + 系数域 + 参数化回代表。

    与 risch._parametrize_const_logs 的登记共享（pmap 即其 backsub）；
    后续 PASSES/SOLVERS 以此为唯一分派依据。
    """
    from cas import term as T

    layers = set()
    consts = {}
    stack = [t]
    while stack:
        u = stack.pop()
        head = getattr(u, "head", None)
        if head is None:
            continue
        n = head.name
        if n == "Log":
            if x not in T.free_vars(u.args[0]):
                consts[u] = None          # Log(常量)：参数化候选
                continue
            layers.add(Layer.EXPLOG)
        elif n == "Exp":
            layers.add(Layer.EXPLOG)
        elif n in _TRIG_SET:
            layers.add(Layer.TRIG)
        elif n == "Piecewise":
            layers.add(Layer.PIECEWISE)
        if n == "Power":
            b_, e_ = u.args
            if isinstance(e_, T.Rat) and e_.f.denominator != 1 \
                    and x in T.free_vars(b_):
                layers.add(Layer.ALGEBRAIC)
            elif x in T.free_vars(e_):
                layers.add(Layer.EXPLOG)   # 变指数幂=超越（归一后入塔）
        stack.extend(u.args)
    # TODO: 代数常数经域闸门链注册后的层判定，随数域系统重建
    coeff = _coeff_of(t, x)
    return Analysis(layers, coeff, consts, x=x)


# ---------------------------------------------------------------------------
# Pass 协议 + 预规范化表（P2：收编散落的入口转换，声明式顺序）。
# 每 pass：全树显式重建（带各自预算），绝不进构造器；幂等可重入——
# 塔内同名前置保留为无操作，回代机制（pmap）仍由塔出口负责。
# ---------------------------------------------------------------------------

class Pass:
    """Stage 协议基类（v3 设计 N2 落地）。

    name     唯一标识（管线数据表引用）
    detect(a) 适用性：基于 Analysis 声明式判定（非 if 散落）
    apply(t,a) 全树显式重建 pass（带各自预算；绝不进构造器）
    needs(ctx) 假设需求声明：如 ['principal-branch']；不可满足时
               本阶段跳过并记 degrade 原因（诚实降级——UNVERIFIED
               从模糊变具体）
    """

    name = "?"
    needs = ()                   # 缺省无假设需求

    def detect(self, a):
        return True

    def apply(self, t, a):
        return t

    def gated(self, ctx):
        """needs 对策略位/账本检查；返回 (可运行?, 降级原因)。"""
        from cas.structure import BRANCH_POLICY
        for req in self.needs:
            if req == "principal-branch":
                if not BRANCH_POLICY.get("principal", False):
                    return False, "needs principal-branch commitment"
            else:
                return False, f"unknown assumption {req}"
        return True, ""


def run_stage_pipeline(stages, t, x, on_degrade=None):
    """通用 Stage 序列执行器：单次分析 → 逐 Stage 检测+门控+应用。

    变更即重分析（层集合可能迁移）。on_degrade(name, reason) 供
    管线记录诚实降级（verify 汇聚为 UNVERIFIED 附因）。"""
    a = analyze(t, x)
    for st in stages:
        if not st.detect(a):
            continue
        ok, why = st.gated(None)
        if not ok:
            if on_degrade:
                on_degrade(st.name, why)
            continue
        t2 = st.apply(t, a)
        if t2 is not None and t2 is not t:
            t = t2
            a = analyze(t, x)      # 变更即重分析
    return t, a


# TODO: 入口预规范化 pass 随函数结构层重建——
# 变指数幂归一（NumPowerNorm）、exp-log 收缩/展开（EFContract/EFExpandTrans）
# 原实现依赖已删除的 risch 层，其语义归图书馆操作定义。
# 管线执行器保留，PRE_PASSES 暂为空表。
PRE_PASSES = []


def run_pre_passes(t, x):
    """入口预规范化：单次分析 → 逐 pass 检测+应用（变更即重分析）。

    返回 (t, a)：最终树 + 最终分析结果（供分派消费）。"""
    return run_stage_pipeline(PRE_PASSES, t, x)


# ---------------------------------------------------------------------------
# 判零 Stage 族（N2）：verify 管线的声明式序列。契约：
#   zero(t0, x) -> True(证零) | False(证伪) | None(无结论)
# needs 门控统一走 Stage.gated（principal 承诺位）。
# ---------------------------------------------------------------------------

# TODO: 判零 Stage 族随判定层重建——
# 塔内零等价原走 diff._tower_zero、同底有理指数幂合并原走 diff._ratpow_zero_run、
# 跨项通分原走 ops.together，三者依赖的模块均已删除。
# 执行器与 needs 门控协议保留；VERIFY_STAGES 暂为空表，
# run_verify_stages 当前恒返回 (False, [])——验证降级为 UNVERIFIED。

VERIFY_STAGES = []


def run_verify_stages(d0, x):
    """verify 零判定序列执行器。返回 (verified?, degrades)。"""
    degrades = []
    for st in VERIFY_STAGES:
        ok, why = st.gated(None)
        if not ok:
            degrades.append((st.name, why))
            continue
        z = st.zero(d0, x)
        if z is True:
            return True, degrades
    return False, degrades


# 分支承诺策略位（Reduce 式诚实开关）：仅影响验证管线的合并阶段，
# 不改变 L0 规范化。默认关闭——√x 族保持 UNVERIFIED 诚实状态；
# :declare principal-branch on 后按需升级 VERIFIED。
BRANCH_POLICY = {"principal": False}


def principal_branch():
    return BRANCH_POLICY["principal"]


def set_principal_branch(on):
    BRANCH_POLICY["principal"] = bool(on)


# ---------------------------------------------------------------------------
# 模块域声明注册表：全项目隐藏域约束的上缴点。
# 每个求解模块一行；事实来源 = docs/cas_v3_arch.md 域系统节
# （2026-08 全量实证审计）。新能力合入同步更新。
# ---------------------------------------------------------------------------

DOMAIN_DECLS = {}


def declare(module, base, layers, notes=""):
    DOMAIN_DECLS[module] = {
        "base": base, "layers": layers, "notes": notes}
