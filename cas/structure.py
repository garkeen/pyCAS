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
    """叶系数域检测：Ga/SymRat 混合判定复用 risch 判据的轻量版。

    裸符号（非积分变量、非保留名 i）= 超越参数（L0 语义）。"""
    from fractions import Fraction as Fr
    from cas.gaussian import Ga
    from cas.poly import SymRat
    from cas.term import Sym

    seen_qi = seen_pr = False
    stack = [t]
    while stack:
        v = stack.pop()
        if isinstance(v, SymRat):
            seen_pr = True
            for pp in (v.num, v.den):
                stack.extend(pp.monos.values())
        elif isinstance(v, Ga):
            if isinstance(v.re, SymRat) or isinstance(v.im, SymRat):
                return CoeffBase.MIXED_QI_PARAMS
            seen_qi = True
        elif isinstance(v, Sym):
            if v is not x and v.name != "i":
                seen_pr = True          # 参数符号
        elif isinstance(v, (Fr, int)):
            continue
        else:
            stack.extend(getattr(v, "args", ()) or ())
    if seen_qi and seen_pr:
        return CoeffBase.MIXED_QI_PARAMS
    if seen_qi:
        return CoeffBase.QI
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
    # 根式代数常数经 _collect_radical 已登记 ALG_MODULI——此处读出
    from cas.risch import ALG_RELATIONS
    if ALG_RELATIONS:
        layers.add(Layer.EXPLOG)          # 参数化后以 exp/log 形态入塔
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


class NumPowerNorm(Pass):
    """变指数/分数幂归一：b^e -> Exp(e·Log(b))。"""
    name = "num_power_norm"

    def apply(self, t, a):
        from cas.risch import _norm_const_base_powers
        return _norm_const_base_powers(t, a.x)


class EFContract(Pass):
    """exp(k·Log u) -> u^k（k∈ℚ；FriCAS iiilog 同款）。"""
    name = "ef_contract"

    def apply(self, t, a):
        from cas.risch import _ef_contract
        from cas.simplify import simplify as _s, expand as _e
        t2 = _ef_contract(t)
        if t2 is not t:
            return _s(_e(t2))
        return t


class EFExpandTrans(Pass):
    """超越头参数环层展开后再收缩一轮。"""
    name = "ef_expand_trans"

    def apply(self, t, a):
        from cas.risch import _ef_expand_trans, _ef_contract
        from cas.simplify import simplify as _s, expand as _e
        t3 = _ef_expand_trans(t)
        if t3 is not t:
            t3 = _ef_contract(t3)
            return _s(_e(t3))
        return t


PRE_PASSES = [NumPowerNorm(), EFContract(), EFExpandTrans()]


def run_pre_passes(t, x):
    """入口预规范化：单次分析 → 逐 pass 检测+应用（变更即重分析）。

    返回 (t, a)：最终树 + 最终分析结果（供 SOLVERS 分派消费）。"""
    return run_stage_pipeline(PRE_PASSES, t, x)


# ---------------------------------------------------------------------------
# 判零 Stage 族（N2）：verify 管线的声明式序列。契约：
#   zero(t0, x) -> True(证零) | False(证伪) | None(无结论)
# needs 门控统一走 Stage.gated（principal 承诺位）。
# ---------------------------------------------------------------------------

class TowerZeroStage(Pass):
    """exp/log 塔内零等价（Risch 结构定理，精确）。"""
    name = "tower_zero"

    def zero(self, t0, x):
        from cas.diff import _tower_zero
        return True if _tower_zero(t0, T.ZERO, x) else None


class RatpowMergeStage(Pass):
    """同底有理指数幂合并后判零——仅 principal 承诺开启（分支切割
    安全：x^{3/2}·x^{-1}=x^{1/2} 在负 x 半轴不成立）。"""
    name = "ratpow_merge"
    needs = ("principal-branch",)

    def zero(self, t0, x):
        m = _merge_ratpow(t0)
        if m is t0:
            return None
        from cas.decide import equivalent, T3
        from cas.diff import _tower_zero
        if m is T.ZERO or (T.is_num(m) and T.num_val(m) == 0):
            return True
        if equivalent(m, T.ZERO) is T3.YES:
            return True
        if _tower_zero(m, T.ZERO, x):
            return True
        return None


class AtomizeTogetherStage(Pass):
    """符号幂原子化 + together 跨项通分判零（M5.6 x^(a+1)/((a+1)c)
    族；simplify 不做跨项通分，只有 together 能折叠系数分式）。"""
    name = "atomize_together"
    needs = ("principal-branch",)

    def zero(self, t0, x):
        from cas.decide import equivalent, T3
        m2 = _atomize_sym_powers(t0)
        if m2 is t0:
            return None
        from cas.ops import together as _tg
        from cas.errors import PolyError
        try:
            m2 = _tg(m2)
        except PolyError:
            pass
        if m2 is T.ZERO or (T.is_num(m2) and T.num_val(m2) == 0):
            return True
        if equivalent(m2, T.ZERO) is T3.YES:
            return True
        return None


VERIFY_STAGES = [TowerZeroStage(), RatpowMergeStage(),
                 AtomizeTogetherStage()]


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
# 不改变 L0 规范化。默认关闭——√x 族保持 PROBABLE 级诚实状态；
# :declare principal-branch on 后按需升级 VERIFIED。
BRANCH_POLICY = {"principal": False}


def _atomize_sym_powers(d0):
    """符号幂原子化（M5.6：principal 承诺域的验证归一化）。

    两步：
    1. 指数整数移位拆分：Power(b, e₀+n)（e₀ 含符号核、n 整数字面量）
       -> Power(b, e₀)·bⁿ——x^(a+1) 与 x^a·x 的跨项对齐；
    2. 非数值指数幂 -> 独立超越原子（同形同原子，驻留指针保证）。
    差值环约简在 {参数 ∪ 原子} 多项式上判定：形式恒等 ⇒ 特化保真
    （原子间无关系假设，只可能保守拒绝）。"""
    head = getattr(d0, "head", None)
    if head is None:
        return d0

    def _split_int(e_):
        """e_ = 核 + 整数字面量 -> (核, n)；无整字面量返回 (e_, 0)。"""
        if isinstance(e_, T.Expr) and e_.head.name == "Plus":
            core = []
            n = 0
            for a_ in e_.args:
                if isinstance(a_, T.Int):
                    n += a_.v
                else:
                    core.append(a_)
            if n != 0:
                if len(core) == 1:
                    return core[0], n
                if core:
                    return T.mk(S("Plus"), tuple(core)), n
                return N(0), n
        return e_, 0

    def _rec(u, subs):
        head_ = getattr(u, "head", None)
        if head_ is None:
            return u
        if head_.name == "Power":
            b_, e_ = u.args
            # 数值指数幂不原子化（Poly 原生支持；负整幂参与跨项相消）
            if isinstance(e_, (T.Int, T.Rat)):
                return T.pw(_rec(b_, subs), e_)
            nb_ = _rec(b_, subs)
            ne_ = _rec(e_, subs)
            core, n = _split_int(ne_)
            key = (nb_._h, getattr(core, "_h", core))
            atom = subs.get(key)
            if atom is None:
                _ATOM_COUNTER[0] += 1
                atom = S(f"_pwa{_ATOM_COUNTER[0]}")
                subs[key] = atom
            # 核心幂由原子承载；仅整数移位保留真实幂
            if n > 0:
                return T.times(atom, T.pw(nb_, N(n)))
            if n < 0:
                return T.times(atom, T.div(N(1), T.pw(nb_, N(-n))))
            return atom
        return T.mk(head_, tuple(_rec(a_, subs) for a_ in u.args))

    subs = {}
    out = _rec(d0, subs)
    return out


_ATOM_COUNTER = [0]


def principal_branch():
    return BRANCH_POLICY["principal"]


def set_principal_branch(on):
    BRANCH_POLICY["principal"] = bool(on)


def _merge_ratpow(t):
    """同底幂合并（验证专用域阶段；L0 裁定不动）。

    仅在 principal 承诺开启时由 verify 管线调用——语义依据：
    本系统 diff 幂规则已承诺单值主支 Log，合并与微分语义一致。
    M5.6 扩展：指数从 Int/Rat 放宽到任意项——x^(a+1)·x^(-1) 类
    微分产物需要符号指数合并才能精确判零（L0 对非整指数永不合并
    的保守裁定在验证域由本阶段解除）。"""
    head = getattr(t, "head", None)
    if head is None:
        return t
    from fractions import Fraction as Fr

    def _as_exp(e_):
        if isinstance(e_, T.Rat):
            return e_.f
        if isinstance(e_, T.Int):
            return Fr(e_.v)
        return None

    def _merge_in(u):
        head_ = getattr(u, "head", None)
        if head_ is None:
            return u
        if head_.name != "Times":
            return T.mk(head_, tuple(_merge_in(a_) for a_ in u.args))
        coeff = Fr(1)
        groups = {}
        rest = []
        for fac in u.args:
            if T.is_num(fac):
                coeff *= T.num_val(fac)
                continue
            if isinstance(fac, Expr) and fac.head.name == "Power":
                b_, e_ = fac.args
                ef = _as_exp(e_)
                # 数值系数从底数剥出（仅 Int/Rat 指数安全）：Power(c·u,q)=c^q·u^q，
                # 使 x^{3/2} 与 (2x)^{-1} 的底归一为同一 x
                while isinstance(b_, Expr) and b_.head.name == "Times" \
                        and ef is not None:
                    nums = [f__ for f__ in b_.args if T.is_num(f__)]
                    others = [f__ for f__ in b_.args if not T.is_num(f__)]
                    if len(nums) != 1 or not others:
                        break
                    cv = T.num_val(nums[0])
                    if cv < 0 and ef.denominator != 1:
                        break          # 负底分数幂：主支外不剥（保守）
                    cnum = others[0] if len(others) == 1 \
                        else T.mk(S("Times"), tuple(others))
                    rest.append(T.pw(N(cv), N(ef)))
                    b_, e_ = cnum, e_
                key = b_._h
                g = groups.get(key)
                if g is None:
                    groups[key] = [b_, e_]
                else:
                    g[1] = T.plus(g[1], e_)
                continue
            rest.append(_merge_in(fac))
        if not groups and coeff == 1:
            return u
        out = list(rest)
        for b_, e_ in groups.values():
            if T.is_num(e_) and T.num_val(e_) == 0:
                continue
            out.append(T.pw(b_, e_))
        if not out:
            return N(coeff)
        u2 = T.mk(S("Times"), tuple(out)) if len(out) > 1 else out[0]
        if coeff != 1:
            u2 = T.times(u2, N(coeff))
        return u2

    args = tuple(_merge_in(a) for a in t.args)
    u = T.mk(head, args)
    uh = getattr(u, "head", None)
    if uh is None or uh.name != "Times":
        return u
    return _merge_in(u)


# ---------------------------------------------------------------------------
# 模块域声明注册表：全项目隐藏域约束的上缴点。
# 每个求解模块一行；事实来源 = docs/cas_v2_arch.md §系数域支持矩阵
# （2026-08 全量实证审计）。新能力合入同步更新。
# ---------------------------------------------------------------------------

DOMAIN_DECLS = {}


def declare(module, base, layers, notes=""):
    DOMAIN_DECLS[module] = {
        "base": base, "layers": layers, "notes": notes}
