# -*- coding: utf-8 -*-
"""结构分析层（统一管线地基，v1：Analysis 一等对象 + 域声明注册表）。

设计文档：docs/domain_env_design.md v3+。原则：
- parse/mk 保持 L0 安全交集不动；本层只做"一次分析、处处使用"
- 每个求解模块在此登记 DOMAIN 声明——隐藏的域约束上缴为数据
"""


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

    __slots__ = ("layers", "coeff", "pmap", "gens")

    def __init__(self, layers, coeff, pmap=None, gens=()):
        self.layers = frozenset(layers)
        self.coeff = coeff
        self.pmap = pmap or {}
        self.gens = gens

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
        stack.extend(u.args)
    # 根式代数常数经 _collect_radical 已登记 ALG_MODULI——此处读出
    from cas.risch import ALG_RELATIONS
    if ALG_RELATIONS:
        layers.add(Layer.EXPLOG)          # 参数化后以 exp/log 形态入塔
    coeff = _coeff_of(t, x)
    return Analysis(layers, coeff, consts)


# ---------------------------------------------------------------------------
# 模块域声明注册表：全项目隐藏域约束的上缴点。
# 每个求解模块一行；事实来源 = docs/cas_v2_arch.md §系数域支持矩阵
# （2026-08 全量实证审计）。新能力合入同步更新。
# ---------------------------------------------------------------------------

DOMAIN_DECLS = {}


def declare(module, base, layers, notes=""):
    DOMAIN_DECLS[module] = {
        "base": base, "layers": layers, "notes": notes}
