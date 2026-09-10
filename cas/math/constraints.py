# -*- coding: utf-8 -*-
"""约束求解：从等式约束提取未知量的线性系统并求解（v4 §8.6 / §9.6）。

**这是不可信侧。** 它产出的是**候选赋值**（witness），不是结论；能不能声称
「这组赋值满足约束系统」由 `constraint.satisfied` checker 逐条复核决定
（§7.3：算法产生候选，checker 决定能声称什么）。所以这里可以启发式、可以拒答，
但绝不能自己宣布正确。

算法步骤（全部是域元素上的显式代数运算，§零.4）：

1. 每条关系取 `E = lhs − rhs`；
2. **线性检验**：把未知量代入 0 / 单位值提取系数，再重建 `E` 并判零差——
   不等即非线性，诚实拒答（FRAGMENT），不硬凑；
3. 组装系数矩阵，交 **通用高斯消元** `linalg.solve_system` 求解；
4. 返回特解作赋值（欠定时仍是一个合法 witness；checker 会判它是否真满足）。

求解只依赖 `linalg`（公共算法机器）+ 域标准形判零，不导入任何求解对方的算法。
"""

from cas.syntax import term as T
from cas.math.domains.linalg import solve_system
from cas.math.qarith import fold
from cas.math.project import project, zero_of, normalize as proj_normalize


def _nf(t):
    """系数归一：投影命中取域标准形（K(x) 上有理函数规范化），落空退回字面折叠。

    只折字面数不够——`x − x`、`x² − x² + 1` 这类要靠域标准形才收敛。
    """
    hit = project(t)
    if hit is not None:
        return proj_normalize(hit)
    return fold(t)


class TermField:
    """把**项**适配成域接口，供 `linalg` 的高斯消元使用。

    系数是参变量上的有理函数（K(x₁..xₙ)），除法按 `b⁻¹` 表示。适配层本身不做
    数学，只是把既有的显式代数运算（域标准形 + 判零）暴露成消元器要的那几个操作。
    """

    is_field = True

    def from_int(self, n):
        return T.N(n)

    def is_zero(self, t):
        return zero_of(t) is True

    def add(self, a, b):
        return _nf(T.plus(a, b))

    def sub(self, a, b):
        return _nf(T.plus(a, T.neg(b)))

    def mul(self, a, b):
        return _nf(T.times(a, b))

    def neg(self, a):
        return _nf(T.neg(a))

    def div_exact(self, a, b):
        return _nf(T.times(a, T.pw(b, T.MONE)))


def _decompose(t, unknowns):
    """把 t 分解为 `Σ cᵢ·uᵢ + c₀`，其中 cᵢ、c₀ 与 unknowns 无关。

    **句法**线性形式分析：不需要化简器、不靠语义判零，因此对超越系数
    （`exp(x)·sin(x)` 之类）同样有效。非线性或含未知量的函数调用（`sin(u)`、
    `u⁻¹`、`u·u`）一律返回 None —— 诚实拒答，不硬凑线性。
    """
    if t in unknowns:                       # 驻留指针恒等
        return ({t: T.ONE}, T.ZERO)
    if not (T.free_vars(t) & set(unknowns)):
        return ({}, t)
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Plus":
            coeffs, const = {}, T.ZERO
            for a in t.args:
                d = _decompose(a, unknowns)
                if d is None:
                    return None
                for k, v in d[0].items():
                    coeffs[k] = T.plus(coeffs.get(k, T.ZERO), v)
                const = T.plus(const, d[1])
            return (coeffs, const)
        if name == "Times":
            parts = []
            for a in t.args:
                d = _decompose(a, unknowns)
                if d is None:
                    return None
                parts.append(d)
            unknown_idx = [i for i, d in enumerate(parts) if d[0]]
            if len(unknown_idx) > 1:
                return None             # 两个含未知量的因子相乘 → 非线性
            if not unknown_idx:
                acc = T.ONE
                for _cs, c0 in parts:
                    acc = T.times(acc, c0)
                return ({}, acc)
            i = unknown_idx[0]
            # 系数必须乘上**其余**因子的常数部分（漏掉它会把 -1·v 的系数算成 +1）
            k_others = T.ONE
            for j, (_cs, c0) in enumerate(parts):
                if j != i:
                    k_others = T.times(k_others, c0)
            cs, c0 = parts[i]
            return ({k: T.times(v, k_others) for k, v in cs.items()},
                    T.times(c0, k_others))
        if name == "Power" and len(t.args) == 2 and t.args[1] is T.ONE:
            return _decompose(t.args[0], unknowns)
    return None


def is_linear(e, unknowns):
    """e 是否对 unknowns 线性（含常数项）。"""
    return _decompose(e, unknowns) is not None


def _constrained_relation(rel, unknowns):
    """等式关系 → 线性形式的系数行与右端项；非线性/非等式返回 None。

    两侧**分别**分解再相减，避免对 `lhs − rhs` 整体做不分配取负而破坏线性形式。
    """
    if not (isinstance(rel, T.Expr) and isinstance(rel.head, T.Sym)
            and rel.head.name == "Eq"):
        return None
    lhs, rhs = rel.args
    dl, dr = _decompose(lhs, unknowns), _decompose(rhs, unknowns)
    if dl is None or dr is None:
        return None
    cl, c0l = dl
    cr, c0r = dr
    # 系数必须归一后再交消元器：分解会产出 `0 + 1` 这类未折叠形式，
    # 直接进高斯消元会让主元判零与除法失效。
    row = [_nf(T.plus(cl.get(u, T.ZERO), T.neg(cr.get(u, T.ZERO))))
           for u in unknowns]
    return row, _nf(T.plus(c0r, T.neg(c0l)))    # Σ cᵢuᵢ = c0r − c0l


def solve_linear_constraints(relations, unknowns):
    """求满足全部关系的赋值。

    返回 `(valuation, complete)`：
      · valuation：`{Unknown: Term}`，未知量以参变量表达；
      · complete：解是否唯一（欠定时为 False，但特解仍是合法 witness）。
    拒答返回 `None`——关系不是等式、非线性、或系统不相容。
    """
    unknowns = tuple(unknowns)
    rows, b = [], []
    for rel in relations:
        got = _constrained_relation(rel, unknowns)
        if got is None:
            return None
        row, rhs = got
        rows.append(row)
        b.append(_nf(rhs))

    ring = TermField()
    sol = solve_system(ring, rows, b)
    if sol is None:
        return None
    particular, homogeneous = sol
    return ({u: particular[i] for i, u in enumerate(unknowns)},
            not homogeneous)
