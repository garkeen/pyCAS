# -*- coding: utf-8 -*-
"""一维柱面代数分解（最简 CAD，架构 §6.4/§8"结式引擎即可起步"）。

把一组关于单变量 x 的**多项式**条件分解成有序、互斥、覆盖全轴的胞腔
（开区间 + 点），并逐胞腔判定每个条件的真值。这是分段函数求导/积分/
解方程的公共地基：一切"分界点在哪、谁在前谁在后"的问题都归结于此。

判定通道（全精确，无近似）：
· 开区间胞腔：取无根有理样本点，边界多项式精确求值定符号。
· 点胞腔（根）：该条件边界多项式若在此根处消没（Sturm 计数 ≥1）则值为 0；
  否则符号在根的小邻域内恒定，取隔离区间中点求值——不依赖 ℚ(α) 扩张。

诚实边界：条件非单变量多项式即拒答——多变量分区（投影未建）记
FRAGMENT；含超越结构（超越根比大小，拒答表 §7 第三行）记 UNDECIDABLE。
"""

from dataclasses import dataclass
from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.errors import CadError
from cas.kernel.verdict import Reason
from cas.math.qarith import fold
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import from_term, p_mul
from cas.math.domains.polytools import p_deg
from cas.math.realroot import (real_roots_intervals, p_eval_at, coef_sign,
                          squarefree_part, sturm_sequence, count_roots_open)

_CMP = ("Lt", "Le", "Gt", "Ge", "Eq", "Ne")


@dataclass(frozen=True, slots=True)
class Cell:
    """一个胞腔。

    kind=="open"：开区间，sample 为腔内无根有理样本点。
    kind=="point"：单根胞腔，iso=(a, b) 为该根的隔离区间
                   （a==b 为精确有理根）。
    lo / hi：本胞腔下/上界根的隔离区间；None 表示无界（−∞ / +∞）。
             点胞腔 lo==hi==iso；开胞腔为其两侧根的隔离区间。"""
    kind: str
    sample: object = None     # Fr（open）
    iso: tuple = None         # (a, b)（point）
    lo: object = None         # 下界根隔离区间或 None（−∞）
    hi: object = None         # 上界根隔离区间或 None（+∞）


# ---------------------------------------------------------------------------
# 条件 → 边界多项式
# ---------------------------------------------------------------------------

def _refusal_reason(d, x):
    fv = T.free_vars(d)
    if any(s is not x for s in fv):
        return Reason.FRAGMENT          # 多变量分区：CAD 投影未建
    return Reason.UNDECIDABLE           # 单变量含超越结构：根比较不可判定


def _boundary(cond, x):
    """比较命题两侧之差 → 单变量多项式；非多项式分区拒答。

    差值先经 ℚ 折叠——解析产物中未收拢的负指数幂（如 -1/2 的
    (2^-1)·(-1)）折叠后即是常数，折叠后仍非多项式才是真拒答。"""
    a, b = cond.args
    d = fold(T.plus(a, T.neg(b)))
    p = from_term(Q_RING, d, (x,))
    if p is None:
        raise CadError(f"条件非单变量多项式分区: {cond!r}",
                       _refusal_reason(d, x))
    return p


def extract_boundary_polys(cond, x):
    """递归收集条件中的边界多项式（比较两侧之差，去常数）。"""
    if cond is T.TRUE or cond is T.FALSE:
        return []
    if isinstance(cond, T.BVal):
        return []
    if isinstance(cond, T.Expr):
        h = cond.head.name
        if h in ("And", "Or"):
            out = []
            for a in cond.args:
                out.extend(extract_boundary_polys(a, x))
            return out
        if h == "Not":
            return extract_boundary_polys(cond.args[0], x)
        if h in _CMP:
            p = _boundary(cond, x)
            return [p] if p_deg(p, 0) > 0 else []
    raise CadError(f"非命题条件: {cond!r}", Reason.FRAGMENT)


# ---------------------------------------------------------------------------
# 胞腔构造
# ---------------------------------------------------------------------------

def cells(polys):
    """由边界多项式集合产出有序胞腔。无实根 → 单开区间 (−∞, ∞)。"""
    if not polys:
        return [Cell("open", sample=Fr(0))]
    P = polys[0]
    for q in polys[1:]:
        P = p_mul(Q_RING, P, q)
    ivs = real_roots_intervals(Q_RING, P)
    if not ivs:
        return [Cell("open", sample=Fr(0))]
    out = []
    a1, _b1 = ivs[0]
    out.append(Cell("open", sample=a1 - 1, hi=ivs[0]))       # (−∞, r₁)
    for i, (a, b) in enumerate(ivs):
        out.append(Cell("point", iso=(a, b), lo=(a, b), hi=(a, b)))
        if i + 1 < len(ivs):
            na, nb = ivs[i + 1]
            out.append(Cell("open", sample=(b + na) / 2,    # (rᵢ, rᵢ₊₁)
                            lo=(a, b), hi=(na, nb)))
    _ak, bk = ivs[-1]
    out.append(Cell("open", sample=bk + 1, lo=ivs[-1]))      # (rₖ, +∞)
    return out


# ---------------------------------------------------------------------------
# 胞腔上的符号判定
# ---------------------------------------------------------------------------

def sign_at_cell(p, cell: Cell) -> int:
    """边界多项式 p 在胞腔上的符号（−1/0/1）。"""
    if p.is_zero():
        return 0
    if cell.kind == "open":
        return coef_sign(p_eval_at(p, cell.sample))
    a, b = cell.iso
    if a == b:                                # 精确有理根
        return coef_sign(p_eval_at(p, a))
    # 无理根：p 在此根消没 ⟺ p 在隔离区间内有根（Sturm 计数）
    sf = squarefree_part(Q_RING, p)
    seq = sturm_sequence(Q_RING, sf)
    if count_roots_open(seq, sf, a, b) >= 1:
        return 0
    return coef_sign(p_eval_at(p, (a + b) / 2))


def _apply_cmp(op: str, sgn: int) -> bool:
    if op == "Lt":
        return sgn < 0
    if op == "Le":
        return sgn <= 0
    if op == "Gt":
        return sgn > 0
    if op == "Ge":
        return sgn >= 0
    if op == "Eq":
        return sgn == 0
    return sgn != 0                           # Ne


def cond_holds(cond, cell: Cell, x) -> bool:
    """条件在胞腔上的真值（胞腔内条件恒真/恒假，符号不变）。"""
    if cond is T.TRUE:
        return True
    if cond is T.FALSE:
        return False
    h = cond.head.name
    if h == "And":
        return all(cond_holds(a, cell, x) for a in cond.args)
    if h == "Or":
        return any(cond_holds(a, cell, x) for a in cond.args)
    if h == "Not":
        return not cond_holds(cond.args[0], cell, x)
    if h in _CMP:
        p = _boundary(cond, x)
        return _apply_cmp(h, sign_at_cell(p, cell))
    raise CadError(f"非命题条件: {cond!r}", Reason.FRAGMENT)


# ---------------------------------------------------------------------------
# 分区解析（公共入口）
# ---------------------------------------------------------------------------

def resolve_partition(conds, x):
    """conds 关于 x 的柱面分解。

    返回 [(Cell, [bool, ...])]，内层布尔列表与 conds 对齐——胞腔上各条件
    的真值。空条件列表返回单一全轴开区间。任一条件非单变量多项式分区
    抛 CadError（reason 见模块说明）。"""
    polys = []
    for c in conds:
        polys.extend(extract_boundary_polys(c, x))
    cell_list = cells(polys)
    return [(cell, [cond_holds(c, cell, x) for c in conds])
            for cell in cell_list]
