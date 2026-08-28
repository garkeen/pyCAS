# -*- coding: utf-8 -*-
"""结构微分：任意数域系数 × 任意已声明函数域。

纯规则递归——反复套用：
· 常数/变元：ℚ 系数与命名常数导数为 0，d(x)/dx = 1
· Plus/Times：线性 + 莱布尼茨律
· Power：幂规则 / 指数规则 / 一般 exp·log 形式
· 函数：图书馆导数模板实例化（DB(0) 提升为参数）× 链式因子

诚实边界：
· 模板缺失 → DiffError，附图书馆说明
· 顶层 Piecewise → DiffError（整体逐支求导在分段点不安全，见下）；审慎
  通道 `differentiate_piecewise` 提供逐支导数 + 分段点显式未验证标注
· 多参数函数、绑定体（Bound）内微分 → DiffError（未建）
结果经 fold 收拢；项层产物可由域层导数（p_deriv/rf_deriv）独立
交叉验证（见 workflow Diff 步骤验证器与 stress/stress_diff.py）。
分段值模板（如 Abs 的 sign 导数）经链式法则留在驻留项，源在域外时
工作流验证器诚实返回 UNKNOWN（步骤 open），不自证。
"""

from cas import term as T
from cas.term import Expr, Sym, Bound
from cas.errors import DiffError
from cas.qarith import fold
import library


def differentiate(t, x: Sym):
    """d(t)/dx：结构递归 + 规则套用，结果折叠。"""
    return fold(_diff(t, x))


def _has(t, x) -> bool:
    return x in T.free_vars(t)


def _diff(t, x):
    if T.is_num(t):
        return T.ZERO
    if isinstance(t, Sym):
        return T.ONE if t is x else T.ZERO
    if isinstance(t, T.Const):
        return T.ZERO                       # 命名常数（π、e、γ……）
    if isinstance(t, Bound):
        raise DiffError("绑定体内微分未建（量词/积分地基未完成）")
    if not isinstance(t, Expr):
        raise DiffError(f"无法微分的项：{t!r}")
    head = t.head.name
    if head == "Plus":
        return T.plus(*(_diff(a, x) for a in t.args))
    if head == "Times":
        # 莱布尼茨：Σᵢ a₁…aᵢ₋₁·daᵢ·aᵢ₊₁…aₙ
        parts = []
        for i, a in enumerate(t.args):
            da = _diff(a, x)
            others = [t.args[j] for j in range(len(t.args)) if j != i]
            parts.append(T.times(*others, da))
        return T.plus(*parts)
    if head == "Power":
        b, e = t.args
        db, de = _diff(b, x), _diff(e, x)
        if not _has(e, x):
            # 幂规则：e·b^(e-1)·db（e 常数，含分数/负数）
            return T.times(e, T.pw(b, T.plus(e, T.MONE)), db)
        if not _has(b, x):
            # 指数规则：b^e·ln(b)·de
            return T.times(t, T.log(b), de)
        # 一般情形：b^e·(de·ln b + e·db/b)
        return T.times(t, T.plus(T.times(de, T.log(b)),
                                 T.times(e, db, T.pw(b, T.MONE))))
    if head in ("Eq", "Ne", "Lt", "Le", "Gt", "Ge", "And", "Or", "Not"):
        raise DiffError("谓词不可微分")
    if head == "Piecewise":
        # 逐支求导在分段点不安全：闭区域边界上的导数须另校验连续性与单侧导数，
        # 段内导数拼起来不等于整体导数（例 x²(x≤0)|x(x>0) 在 0 处左右导不等却
        # 逐支给出 0）。分段求导的审慎通道未建——诚实拒答，不冒充结果。
        raise DiffError("分段函数逐支求导在分段点须校验连续性与单侧导数，未建")
    # 函数应用：查图书馆导数模板
    tpl, note = library.function_deriv(head)
    if tpl is None:
        raise DiffError(f"{head} 无导数模板" + (f"（{note}）" if note else ""))
    d = library.lookup_function(head)
    if d is not None and d.arity is not None and len(t.args) != d.arity:
        raise DiffError(f"{head} 声明元数 {d.arity}，实收 {len(t.args)} 参")
    if len(t.args) != 1:
        raise DiffError(f"{head} 多参数微分未建（偏导地基未完成）")
    arg = t.args[0]
    inner = T._lift(tpl, arg, 0)            # DB(0) 实例化为参数
    return T.times(inner, _diff(arg, x))    # 链式法则：模板值 × 内层导数


def differentiate_piecewise(t, x: Sym):
    """分段求导（审慎通道）：逐支对开区间胞腔求导，分段点显式标注未验证。

    导数只在开区间胞腔（单一分支主宰的开邻域）上成立；分段点（点胞腔）
    的可导性须连续性与单侧导数校验（极限层 §6.5，未建），故单独列出，
    绝不把逐支导数冒充为分段点导数。

    返回 (导数分段, 未验证分段点胞腔列表)。条件非单变量多项式分区时
    透传 cad.CadError。"""
    from cas.piecewise import branches, piecewise, fold_nested, domain_cells
    t = fold_nested(t)
    deriv = piecewise([(differentiate(v, x), c) for v, c in branches(t)])
    boundaries = [cell for cell, _v in domain_cells(t, x)
                  if cell.kind == "point"]
    return deriv, boundaries
