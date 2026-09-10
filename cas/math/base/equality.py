# -*- coding: utf-8 -*-
"""等式与域标准形（v4 §三 目标位置：`math/base/equality.py`）。

**域标准形即判定过程**——这不是「化简器碰运气」，而是：

    判等 = 化简为规范形后判定

`normal_form` 把项（或等式）化到所属域的标准形；`equal` 在标准形上判定，命中
即完全判定，投影落空则退回字面折叠、再落空交由调用方按「未决」处理（**不猜**）。

这也是 v4 §零.1「判等第一优先」的实现落点：任何新结构要进系统，先打通这条通道。
"""

from cas.syntax import term as T
from cas.syntax.term import Expr
from cas.math.project import project, zero_of, normalize as proj_normalize
from cas.math.qarith import fold


def is_eq(t) -> bool:
    return isinstance(t, Expr) and t.head.name == "Eq"


def normal_form(t):
    """项或等式的域标准形：投影命中则取域标准形，落空原样返回。

    等式按「两侧差值 = 0」化：`Eq(l, r) → Eq(nf(l − r), 0)`——两边同时化简到
    同一标准形与把差值化零是同一件事，取后者可少维护一套等式专用规范形。
    """
    if is_eq(t):
        lhs, rhs = t.args
        hit = project(T.plus(lhs, T.neg(rhs)))
        if hit is not None:
            return T.eq(proj_normalize(hit), T.ZERO)
        return t
    hit = project(t)
    if hit is not None:
        return proj_normalize(hit)
    return t


def equal(a, b) -> bool:
    """等式判等：两侧差值经投影判零（K(x) ⊇ K[x] ⊇ ℚ）。

    仅在投影覆盖到的片段内**完全判定**；覆盖不到时退回字面折叠比较（句法等价
    即真），仍不可判则按「不等」返回——调用方若需三值语义，应先查片段覆盖
    （`verdict`/`decide`），此处不生成 UNKNOWN 以免与判定层词汇混淆。
    """
    if not is_eq(a) or not is_eq(b):
        return a is b
    la, ra = a.args
    lb, rb = b.args
    d = T.plus(T.plus(la, T.neg(ra)), T.neg(T.plus(lb, T.neg(rb))))
    z = zero_of(d)
    if z is True:
        return True
    if z is False:
        return False
    return fold(T.plus(la, T.neg(ra))) is fold(T.plus(lb, T.neg(rb)))
