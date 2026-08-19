"""Refine 通道：账本驱动化简（decide 的第二大消费者，第一是域闸门）。

语义：只重写 decide 对账本判 YES 的结构，判不动的保持原样（永不静默错）。
覆盖：Abs 符号消去、√(x²) 按符号脱根、exp(log x)/log(exp x) 互逆、
Piecewise 分支按账本裁剪/选定。
实现：显式栈后序重建（深表达式不触及 Python 递归上限，与 simplify/subst 同款）。
"""

from fractions import Fraction as Fr

from cas import term as T
from cas.term import Expr, Rat
from cas.decide import decide, T3
from cas.simplify import _postorder


def _refine_node(head_name, args, ctx):
    """单节点 refine：可判则返回重写结果，否则返回 None（由调用方走 mk 重建）。"""
    if head_name == "Abs":
        (a,) = args
        if decide(T.mk(T.S("Ge"), (a, T.ZERO)), ctx) is T3.YES:
            return a
        if decide(T.mk(T.S("Le"), (a, T.ZERO)), ctx) is T3.YES:
            return T.neg(a)
        return None
    if head_name == "Power" and len(args) == 2 \
            and isinstance(args[1], Rat) and args[1].f == Fr(1, 2):
        b = args[0]
        # √(c²)：c≥0 -> c；c≤0 -> -c（判不动保持 √ 形态，sqrt_sq 规则给 |c| 兜底）
        if isinstance(b, Expr) and b.head.name == "Power" and b.args[1] is T.TWO:
            c = b.args[0]
            if decide(T.mk(T.S("Ge"), (c, T.ZERO)), ctx) is T3.YES:
                return c
            if decide(T.mk(T.S("Le"), (c, T.ZERO)), ctx) is T3.YES:
                return T.neg(c)
        return None
    if head_name == "Log" and isinstance(args[0], Expr) and args[0].head.name == "Exp":
        return args[0].args[0]   # log(exp a) = a：exp 在实数上单射，无条件
    if head_name == "Exp" and isinstance(args[0], Expr) and args[0].head.name == "Log":
        a = args[0].args[0]
        # exp(log a) = a 需 a>0（实数域）：账本可判才重写
        if decide(T.mk(T.S("Gt"), (a, T.ZERO)), ctx) is T3.YES:
            return a
        return None
    if head_name == "Piecewise" and len(args) % 2 == 0:
        kept = []
        picked = None
        hit = False
        for i in range(0, len(args), 2):
            v, c = args[i], args[i + 1]
            r = decide(c, ctx)
            if r is T3.YES:
                picked = v
                hit = True
                break
            if r is T3.NO:
                hit = True
                continue
            kept.extend([v, c])
        if not hit:
            return None
        if picked is not None:
            return picked
        if not kept:
            return T.UND
        return T.mk(T.S("Piecewise"), tuple(kept))
    return None


def refine(t, ctx):
    """账本驱动化简 -> (新项, 是否有变化)。无账本可判时原样返回。

    无条件重写（log∘exp 互逆）不依赖账本，账本空时仍可生效。
    """
    changed = False
    val = {}
    for u in reversed(_postorder(t)):
        if isinstance(u, T.Bound):
            nb = val[u.body]
            val[u] = u if nb is u.body else T._mk_bound_canon(u.hint, nb)
            continue
        if not isinstance(u, Expr):
            val[u] = u
            continue
        args = tuple(val[a] for a in u.args)
        r = _refine_node(u.head.name, args, ctx)
        if r is not None:
            val[u] = r
            changed = True
        elif any(a is not b for a, b in zip(args, u.args)):
            val[u] = T.mk(u.head, args)
            changed = True
        else:
            val[u] = u
    return val[t], changed
