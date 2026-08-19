from cas import term as T
from cas.term import Expr, Int, register_norm  # register_norm：每头规范化扩展入口（见 term.NORM）
from cas.errors import BudgetExceeded

WEIGHTS = {"Power": 2, "Exp": 2, "Log": 2}
DEFAULT_W = 1

# 项 id 记忆化：驻留项不可变且内容寻址，化简结果按 _h 缓存永久有效。
# [教训：expreduce 每个项自带 EvaledHash 缓存，求值命中即跳过——驻留使 pyCAS 免费获得同款]
_MEMO = {}


def cost(t):
    if isinstance(t, Expr):
        w = WEIGHTS.get(t.head.name, DEFAULT_W)
        return w + sum(cost(a) for a in t.args)
    if isinstance(t, T.Bound):
        return 1 + cost(t.body)
    return 1


def _mul_expand(a, b):
    if isinstance(a, Expr) and a.head.name == "Plus":
        return T.plus(*[_mul_expand(x, b) for x in a.args])
    if isinstance(b, Expr) and b.head.name == "Plus":
        return T.plus(*[_mul_expand(a, y) for y in b.args])
    return T.times(a, b)


def expand(t):
    if isinstance(t, Expr):
        name = t.head.name
        if name == "Plus":
            return T.plus(*[expand(a) for a in t.args])
        if name == "Times":
            acc = T.ONE
            for a in t.args:
                acc = _mul_expand(acc, expand(a))
            return acc
        if name == "Power":
            b, e = t.args
            if isinstance(e, Int) and e.v >= 2:
                base = expand(b)
                acc = base
                for _ in range(e.v - 1):
                    acc = _mul_expand(acc, base)
                return acc
            if isinstance(e, Int) and e.v == 1:
                return expand(b)
            if isinstance(e, Int) and e.v == 0:
                return T.ONE
            return t
    return t


def _postorder(t):
    """显式栈后序遍历（不依赖 Python 递归栈，深表达式安全）。"""
    order = []
    stack = [t]
    while stack:
        u = stack.pop()
        order.append(u)
        if isinstance(u, Expr):
            stack.extend(u.args)
        elif isinstance(u, T.Bound):
            stack.append(u.body)
    return order


def simplify(t, budget=100000):
    """自底向上重建：每层经规范化构造器 mk（构造即规范化）。

    环层（Plus/Times/Power）的规范形由 mk 保证；本函数负责把子项变化向上传播。
    实现为显式工作栈（文档 §2 工程约束），预算按节点计；
    结果按项 id 记忆化（项不可变，缓存永久有效）。
    """
    hit = _MEMO.get(t._h)
    if hit is not None:
        return hit
    spent = budget

    def rebuild(root):
        nonlocal spent
        val = {}
        for u in reversed(_postorder(root)):
            spent -= 1
            if spent < 0:
                raise BudgetExceeded()
            if u in val:
                continue
            if isinstance(u, Expr):
                val[u] = T.mk(u.head, tuple(val[a] for a in u.args))
            elif isinstance(u, T.Bound):
                val[u] = T.mk_bound(u.hint, val[u.body])
            else:
                val[u] = u
        return val[root]

    prev = t
    for _ in range(20):
        nxt = rebuild(prev)
        if nxt is prev:
            _MEMO[t._h] = prev
            return prev
        prev = nxt
    _MEMO[t._h] = prev
    return prev
