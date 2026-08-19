from cas import term as T
from cas.term import Expr, Int, register_norm  # register_norm：每头规范化扩展入口（见 term.NORM）
from cas.errors import BudgetExceeded

WEIGHTS = {"Power": 2, "Exp": 2, "Log": 2}
DEFAULT_W = 1

# 项 id 记忆化：驻留项不可变且内容寻址，化简结果按 _h 缓存永久有效。
# [教训：expreduce 每个项自带 EvaledHash 缓存，求值命中即跳过——驻留使 pyCAS 免费获得同款]
_MEMO = {}


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


def cost(t):
    """节点加权总和（显式栈后序，深表达式不触及 Python 递归上限）。"""
    val = {}
    for u in reversed(_postorder(t)):
        if isinstance(u, Expr):
            val[u] = WEIGHTS.get(u.head.name, DEFAULT_W) + sum(val[a] for a in u.args)
        elif isinstance(u, T.Bound):
            val[u] = 1 + val[u.body]
        else:
            val[u] = 1
    return val[t]


def _mul_expand(a, b):
    """乘法对加法分配：构造器 flatten 保证 Plus 参数不含 Plus，分配仅一层。"""
    as_ = list(a.args) if isinstance(a, Expr) and a.head.name == "Plus" else [a]
    bs = list(b.args) if isinstance(b, Expr) and b.head.name == "Plus" else [b]
    if len(as_) == 1 and len(bs) == 1:
        return T.times(a, b)
    return T.plus(*[T.times(x, y) for x in as_ for y in bs])


def expand(t):
    """环层全展开（显式栈后序重建：子项先展开，向上只做分配）。"""
    val = {}
    for u in reversed(_postorder(t)):
        if isinstance(u, Expr):
            name = u.head.name
            if name == "Plus":
                val[u] = T.plus(*[val[a] for a in u.args])
            elif name == "Times":
                acc = T.ONE
                for a in u.args:
                    acc = _mul_expand(acc, val[a])
                val[u] = acc
            elif name == "Power":
                b, e = u.args
                if isinstance(e, Int) and e.v >= 2:
                    base = val[b]
                    acc = base
                    for _ in range(e.v - 1):
                        acc = _mul_expand(acc, base)
                    val[u] = acc
                elif isinstance(e, Int) and e.v == 1:
                    val[u] = val[b]
                elif isinstance(e, Int) and e.v == 0:
                    val[u] = T.ONE
                else:
                    val[u] = u
            else:
                val[u] = u
        elif isinstance(u, T.Bound):
            val[u] = T.mk_bound(u.hint, val[u.body])
        else:
            val[u] = u
    return val[t]


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
