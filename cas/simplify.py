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


def _pass_exp_add_law(args):
    """exp 加法定律：exp(a)*exp(b) -> exp(a+b)（无条件恒等，化简层
    语义——合并后 Exp 因子单调减少，重建循环必终止）。

    B8 入册：原为 rebuild 循环内联特例；化简层语义重写统一在此
    注册表枚举（构造期折叠不收它——合并是代价选择而非规范形要求）。
    """
    exps = [a for a in args if isinstance(a, Expr) and a.head.name == "Exp"]
    if len(exps) >= 2:
        rest = [a for a in args if a not in exps]
        merged = T.mk(T.S("Exp"), (T.plus(*[e.args[0] for e in exps]),))
        return tuple(rest) + (merged,)
    return None


def _pass_exp_pow_expand(args):
    """Exp(a)^n -> Exp(n*a)：mk 幂合并会把 e^x*e^x 收为 Exp^2 形态，
    此处展开回单项指数，使加法定律与判零链完整（整数指数无条件）。"""
    if (len(args) == 2 and isinstance(args[0], Expr)
            and args[0].head.name == "Exp" and isinstance(args[1], T.Int)):
        merged = T.mk(T.S("Exp"), (T.times(args[1], args[0].args[0]),))
        return (merged,)
    return None


# B8 化简层语义 pass 注册表：head -> [具名 pass]。每个 pass 接收
# 已重建的 args 元组，返回新 args 或 None（不动）。
_SIMPLIFY_PASSES = {
    "Times": [_pass_exp_add_law],
    "Power": [_pass_exp_pow_expand],
}


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
            val[u] = T._mk_bound_canon(u.hint, val[u.body])
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
                args = tuple(val[a] for a in u.args)
                # B8 入册：化简层语义 pass 统一走注册表（见
                # _SIMPLIFY_PASSES），重建循环内不再有游离特例。
                # 协议：Times 类 pass 返回新 args（同头重建）；Power
                # 幂展开返回单元素元组 ⟹ 节点整体替换为该单项
                # （Exp(a)^n -> Exp(n·a)，判零链依赖此形态）。
                _r = None
                for _p in _SIMPLIFY_PASSES.get(u.head.name, ()):
                    _r = _p(args)
                    if _r is not None:
                        break
                if _r is not None:
                    if u.head.name == "Power":
                        val[u] = _r[0]
                        continue
                    args = _r
                val[u] = T.mk(u.head, args)
            elif isinstance(u, T.Bound):
                # 重建已抽象体不得重新 mk_bound（_abstract 会提升体里已有 DB 引用）
                val[u] = T._mk_bound_canon(u.hint, val[u.body])
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
