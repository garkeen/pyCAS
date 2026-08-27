from cas import term as T
from cas.term import Expr, Int
from cas.errors import BudgetExceeded

WEIGHTS = {"Power": 2}
DEFAULT_W = 1

# 项 id 记忆化：驻留项不可变且内容寻址，化简结果按 _h 缓存永久有效。
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


# 化简层语义 pass 注册表：head -> [pass]。当前为空——一切恒等式由
# 图书馆声明（library/），经规则引擎通用管线消费，不在此处硬编码。
# pass 协议：接收已重建的 args 元组，返回新 args 元组或 None（不动）。
_SIMPLIFY_PASSES = {}


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
                _r = None
                for _p in _SIMPLIFY_PASSES.get(u.head.name, ()):
                    _r = _p(args)
                    if _r is not None:
                        args = _r
                        break
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


def autosimplify(t, budget=100000):
    """自动通道化简：环层重建 + 图书馆 auto 规则定点迭代。

    纪律：
    · 只应用 auto 且无守卫的规则——守卫评估要回调判定管线，
      而判定管线消费本函数，有守卫的 auto 规则会形成循环；
      带守卫的规则走交互通道（REPL apply，守卫过 decide）。
    · 每步代价必须严格下降——终止性由良基性保证，不靠轮数魔法。
    """
    from cas.rules import library_ruleset, apply_rule

    rs = library_ruleset()
    auto_rules = [r for r in rs.rules.values() if r.auto and r.guard is None]
    cur = simplify(t, budget)
    rounds = 0
    while rounds < 50:
        rounds += 1
        base = cost(cur)
        nxt = None
        for path in T.all_paths(cur):
            for rule in sorted(auto_rules, key=lambda r: r.priority):
                res = apply_rule(rule, cur, path, budget=budget)
                if res.ok and cost(res.term) < base:
                    nxt = res.term
                    break
            if nxt is not None:
                break
        if nxt is None:
            return cur
        cur = simplify(nxt, budget)
    return cur
