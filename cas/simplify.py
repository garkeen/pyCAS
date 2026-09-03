from cas import term as T
from cas.term import Expr, Int
from cas.errors import BudgetExceeded
from cas.termpath import postorder

# 项 id 记忆化：驻留项不可变且内容寻址，化简结果按 _h 缓存永久有效。
_MEMO = {}


def cost(t):
    """节点总数（均匀代价，显式栈后序）。良基自然数，供代价下降判据。"""
    n = 0
    for _u in postorder(t):
        n += 1
    return n


def _mul_expand(a, b):
    """乘法对加法分配：构造器 flatten 保证 Plus 参数不含 Plus，分配仅一层。"""
    as_ = list(a.args) if isinstance(a, Expr) and a.head.name == "Plus" else [a]
    bs = list(b.args) if isinstance(b, Expr) and b.head.name == "Plus" else [b]
    if len(as_) == 1 and len(bs) == 1:
        return T.times(a, b)
    return T.plus(*[T.times(x, y) for x in as_ for y in bs])


def expand(t):
    """环层全展开（显式栈后序重建：子项先展开，向上只做分配）。

    注意：生产路径目前不消费本函数，唯一调用方是压力台架
    （stress/stress_qarith.py）。它不是死代码（被测试使用），但与
    cas/domains/poly 的 Times 展开存在功能重叠——合并前需先确认
    压力台架改用哪一侧。
    """
    val = {}
    for u in reversed(postorder(t)):
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
        for u in reversed(postorder(root)):
            spent -= 1
            if spent < 0:
                raise BudgetExceeded()
            if u in val:
                continue
            if isinstance(u, Expr):
                args = tuple(val[a] for a in u.args)
                val[u] = T.mk(u.head, args)
            elif isinstance(u, T.Bound):
                # 重建已抽象体不得重新 mk_bound（_abstract 会提升体里已有 DB 引用）
                val[u] = T._mk_bound_canon(u.hint, val[u.body])
            else:
                val[u] = u
        return val[root]

    # 不动点迭代：mk 构造器幂等（已规范化的 args 重建不变），故收敛于至多两轮；
    # 循环条件即真不动点判据，无轮数魔法。
    prev = t
    while True:
        nxt = rebuild(prev)
        if nxt is prev:
            _MEMO[t._h] = prev
            return prev
        prev = nxt


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
    # 终止性：每次接受规则都使 cost 严格下降（良基自然数），必达不动点，无轮数上限。
    while True:
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
