from cas.syntax import term as T
from cas.syntax.term import Expr
from cas.errors import BudgetExceeded
from cas.syntax.termpath import postorder

# 项 id 记忆化：驻留项不可变且内容寻址，化简结果按 _h 缓存永久有效。
_MEMO = {}


def cost(t):
    """节点总数（均匀代价，显式栈后序）。良基自然数，供代价下降判据。"""
    n = 0
    for _u in postorder(t):
        n += 1
    return n


def simplify(t, budget=100000):
    """自底向上重建：每层经驻留构造器 mk 重新驻留。

    mk 只做**表示**规范化（AC 拉平/排序/幂等去重/单位元吸收），不做环层
    代数标准形（v4 §2.1：项是纯语法，构造期不判定）。因此对已驻留的项，
    重建后重新驻留必得同一节点——本函数在常规输入下即恒等，唯一作用是
    把「子项被替换过」的情形沿父链重新驻留（预算按节点计，超限抛
    BudgetExceeded）。结果按项 id 记忆化（项不可变，缓存永久有效）。
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
    from cas.math.rules import declared_ruleset, apply_rule

    rs = declared_ruleset()
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
