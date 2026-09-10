# -*- coding: utf-8 -*-
"""数学算法门面：workflow 需要、但不能自己 import 的算法（v4 §四）。

workflow 层的职责是「组织计算、登记边界」，它时不时需要两样**数学**能力：

    domain_of(term)                 投影该式所属域（步骤展示用）
    solve_linear_constraints(...)   约束系统的线性求解（不可信侧）

这两样都住在 `cas.math`，而 §四 禁止 `workflow → cas.math`。所以它们在这里被
包成一个门面，由 runtime 注入 workflow——workflow 只知道「有个 algorithms 能问
这两件事」，不知道它们怎么实现。

**注意求解器的位置**：它在不可信侧（可以给错候选），产出仍须经
`constraint.satisfied` checker 复核；门面只负责把调用接过去。
"""


class Algorithms:
    """workflow 可见的数学算法门面。"""

    def domain_of(self, term) -> str:
        """该项所属域名（投影赋予，不做叶嗅探）；落空返回空串。"""
        from cas.math.project import project
        from cas.syntax.term import Expr, Sym
        t = term
        if (isinstance(term, Expr) and isinstance(term.head, Sym)
                and term.head.name == "Eq"):
            la, ra = term.args
            from cas.syntax import term as T
            t = T.plus(la, T.neg(ra))
        hit = project(t)
        return hit.name if hit is not None else ""

    def solve_linear_constraints(self, relations, unknowns):
        """从等式约束提取未知量的线性系统并求解。

        返回 `(valuation, complete)`；求解器拒答（非线性 / 不相容）返回 None。
        """
        from cas.math.constraints import solve_linear_constraints
        return solve_linear_constraints(relations, unknowns)
