# -*- coding: utf-8 -*-
"""子项抽象（v4 §5.4）。

把满足谓词的**极大**子项替换为新符号，从而把复杂子表达式降为代数独立元：

    sin(x)^2 + sin(x)   --abstract(is_Sin)-->   _u0^2 + _u0

**相同子项映射到同一个符号**（按驻留指针恒等），这是能多项式化的前提；
`thaw` 是把符号换回原项的逆操作。

用途：循环积分方程（§9.5 的 `I(x) → u`）、把 `sin(x)` 当代数未知量、把
`y'(x)` 当方程未知量、矩阵表达式方程、特殊函数表达式的多项式化。

**这只是语法抽象。** 把冻结项视为代数独立元是否安全，由使用它的数学算法与
checker 决定（v4 §5.4 末句）——本模块不作任何数学判断。

绑定体内不抽象：de Bruijn 索引只在原绑定作用域内有效，把体内子项冻出绑定层
会让 `#i` 逃逸（本模块显式不下降进 `Bound` 的体，`Bound` 作为整体不匹配）。
"""

from dataclasses import dataclass

from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class Abstraction:
    """抽象结果：新项 + (符号, 原项) 表（该顺序即 `thaw` 的环境）。"""
    term: T.Term
    replacements: tuple

    def thaw(self, t=None):
        """按本抽象的环境还原（默认还原抽象结果本身）。"""
        return thaw(self.term if t is None else t, self.replacements)


def abstract_subterms(t, predicate, prefix="_u"):
    """把满足 predicate 的极大子项替换为新符号。

    · 极大：一个子项匹配即不再下降进它（`sin(x)` 匹配时 `x` 不会被单独抽象）；
    · 同一：相同子项（驻留指针恒等）共用同一个符号；
    · 新鲜：新符号名避开 `t` 的全部自由变量。
    """
    used = {s.name for s in T.free_vars(t)}
    reps = []
    seen = {}
    counter = [0]

    def fresh():
        while True:
            name = f"{prefix}{counter[0]}"
            counter[0] += 1
            if name not in used:
                used.add(name)
                return T.S(name)

    def walk(u):
        if predicate(u):
            sym = seen.get(u)
            if sym is None:
                sym = fresh()
                seen[u] = sym
                reps.append((sym, u))
            return sym
        if isinstance(u, T.Expr):
            args = tuple(walk(a) for a in u.args)
            if all(a is b for a, b in zip(args, u.args)):
                return u
            return T.mk(u.head, args)
        return u

    return Abstraction(term=walk(t), replacements=tuple(reps))


def thaw(t, environment):
    """把抽象符号按环境换回原项（`abstract_subterms` 的逆）。

    环境是 `((Symbol, Term), ...)`；用 `subst` 重建（会重新 AC 规范化，故
    `thaw(abstract(x)) is x` 只在原项已是规范形时成立——判等请走域层，不要
    依赖指针）。
    """
    if not environment:
        return t
    return T.subst(t, dict(environment))
