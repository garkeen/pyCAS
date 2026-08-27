# -*- coding: utf-8 -*-
"""定义域条件提取（守卫系统的结构通道）。

Power 的约束是环层句法的通用规则（负整幂底 ≠ 0、偶分母有理幂底 ≥ 0
等），住内核；函数头的约束由图书馆声明注册（library.register_domain_cond），
内核运行时查询——语义归图书馆，结构归内核，两不混淆。

原居 cas/domain.py（值域+代数域概念分裂的遗留），该模块已废除。
"""

from cas import term as T
from cas.term import S, Int, Rat
import library

# 函数头定义域条件注入点：{head_name -> callable(t) -> [constraint]}。
# 内核不硬连任何函数声明总表；宿主在启动时按需注册。
DOM_HOOKS = {}


def _guarded(cond, guards):
    """分支守卫的条件化：¬cond ∨ guard（该分支只在 cond 成立处生效，
    其定义域义务随之只在 cond 下需要兑现）。"""
    neg = T.mk(S("Not"), (cond,)) if cond is not T.TRUE else T.FALSE
    return [T.mk(S("Or"), (neg, g)) for g in guards]


def dom_condition(t, out=None):
    """递归提取定义域约束（纯结构，不判值）。

    Power 约束为结构性通用规则：负整数幂 a^-k -> a≠0；偶分母有理幂
    a^(p/q) -> a≥0；负有理幂 a^-e：偶分母 -> a>0（非负且非零），
    奇分母 -> a≠0。Piecewise 逐分支提取体约束并条件化（¬cond ∨ 约束），
    分支间的并由判定层按析取处理。其余函数头经 DOM_HOOKS / 图书馆声明注入。
    """
    if out is None:
        out = []
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Power":
            b, e = t.args
            if isinstance(e, Int) and e.v < 0:
                out.append(T.mk(S("Ne"), (b, T.ZERO)))
            elif isinstance(e, Rat):
                if e.f >= 0 and e.f.denominator % 2 == 0:
                    out.append(T.mk(S("Ge"), (b, T.ZERO)))
                elif e.f < 0:
                    if e.f.denominator % 2 == 0:
                        out.append(T.mk(S("Gt"), (b, T.ZERO)))
                    else:
                        out.append(T.mk(S("Ne"), (b, T.ZERO)))
        elif name == "Piecewise" and len(t.args) % 2 == 0:
            a = t.args
            for i in range(0, len(a), 2):
                v, c = a[i], a[i + 1]
                body = []
                dom_condition(v, body)          # 分支体自身约束（含嵌套）
                out.extend(_guarded(c, body))
            return out                          # 条件是命题，不作值域守卫
        else:
            h = DOM_HOOKS.get(name)
            if h is not None:
                out.extend(h(t))
            else:
                fn = library.lookup_domain_cond(name)
                if fn is not None:
                    out.extend(fn(t))
        for x in t.args:
            dom_condition(x, out)
    elif isinstance(t, T.Bound):
        dom_condition(t.body, out)
    return out
