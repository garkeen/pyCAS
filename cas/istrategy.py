"""积分策略层对象化（sympy manualintegrate 同款：命名规则步树）。

integrate() 自动通道出结果；本模块出"推导即数据"：每步命名 + 子步，
人可干预任一步（经 :parts/:solveq 等方案命令），树可入转录回放。
分类只复用内核既有探测（不重复实现算法）：spec 表 / 线性复合 /
正向换元 / 有理算法 / tan(x/2)；不可积诚实 failed。
"""

from dataclasses import dataclass, field

from cas import term as T
from cas.pprint import to_str


@dataclass
class IntStep:
    kind: str          # table / linear / usub / rational / tan-half / failed
    note: str
    children: list = field(default_factory=list)


def format_steps(step, indent=0):
    import re

    # 哑元美化：内部换元哑元 _usub_zN 在展示层渲染为 u
    note = re.sub(r"_usub_z\d*", "u", step.note)
    lines = ["  " * indent + f"[{step.kind}] {note}"]
    for c in step.children:
        lines.extend(format_steps(c, indent + 1))
    return lines


def explain(t, x, _depth=0):
    """积分策略分类 -> IntStep 树。与 integrate() 同一套探测，只做展示分类。"""
    from cas import spec as _spec
    from cas import integrate as _zi
    from cas.solve import _linear_split

    if _depth > 2:
        return IntStep("failed", "strategy depth exceeded (honest)")
    # 1. spec 原函数表（裸 / 线性复合）
    if isinstance(t, T.Expr) and len(t.args) == 1:
        sp = _spec.get(t.head.name)
        if sp is not None and sp.anti is not None:
            arg = t.args[0]
            if arg is x:
                return IntStep("table", f"spec antiderivative: \u222b{sp.print_name} "
                                          f"({to_str(sp.anti(x))} verified by D)")
            a_, b_ = _linear_split(arg, x)
            if T.is_num(a_) and T.num_val(a_) != 0 and T.is_num(b_) and x in T.free_vars(arg):
                return IntStep("linear", f"linear composition u={to_str(arg)}: "
                                         f"scale 1/{to_str(T.N(T.num_val(a_)))}")
    # 2. 正向换元（t = h(g(x)) g'(x)；递归解释 h）
    us = _zi._try_usub(t, x)
    if us is not None:
        _F, _ok, g, h, _H = us
        vs = sorted(T.free_vars(h), key=lambda v: v.name)
        if len(vs) == 1:
            return IntStep("usub", f"u = {to_str(g)} (du divides integrand)",
                           [explain(h, vs[0], _depth + 1)])
        return IntStep("usub", f"u = {to_str(g)} (du divides integrand)")
    # 3. 有理函数算法
    try:
        _P, _Q = _zi._rat_pair(t, x)
        return IntStep("rational", "Hermite reduction + Rothstein-Trager log part "
                                    "(algorithm; verify by D)")
    except Exception:
        pass
    # 4. 三角 tan(x/2)
    if _zi._trig_check(t, x):
        return IntStep("tan-half", "t = tan(x/2) substitution -> rational integration")
    return IntStep("failed", "no strategy found (honest refusal; try :parts)")
