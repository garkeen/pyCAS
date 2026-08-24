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
    """积分策略步树 —— B7：从单一执行踪迹派生。

    不再并行重跑分类：直接执行真实 integrate()，步树由
    intcore._LAST_TRACE（求解器命中/错过序列）构造——展示与
    执行同源，结构性不可能各说各话。子步 = 本次顶层调用期间
    内层递归 integrate 的命中（如 usub 的 ∫h du）。不可积/
    证明性拒答如实出 failed 节点并携带原因。
    """
    from cas.intcore import integrate as _ig, _LAST_TRACE
    from cas.risch import RischNonElementary, RischUnsupported
    from cas.errors import BudgetExceeded

    try:
        F, ok, method, provisos = _ig(t, x)
    except (RischNonElementary, RischUnsupported) as e:
        return IntStep("failed", f"{type(e).__name__}: {e}")
    except BudgetExceeded:
        return IntStep("failed", "budget exceeded (honest abort)")

    def kind_of(entry):
        m = entry.get("method", "")
        slv = entry.get("solver", "")
        if "linear composition" in m:
            return "linear"
        if m.startswith("spec antiderivative") or "multi-angle" in slv:
            return "table"
        if "u-substitution" in m or "u-substitution" in slv:
            return "usub"
        if "Hermite" in m or "power rule" in m:
            return "rational"
        if "tan(x/2)" in m:
            return "tan-half"
        if "tower" in m or "Risch" in m:
            return "tower"
        if "special function" in m:
            return "special"
        return "step"

    hits = [e for e in _LAST_TRACE if e.get("ev") == "hit"]
    if not hits:
        return IntStep("failed", "no strategy fired (trace empty)")
    # 根 = 最外层命中；内层递归（depth 更大）按执行序作子步
    root_e = min(hits, key=lambda e: e["depth"])
    tag = "VERIFIED" if root_e.get("ok") else "UNVERIFIED"
    root = IntStep(kind_of(root_e),
                   f"{root_e.get('method','')} [{tag}]")
    for e in hits:
        if e is root_e or e["depth"] <= root_e["depth"]:
            continue
        ctag = "VERIFIED" if e.get("ok") else "UNVERIFIED"
        root.children.append(IntStep(kind_of(e),
                                     f"{e.get('method','')} [{ctag}]"))
    return root
