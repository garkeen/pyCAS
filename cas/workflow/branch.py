# -*- coding: utf-8 -*-
"""Branch：条件分支（v4 §8.8）。

每个 case 用**独立子作用域**，兄弟分支互不可见（不变量 9）：

    Γ
    ├── Γ + [a ≠ 0]
    └── Γ + [a = 0]

**分支上下文不能直接合并。** 合并必须在父作用域中验证五件事（§8.8）：

    1. 分支覆盖父问题
    2. 每个分支回答同一个任务
    3. 分支结果各自在其 scope 中成立
    4. 辅助符号没有逃逸
    5. 分支开放条件被正确提升

第 5 条是分支合并最容易出错的地方：分支 `C_i` 中开放的守卫 `G_i`，提升到父层是

    C_i ⇒ G_i

而不是全局无条件要求 `G_i`。这就是 `promote_guard`。
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.kernel.ids import JudgmentId, ScopeId
from cas.workflow.ids import TaskId


@dataclass(frozen=True, slots=True)
class BranchCase:
    condition: T.Term
    scope: ScopeId
    task: TaskId | None = None
    label: str = ""


@dataclass(frozen=True, slots=True)
class BranchGroup:
    id: int
    parent_scope: ScopeId
    cases: tuple
    coverage: JudgmentId | None = None


def promote_guard(case_condition, guard):
    """分支内的开放守卫提升到父层：`C_i ⇒ G_i`（不是全局 `G_i`）。"""
    return T.implies(case_condition, guard)


def complementary_pair(cases):
    """条件列表是否含排中律互补对（c 与 ¬c 同时作为一个分支的条件）。

    这是**句法**判定，不猜语义；返回 (i, j) 或 None。
    """
    for i in range(len(cases)):
        ci = cases[i].condition
        for j in range(i + 1, len(cases)):
            cj = cases[j].condition
            if _is_neg(cj, ci) or _is_neg(ci, cj):
                return (i, j)
    return None


def _is_neg(a, b):
    return (isinstance(a, T.Expr) and isinstance(a.head, T.Sym)
            and a.head.name == "Not" and a.args[0] is b)


class BranchStore:
    """分支组存储（追加式）。"""

    def __init__(self):
        self._groups: dict[int, BranchGroup] = {}
        self._next = 0

    def create(self, parent_scope, cases) -> BranchGroup:
        gid = self._next
        self._next += 1
        g = BranchGroup(id=gid, parent_scope=parent_scope,
                        cases=tuple(cases))
        self._groups[gid] = g
        return g

    def get(self, gid) -> BranchGroup:
        return self._groups[gid]

    def set_coverage(self, gid, jid) -> BranchGroup:
        from dataclasses import replace
        g = replace(self._groups[gid], coverage=jid)
        self._groups[gid] = g
        return g

    def all(self):
        return tuple(self._groups[i] for i in range(self._next))

    def __len__(self):
        return self._next
