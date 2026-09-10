# -*- coding: utf-8 -*-
"""应用门面（v4 §三 目标树 `api.py`；§四 依赖方向的落点）。

**frontend 只许依赖 `api` / `workflow` / `runtime`**（v4 §四 的表）。此前前端
直接 import 了七个具体数学模块（`qarith` / `judge` / `tactics` / `diff` / `cad` /
`integrate` / `piecewise`）以及 `kernel.verdict`，绕过了那张表——而
`runtime/dispatch.py` 的注释自己写着「前端不得直连 math，§四」。本模块是这些
设施的**唯一出口**，门禁见 `tests/test_v4_invariants.py`
（`test_dependency_frontend_only_api_workflow_runtime`）。

门面只做**转发**：不新增语义、不缓存、不改拒答行为。拒答异常
（`DiffError` / `IntegrateError` / `CadError` / `TacticsError`）也在此出口，
前端不必再去 `cas.math.*` 取异常类型。
"""

from cas.errors import CadError, DiffError, IntegrateError, TacticsError
from cas.kernel.verdict import NO, YES
from cas.math.diff import differentiate, differentiate_piecewise
from cas.math.integrate import definite_integrate, integrate_term
from cas.math.judge import back_substitute, guard_report
from cas.math.piecewise import is_piecewise
from cas.math.qarith import fold
from cas.math.rules import apply_rule, declared_ruleset
from cas.math.tactics import solve_linear, solve_piecewise
from cas.runtime.dispatch import domain_normal_form

__all__ = (
    # 判定结果单例（前端只读比较，不构造 verdict）
    "YES", "NO",
    # 拒答异常
    "DiffError", "IntegrateError", "CadError", "TacticsError",
    # ℚ 字面算术与域标准形
    "fold", "domain_normal_form",
    # 回代判官（验证侧；求解器在 tactics）
    "back_substitute", "guard_report",
    # 求解 / 微分 / 积分 / 分段
    "solve_linear", "solve_piecewise",
    "differentiate", "differentiate_piecewise",
    "integrate_term", "definite_integrate",
    "is_piecewise",
    # 声明规则（前端 rules / apply 命令）
    "declared_ruleset", "apply_rule",
)
