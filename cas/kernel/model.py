# -*- coding: utf-8 -*-
"""内核数据模型（v4 §6.2–§6.6、§6.10、§6.11）。

内核的基本对象不是「变换后的表达式」，而是**条件性、作用域化的命题**：

    Γ ⊢ P [Δ]

· Γ = Scope（声明 / 定义 / 假设）
· P = Judgment.proposition
· Δ = Judgment.requirements（未清偿条件）

结论与判定结果用**封闭变体层次**（`Applicability`）表达，让非法状态不可表示；
值对象一律 `frozen=True, slots=True`。`Step` 不分子类——步骤做了什么由结论
命题与证据说明（v4 §6.6 / AGENTS.md §三）。

内核不认识数学 head：本模块只依赖 syntax，不导入任何具体数学模块。
"""

from dataclasses import dataclass, field
from enum import Enum

from cas.syntax import term as T
from cas.kernel.ids import JudgmentId, RequirementId, ScopeId, StepId


# ---------------------------------------------------------------------------
# 作用域条目（v4 §6.2）
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Declaration:
    """声明：`x : Real`、`n : Integer`、`c : Parameter independent of x`、`y : Function(Real, Real)`。"""
    symbol: T.Term
    sort: T.Term


@dataclass(frozen=True, slots=True)
class Definition:
    """定义：`u := x²`。局部别名，不是用户需要证明的数学等式。"""
    symbol: T.Term
    body: T.Term


@dataclass(frozen=True, slots=True)
class Assumption:
    """假设：`x > 0`、`a ≠ 0`、`continuous(f, I)`。用户或分支明确接受的条件。

    开放守卫不得自动写入 assumptions（v4 不变量 5）——那是 Requirement 的事。
    """
    proposition: T.Term


# ---------------------------------------------------------------------------
# Requirement：开放条件（v4 §6.3）
# ---------------------------------------------------------------------------

class RequirementReason(Enum):
    """条件为何被引入。与判定失败理由（verdict.Reason）是两回事。"""
    DEFINEDNESS = "definedness"
    RULE_GUARD = "rule_guard"
    ALGORITHM_PRECONDITION = "algorithm_precondition"
    BRANCH_COVERAGE = "branch_coverage"
    DOMAIN_MEMBERSHIP = "domain_membership"


@dataclass(frozen=True, slots=True)
class Requirement:
    id: RequirementId
    scope: ScopeId
    proposition: T.Term
    introduced_by: StepId
    reason: RequirementReason


# ---------------------------------------------------------------------------
# Judgment / Step（v4 §6.4、§6.6）
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Judgment:
    """可依赖的数学结论：Γ ⊢ proposition [requirements]。

    `producer` 是产生它的 Step。Judgment 只能由 `kernel.commit` 创建
    （v4 不变量 3）。
    """
    id: JudgmentId
    scope: ScopeId
    proposition: T.Term
    requirements: tuple[RequirementId, ...]
    producer: StepId


@dataclass(frozen=True, slots=True)
class ContextReadSet:
    """本步读取过的上下文事实（v4 §6.11）。

    任何隐式使用都必须留下读依赖——否则「依赖某条假设却没记录」会静默发生。
    """
    entries: tuple[tuple[str, str], ...] = ()

    def merge(self, other):
        seen = dict(self.entries)
        for k, v in other.entries:
            seen[k] = v
        return ContextReadSet(tuple(sorted(seen.items())))

    def __bool__(self):
        return bool(self.entries)


@dataclass(frozen=True, slots=True)
class Step:
    """数学依赖边（v4 §6.6）：无子类，分派走 checker 注册表。

    `premises` / `conclusions` 是 Judgment id——Artifact 不能作为前提
    （v4 不变量 4）。
    """
    id: StepId
    scope: ScopeId
    premises: tuple[JudgmentId, ...]
    conclusions: tuple[JudgmentId, ...]
    evidence: object                    # kernel.evidence.Evidence
    reads: ContextReadSet = field(default_factory=ContextReadSet)


# ---------------------------------------------------------------------------
# 条件清偿与适用性（v4 §6.10）
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Discharge:
    """条件清偿：requirement 由 by_judgment 在当前 scope 证明。

    清偿不修改原 Judgment——原条件结论仍然成立，只是查询时变为可直接应用。
    """
    requirement: RequirementId
    by_judgment: JudgmentId
    scope: ScopeId


class Applicability:
    """适用性封闭层次（v4 §6.10）。

    条件被否证时不销毁原结论，只标 `Inapplicable`——原结论作为条件命题仍然
    正确，且不沿依赖边级联销毁（v3 的反向修正）。
    """
    __slots__ = ()

    def is_applicable(self):
        return self.__class__ is Applicable

    def is_conditional(self):
        return self.__class__ is Conditional

    def is_inapplicable(self):
        return self.__class__ is Inapplicable


@dataclass(frozen=True, slots=True)
class Applicable(Applicability):
    """可直接应用：所有条件已清偿。"""


@dataclass(frozen=True, slots=True)
class Conditional(Applicability):
    """条件候选：仍有未清偿 requirement。"""
    requirements: tuple[RequirementId, ...] = ()


@dataclass(frozen=True, slots=True)
class Inapplicable(Applicability):
    """在当前作用域不适用：有条件被否证。原结论不删除。"""
    refutations: tuple[JudgmentId, ...] = ()
