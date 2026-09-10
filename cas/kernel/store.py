# -*- coding: utf-8 -*-
"""内核账本（v4 §6.9 写入、§6.10 清偿、§四.5 分层）。

追加式，不物理删除：Judgment store 只增；原结论永不因条件被否证而消失
（v3 的 dead 级联销毁是反向修正对象）。

store 只持有**已提交**的事实。计算中间产物是 Artifact，不进此处（v4 §8.2 /
AGENTS.md §四.1）——所以账本大小与重写次数无关，只与提交次数有关。
"""

from cas.kernel.evidence import CheckerRegistry
from cas.kernel.ids import JudgmentId, RequirementId, StepId
from cas.kernel.model import (
    Applicable, Conditional, Discharge, Inapplicable, Judgment, Requirement, Step,
)
from cas.kernel.scope import ScopeStore


class KernelStore:
    """追加式账本：作用域、条件、结论、步骤、清偿。"""

    def __init__(self, scopes=None, checkers=None):
        self.scopes = scopes if scopes is not None else ScopeStore()
        self.checkers = checkers if checkers is not None else CheckerRegistry()
        self._requirements: dict[RequirementId, Requirement] = {}
        self._judgments: dict[JudgmentId, Judgment] = {}
        self._steps: dict[StepId, Step] = {}
        self._discharges: dict[RequirementId, list] = {}
        self._refutations: dict[RequirementId, list] = {}
        self._next_req = 0
        self._next_jud = 0
        self._next_step = 0

    # --- id 发放 ---

    def new_requirement_id(self) -> RequirementId:
        rid = RequirementId(self._next_req)
        self._next_req += 1
        return rid

    def new_judgment_id(self) -> JudgmentId:
        jid = JudgmentId(self._next_jud)
        self._next_jud += 1
        return jid

    def new_step_id(self) -> StepId:
        sid = StepId(self._next_step)
        self._next_step += 1
        return sid

    # --- 写入（只有 commit 调用）---

    def put_requirement(self, req: Requirement) -> Requirement:
        self._requirements[req.id] = req
        return req

    def put_judgment(self, j: Judgment) -> Judgment:
        self._judgments[j.id] = j
        return j

    def put_step(self, s: Step) -> Step:
        self._steps[s.id] = s
        return s

    def add_discharge(self, d: Discharge) -> None:
        self._discharges.setdefault(d.requirement, []).append(d)

    def add_refutation(self, requirement: RequirementId, by: JudgmentId) -> None:
        """记录条件被否证：原结论保留，适用性变为 Inapplicable（v4 §6.10）。"""
        self._refutations.setdefault(requirement, []).append(by)

    # --- 查询 ---

    def get_requirement(self, rid: RequirementId) -> Requirement:
        return self._requirements[rid]

    def get_judgment(self, jid: JudgmentId) -> Judgment:
        return self._judgments[jid]

    def get_step(self, sid: StepId) -> Step:
        return self._steps[sid]

    def all_steps(self) -> tuple:
        return tuple(self._steps[i] for i in range(self._next_step))

    def all_judgments(self) -> tuple:
        return tuple(self._judgments[i] for i in range(self._next_jud))

    def requirements_of(self, jid: JudgmentId) -> tuple:
        return self._judgments[jid].requirements

    def all_requirements(self) -> tuple:
        return tuple(self._requirements.values())

    def discharges_of(self, rid: RequirementId) -> tuple:
        return tuple(self._discharges.get(rid, ()))

    def refutations_of(self, rid: RequirementId) -> tuple:
        return tuple(self._refutations.get(rid, ()))

    def is_discharged(self, rid: RequirementId, scope) -> bool:
        """在 scope 中是否已清偿：清偿发生在 scope 或其任一祖先中即可见。"""
        for d in self._discharges.get(rid, ()):
            if self.scopes.is_visible(d.scope, scope):
                return True
        return False

    def is_refuted(self, rid: RequirementId, scope) -> bool:
        for r in self._refutations.get(rid, ()):
            j = self._judgments[r]
            if self.scopes.is_visible(j.scope, scope):
                return True
        return False

    # --- 适用性（v4 §6.10）---

    def applicability(self, jid: JudgmentId, scope):
        """结论在 scope 中的适用性。

        否证优先于清偿：有任一条条件在 scope 可见范围内被否证即 Inapplicable
        （即便另一条已清偿）。原结论不删除、不级联。
        """
        reqs = self.requirements_of(jid)
        refuted = tuple(r for r in reqs if self.is_refuted(r, scope))
        if refuted:
            return Inapplicable(refutations=tuple(refuted))
        pending = tuple(r for r in reqs if not self.is_discharged(r, scope))
        if pending:
            return Conditional(requirements=pending)
        return Applicable()

    # --- 规模（性能纪律：账本大小只与提交次数有关）---

    def stats(self):
        return {
            "requirements": len(self._requirements),
            "judgments": len(self._judgments),
            "steps": len(self._steps),
            "scopes": self._next_scope_count(),
        }

    def _next_scope_count(self):
        return getattr(self.scopes, "_next", 0)
