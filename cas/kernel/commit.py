# -*- coding: utf-8 -*-
"""`commit`：唯一可信提交入口（v4 §6.9）。

**`commit` 是边界操作，不是内循环的门。** 它把候选结论升级为可依赖事实：
复核证据、收集条件、尝试清偿、原子写入 Step / Judgment / Requirement。
无守卫、无作用域变化的重写根本不必经过它——规则健全性在准入时已结清
（v4 §6.8 / AGENTS.md §四.1）。把它当成每步计算的必经关口，内核就变回
解释器，CAS 也就变成了定理证明器。

十步流程（v4 §6.9）：

    1  检查 scope 与项的绑定合法性
    2  检查 premise 是否在当前 scope 可访问
    3  调用 checker
    4  checker 验证结论并返回直接条件
    5  收集 premise 继承的未清偿条件
    6  使用当前 context 尝试清偿条件
    7  Proved   → 记录清偿依据
    8  Refuted  → 本次应用不适用，拒绝提交
    9  Unknown  → 根据 guard policy 处理
    10 原子地写入 Step、Judgment、Requirement

无前驱、无条件的典型情形退化为四步（scope 检查 → checker 调用 → 记录结论 →
原子写入），是完整流程的可证明子集（AGENTS.md §四.4）。
"""

from dataclasses import dataclass, field, replace
from enum import Enum

from cas.syntax import term as T
from cas.kernel.context import TrackedContext
from cas.kernel.evidence import Evidence
from cas.kernel.ids import StepId
from cas.kernel.model import (
    ContextReadSet, Discharge, Judgment, Requirement, RequirementReason, Step,
)
from cas.kernel.services import NullServices
from cas.kernel.verdict import Reason


class GuardPolicy(Enum):
    """守卫策略（v4 §6.9）。对 Unknown 的处置是**唯一不许关**的开关。"""
    REQUIRE_PROVED = "require_proved"        # 自动化简默认：未决不落地
    ALLOW_CONDITIONAL = "allow_conditional"  # 手动显式应用：带条件落地
    REQUEST_SPLIT = "request_split"          # 要求分类讨论


@dataclass(frozen=True, slots=True)
class StepProposal:
    scope: object
    premises: tuple = ()
    conclusions: tuple = ()
    evidence: Evidence = None
    guard_policy: GuardPolicy = GuardPolicy.REQUIRE_PROVED
    # commit 解析前提后回填（checker 只许读这里，不得信任调用方自报的前提）
    premise_propositions: tuple = field(default=())


# ---------------------------------------------------------------------------
# 提交结果：封闭层次（消费方必须穷尽分支）
# ---------------------------------------------------------------------------

class CommitResult:
    __slots__ = ()

    def is_committed(self):
        return self.__class__ is Committed

    def is_refused(self):
        return self.__class__ is Refused

    def is_undecided(self):
        return self.__class__ is Undecided

    def is_needs_split(self):
        return self.__class__ is NeedsSplit


@dataclass(frozen=True, slots=True)
class Committed(CommitResult):
    step: StepId
    judgments: tuple
    requirements: tuple
    reads: ContextReadSet = field(default_factory=ContextReadSet)


@dataclass(frozen=True, slots=True)
class Refused(CommitResult):
    """结论不成立 / 前提不可访问 / 条件被否证——本次应用不适用。"""
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


@dataclass(frozen=True, slots=True)
class Undecided(CommitResult):
    """复核未决且策略要求已证：什么都不写（未验证候选不得进入可信推导）。"""
    reason: Reason = Reason.FRAGMENT
    detail: str = ""


@dataclass(frozen=True, slots=True)
class NeedsSplit(CommitResult):
    """策略要求分类讨论：把待决条件交回工作流开分支。"""
    conditions: tuple = ()


# ---------------------------------------------------------------------------
# 提交
# ---------------------------------------------------------------------------

def commit(store, proposal, context=None, services=None,
           discharge_checker_id="kernel.decide",
           mode=None, inherited_reads=None) -> CommitResult:
    from cas.kernel.mode import DEFAULT_MODE
    mode = mode if mode is not None else DEFAULT_MODE
    services = services if services is not None else NullServices()

    # --- 1. scope 合法性与项的绑定合法性 ---
    try:
        store.scopes.get(proposal.scope)
    except KeyError:
        return Refused(Reason.FRAGMENT, f"scope 不存在: {proposal.scope}")
    # 局部符号不得泄漏到作用域之外的结论（v4 §6.1 第7条 / 不变量 15）：
    # 作用域内引入的符号（声明 / 定义左端）只在该作用域及其后代有义。
    for prop in proposal.conclusions:
        escaped = store.scopes.escapes(proposal.scope, prop)
        if escaped:
            return Refused(Reason.FRAGMENT,
                           f"局部符号逃逸到本作用域结论: {escaped!r}")
    ctx = context if context is not None \
        else TrackedContext(store.scopes, services, proposal.scope, mode)

    # --- 2. premise 可见性（子作用域结论不得反向使用；兄弟分支互不可见）---
    inherited = []
    premise_props = []
    for pid in proposal.premises:
        try:
            pj = store.get_judgment(pid)
        except KeyError:
            return Refused(Reason.FRAGMENT, f"前提不存在: {pid}")
        if not store.scopes.is_visible(pj.scope, proposal.scope):
            return Refused(Reason.FRAGMENT, f"前提 {pid} 在 scope {proposal.scope} 不可见")
        inherited.extend(pj.requirements)
        premise_props.append(pj.proposition)
    # 回填前提命题：调用方自报的值一律丢弃（checker 只读内核解析出来的）
    proposal = replace(proposal, premise_propositions=tuple(premise_props))

    # --- 3. checker ---
    checker = store.checkers.get(proposal.evidence.checker_id)
    if checker is None:
        return Undecided(Reason.FRAGMENT,
                         f"checker 未注册: {proposal.evidence.checker_id}")

    # --- 4. 复核 ---
    result = checker.check(proposal, ctx, services)
    if result.is_rejected():
        return Refused(result.reason, result.detail)

    # checker 无法复核结论：候选未经验证，任何策略下都不落地（v4 不变量 16）。
    # GuardPolicy 管的是**条件清偿**的未决（下面第 6 步之后的 Proved/Refuted/
    # Unknown），不是「结论没验过也放行」。
    if result.is_unknown():
        return Undecided(result.reason, result.detail or "结论未获复核")

    direct = tuple(result.direct_requirements) if result.is_accepted() else ()

    # --- 5/6. 条件收集与清偿尝试（Proved / Refuted / Unknown 三分）---
    proved_terms = []
    for t in direct:
        v = ctx.decide(t)
        if v.is_yes():
            proved_terms.append(t)                    # 7. Proved
        elif v.is_no():
            return Refused(Reason.GUARDED, f"条件被否证: {t!r}")   # 8. Refuted
        else:
            # 9. Unknown → 按 guard policy 处理
            if proposal.guard_policy is GuardPolicy.REQUIRE_PROVED:
                return Undecided(v.reason,
                                 f"条件未决，REQUIRE_PROVED 拒绝落地: {t!r}")
            if proposal.guard_policy is GuardPolicy.REQUEST_SPLIT:
                return NeedsSplit((t,))

    for rid in inherited:
        if store.is_refuted(rid, proposal.scope):
            return Refused(Reason.GUARDED, f"前提条件已被否证: {rid}")

    # --- 10. 原子写入 ---
    step_id = store.new_step_id()

    direct_ids = {}
    all_req = list(inherited)
    for t in direct:
        rid = store.new_requirement_id()
        store.put_requirement(Requirement(
            id=rid, scope=proposal.scope, proposition=t,
            introduced_by=step_id, reason=RequirementReason.RULE_GUARD))
        direct_ids[t] = rid
        all_req.append(rid)
    # 结论依赖**全部**直接条件与继承条件；清偿与否是另一回事（§6.10：
    # 清偿不修改原结论，只让查询时变为可直接应用）。
    carried = tuple(inherited) + tuple(direct_ids[t] for t in direct)

    jids = []
    for prop in proposal.conclusions:
        jid = store.new_judgment_id()
        store.put_judgment(Judgment(
            id=jid, scope=proposal.scope, proposition=prop,
            requirements=carried, producer=step_id))
        jids.append(jid)

    step_reads = ctx.read_set(dedupe=not mode.raw_reads())
    if inherited_reads is not None:
        # 继承的读依赖（如分支合并：结论依赖各支读过的事实，v4 §6.11）。
        # 归并与去重规则同 read_set——粒度仍由模式决定。
        step_reads = inherited_reads.merge(step_reads)
    store.put_step(Step(id=step_id, scope=proposal.scope,
                        premises=tuple(proposal.premises),
                        conclusions=tuple(jids),
                        evidence=proposal.evidence,
                        # 读依赖以 TrackedContext 的记录为准（§6.11：checker 读
                        # 上下文的唯一通道）。粒度随模式：审计保留每次出现。
                        reads=step_reads))

    # --- 7. Proved → 记录清偿依据 ---
    # interactive 推迟清偿登记（AGENTS.md §四.2）：条件**照判**（上一步，否则
    # 被否证的守卫会被放过），只是暂时不把已证条件记成 Discharge。
    if not mode.defers_discharge():
        for t in proved_terms:
            dj = _commit_decided(store, proposal.scope, t, ctx, services,
                                 discharge_checker_id, mode)
            if dj is not None:
                store.add_discharge(Discharge(requirement=direct_ids[t],
                                              by_judgment=dj,
                                              scope=proposal.scope))

    # 10d. 否证登记：结论恰为某待决条件的否定时，原结论标 Inapplicable（不删除）
    for jid, prop in zip(jids, proposal.conclusions):
        _record_refutations(store, proposal.scope, prop, jid)

    return Committed(step=step_id, judgments=tuple(jids),
                     requirements=tuple(all_req), reads=step_reads)


def _commit_decided(store, scope, proposition, ctx, services, checker_id,
                    mode=None):
    """为已判定的条件补一条经同一协议落地的结论，作为清偿依据。

    递归安全：decide-checker 不接受任何直接条件，故不会再次触发清偿。
    """
    if store.checkers.get(checker_id) is None:
        return None
    prop = StepProposal(scope=scope, premises=(), conclusions=(proposition,),
                        evidence=Evidence(checker_id, proposition),
                        guard_policy=GuardPolicy.REQUIRE_PROVED)
    res = commit(store, prop, context=ctx, services=services,
                 discharge_checker_id=checker_id, mode=mode)
    return res.judgments[0] if res.is_committed() else None


def _negated(p):
    if isinstance(p, T.Expr) and isinstance(p.head, T.Sym) and p.head.name == "Not":
        return p.args[0]
    return None


def _record_refutations(store, scope, proposition, jid):
    """结论与某待决条件互为否定时登记否证。仅做句法否定，不做语义猜测。"""
    neg = _negated(proposition)
    for req in store.all_requirements():
        if store.is_discharged(req.id, scope):
            continue
        rp = req.proposition
        if (neg is not None and rp is neg) or (_negated(rp) is proposition):
            store.add_refutation(req.id, jid)
