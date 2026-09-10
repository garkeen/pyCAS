# -*- coding: utf-8 -*-
"""基础模块的 checker（v4 §三 目标位置：`math/base/checkers.py`）。

阶段2 这些 checker 曾以「包裹旧验证器」的形式暂居 `cas/workflow/checkers.py`；
阶段6 迁回数学侧——**它们验证的是数学，不是工作流**，住在 workflow 里会让
`workflow → cas.math` 反向依赖（v4 §四 禁止）。

checker 协议（v4 §6.7）：`check(proposal, context, services) -> CheckResult`。
两条不变的纪律：

· 结论的**实例**必须复核，不信任调用方自报（前驱命题由 `commit` 解析后回填到
  `proposal.premise_propositions`）；
· **守卫由 checker 判定并回报**（`Accepted.direct_requirements`），内核据此建
  Requirement 并尝试清偿——checker 不自己裁决条件成立与否。

本模块的共享助手（`_eq_equal` / `_normalize_eq` / `_ok` …）也被
`math/calculus/*/checkers.py` 与 `math/solving/equations/checkers.py` 复用。
"""

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.term import Expr, S
from cas.syntax.match import matches
from cas.kernel.evidence import Accepted, Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.math.domcond import dom_condition
from cas.math.base.equality import equal, normal_form


# ---------------------------------------------------------------------------
# 共享助手
# ---------------------------------------------------------------------------

def _is_eq(t) -> bool:
    return isinstance(t, Expr) and t.head.name == "Eq"


def _is_piecewise(t) -> bool:
    from cas.math.piecewise import is_piecewise
    return is_piecewise(t)


def _ok(proposal, context, extra=()):
    """通过，并回报直接条件（内容定义域约束 + 类型特定条件）。"""
    content = proposal.conclusions[0]
    reqs = tuple(dom_condition(content)) + tuple(extra)
    return Accepted(direct_requirements=reqs, reads=context.read_set())


def _one_conclusion(proposal):
    if len(proposal.conclusions) != 1:
        return None, Rejected(Reason.FRAGMENT, "checker 只接受单结论提案")
    return proposal.conclusions[0], None


def _premise(proposal):
    if not proposal.premise_propositions:
        return None
    return proposal.premise_propositions[0]


def _same_subst(a, b):
    """两个替换是否逐洞相同（项按指针，序列按元素指针）。"""
    if set(a) != set(b):
        return False
    for k, va in a.items():
        vb = b[k]
        if isinstance(va, tuple) or isinstance(vb, tuple):
            if not (isinstance(va, tuple) and isinstance(vb, tuple)):
                return False
            if len(va) != len(vb) or any(x is not y for x, y in zip(va, vb)):
                return False
        elif va is not vb:
            return False
    return True


def _rule_conditions(rule, subst):
    """规则守卫实例化为具体条件。checker 报告条件，判定与清偿归内核。"""
    if rule.guard is None:
        return ()
    return (P.instantiate(rule.guard, subst),)


# ---------------------------------------------------------------------------
# checker
# ---------------------------------------------------------------------------

class ClaimChecker:
    """断言入账：命题必须已登记为当前作用域的假设（v4 §6.2）。

    不是「无条件放行」——内核复核假设确实存在，故不是 fail-open。
    同时回报**表达式自身的定义域条件**：`x/x` 被断言时即携带 `x ≠ 0`，
    后续重写经内核继承，条件不会在化简中丢失（v4 §9.1）。
    """
    id = "assumption.entry"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        if not any(a is content for a in context.assumptions()):
            return Rejected(Reason.FRAGMENT, "断言未登记为作用域假设")
        return _ok(proposal, context)


class BothSidesChecker:
    """等式两边同施加运算。mul/div 要求运算元 ≠ 0（作为直接条件回报，
    由内核判定与清偿——checker 不自己裁决，只声明条件）。"""
    id = "both_sides.operate"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None or not _is_eq(pred):
            return Rejected(Reason.FRAGMENT, "前驱不是等式")
        d = proposal.evidence.payload
        lhs, rhs = pred.args
        op = d.op
        if op == "add":
            exp = T.eq(T.plus(lhs, d.operand), T.plus(rhs, d.operand))
        elif op == "sub":
            exp = T.eq(T.plus(lhs, T.neg(d.operand)),
                       T.plus(rhs, T.neg(d.operand)))
        elif op == "mul":
            exp = T.eq(T.times(lhs, d.operand), T.times(rhs, d.operand))
        elif op == "div":
            exp = T.eq(T.times(lhs, T.pw(d.operand, T.N(-1))),
                       T.times(rhs, T.pw(d.operand, T.N(-1))))
        else:
            return Rejected(Reason.FRAGMENT, f"未知运算: {op}")
        if not equal(content, exp):
            return Rejected(Reason.FRAGMENT, "内容与前驱运算结果不符")
        extra = ()
        if op in ("mul", "div"):
            extra = (T.mk(S("Ne"), (d.operand, T.ZERO)),)
        return _ok(proposal, context, extra)


class NormalizeChecker:
    """重写为域标准形：内容 == 前驱的域标准形（不涉及规则搜索）。"""
    id = "equality.normalize"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        if equal(content, normal_form(pred)):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "内容不是前驱的域标准形")


class RuleInstanceChecker:
    """声明规则在 (path, substitution) 处的**一次实例**。

    只验证给定实例，四步：
      1. 规则查表——规则是数据，不是搜索；
      2. 给定替换确为该位置的一个匹配（用 syntax 层的模式匹配器核验匹配
         关系；与提出方「遍历路径与规则去找匹配」的**搜索**是两回事）；
      3. 结果确为该模板在该替换下的实例化；
      4. 前驱其余部分原样保留（只改 path 处）。

    checker 不导入 `apply_rule` 一类搜索器，也不遍历路径（v4 §7.3 / 不变量 14）。
    """
    id = "rule.instance"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        d = proposal.evidence.payload
        from cas.math.rules import declared_ruleset
        rule = declared_ruleset().rules.get(d.rule)
        if rule is None:
            return Rejected(Reason.FRAGMENT, f"未知规则: {d.rule}")
        if d.substitution is None:
            return Rejected(Reason.FRAGMENT, "规则实例缺少 substitution")
        path = tuple(d.path)
        try:
            sub_t = T.term_at(pred, path)
        except IndexError:
            return Rejected(Reason.FRAGMENT, f"路径越界: {path}")
        if not any(_same_subst(s, d.substitution)
                   for s in matches(rule.pattern, sub_t)):
            return Rejected(Reason.FRAGMENT, "给定替换不是该位置的一个匹配")
        inst = P.instantiate(rule.template, d.substitution)
        if T.replace_at(pred, path, inst) is not content:
            return Rejected(Reason.FRAGMENT, "内容不是该实例的结果")
        return _ok(proposal, context, _rule_conditions(rule, d.substitution))


class SubstChecker:
    """代换：前驱中某变量替换为值，纯句法操作。"""
    id = "substitute"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        d = proposal.evidence.payload
        substituted = T.subst(pred, {d.var: d.value})
        if equal(content, substituted) or equal(content, normal_form(substituted)):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "内容与代换结果不符")


class SplitChecker:
    """条件分支切割：内容 ⟺ 前驱 ∧ (¬)条件。"""
    id = "branch.split"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        d = proposal.evidence.payload
        cond = d.condition
        branch = T.not_(cond) if d.negate else cond
        expected = T.mk(S("And"), (pred, branch))
        if content is expected:
            return _ok(proposal, context)
        v = context.decide(T.mk(S("Eq"), (content, expected)))
        if v.is_yes():
            return _ok(proposal, context)
        if v.is_no():
            return Rejected(Reason.FRAGMENT, "内容不是前驱与分支条件的合取")
        return UnknownResult(v.reason, "分支等价判定未决")


def _is_tautology(t) -> bool:
    """句法重言式：析取中出现互补对（`c` 与 `¬c`），或常元真。

    判据在**验证侧**，不靠构造期坍缩（v4 §2.1：项不判定语义；§7.3：
    验证独立于构造）。只认排中律这一条，其余覆盖需真证明。
    """
    if isinstance(t, T.BVal):
        return t.val
    if not (isinstance(t, T.Expr) and t.head.name == "Or"):
        return False
    disjuncts = {a._h for a in t.args}
    return any(isinstance(a, T.Expr) and a.head.name == "Not"
               and a.args[0]._h in disjuncts for a in t.args)


class BranchCoverageChecker:
    """分支覆盖（v4 §8.8）：分支条件之析取是否覆盖父问题。

    只认**句法重言式**——排中律 `c ∨ ¬c`。该判定在此独立完成，不依赖
    `mk` 构造期把互补对坍缩成 `⊤`（v4 §2.1 禁止驻留期判定语义）。非互补的
    覆盖需要真覆盖证明，此处诚实返回未决，不冒充。
    """
    id = "branch.coverage"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        if _is_tautology(content):
            return Accepted()
        return UnknownResult(Reason.FRAGMENT, "覆盖不是句法重言式，需真覆盖证明")


class BranchMergeChecker:
    """分支合并（v4 §8.8）：按情况讨论。

    每支在同一命题 `P` 上给出结论、各支条件之析取覆盖父问题，于是 `P` 在父
    作用域成立；各支开放守卫逐条提升为 `C_i ⇒ G_i`（第 5 条）。

    **边界（必须如实知道）**：分支结论**不能**作为父作用域前提——不变量 8
    「子作用域结论不得反向用于父作用域」由 `commit` 第 2 步强制，所以本步的
    前提只有一条（父作用域里的覆盖结论）。因此「每支确实回答了 P」这一环由
    工作流按**内核记录**核出（`Judgment.scope` / `Judgment.proposition`），
    不是 checker 独立复算的：checker 在此复核的是「前提/载荷/结论三者一致」，
    即覆盖命题等于载荷各支条件之析取（载荷因此被已提交的覆盖结论钉住）、
    各支回答数等于支数、且每一支回答的就是结论 `P`。

    要让该环也由内核独立复核，需要 commit 支持「蕴含引入」（由 Γ,C ⊢ P 得
    Γ ⊢ C⇒P）这一作用域规则——那是内核新规则，属设计决定，尚未落。
    """
    id = "branch.merge"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        d = proposal.evidence.payload
        coverage = T.or_(*d.conditions)
        if not any(p is coverage for p in proposal.premise_propositions):
            return Rejected(Reason.FRAGMENT, "前提里没有该分支组的覆盖命题")
        if len(d.answers) != len(d.conditions):
            return Rejected(Reason.FRAGMENT,
                            f"分支回答数 {len(d.answers)} 与分支数 "
                            f"{len(d.conditions)} 不符")
        if any(a is not content for a in d.answers):
            return Rejected(Reason.FRAGMENT, "并非每个分支都回答同一命题")
        promoted = tuple(T.implies(c, g)
                         for c, gs in zip(d.conditions, d.guards) for g in gs)
        return Accepted(direct_requirements=tuple(dom_condition(content)) + promoted,
                        reads=context.read_set())


class ConstraintSatisfiedChecker:
    """约束满足（v4 §8.6 + §8.3 候选规格模式）。

    载荷是 `ValuationCheck(constraint, valuation)`。checker 复核两件事：

      1. 结论**确实是**该约束在该赋值下的实例（句法身份，不信任调用方自报）；
      2. 该实例在当前上下文下判零 —— 用独立设施（域标准形 / 恒等判定 / 定义域
         分析），**不重跑求解器**。

    找 valuation 是求解器的活（不可信侧，可以给错候选）；此处只决定「能声称
    什么」。判零在投影外时诚实返回未决。
    """
    id = "constraint.satisfied"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        d = proposal.evidence.payload
        rel = d.constraint.relation
        inst = T.subst(rel, dict(d.valuation))
        if content is not inst:
            return Rejected(Reason.FRAGMENT, "结论不是该约束在该赋值下的实例")
        v = context.decide(inst)
        if v.is_yes():
            return _ok(proposal, context)
        if v.is_no():
            return Rejected(Reason.FRAGMENT, "该赋值下约束不成立")
        return UnknownResult(v.reason, "约束实例判零未决")


CHECKERS = (ClaimChecker, BothSidesChecker, NormalizeChecker,
            RuleInstanceChecker, SubstChecker, SplitChecker,
            BranchCoverageChecker, BranchMergeChecker,
            ConstraintSatisfiedChecker)


def register(store) -> None:
    """把本模块的 checker 注册进账本。**显式调用**，不在 import 期改全局状态。"""
    for cls in CHECKERS:
        ck = cls()
        if ck.id not in store.checkers:
            store.checkers.register(ck.id, ck)
