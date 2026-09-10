# -*- coding: utf-8 -*-
"""旧验证器的 checker 适配层（v4 §十一 阶段2 的「包裹旧验证器」）。

八个 verifier 从 `workflow.py` 搬到这里，签名改成 v4 §6.7 的 checker 协议：

    check(proposal, context, services) -> CheckResult

两处实质变化（不是换壳）：

1. **不再读工作流内部状态**。原先靠 `self._steps[d.pred].content` 取前驱，
   现在读 `proposal.premise_propositions`——由 `commit` 解析前提后回填，
   checker 不得信任调用方自报。
2. **守卫由 checker 判定并回报**（v4 §6.7「守卫不能只由算法自己声明」）。
   原先 `workflow._collect` 把守卫当字段挂在步骤上，现在 checker 返回
   `Accepted.direct_requirements`，内核据此建 Requirement 并尝试清偿；
   前驱条件的继承也由内核负责，不再逐类型手工 push。

依赖债：本文件仍依赖 cas.math.*（decide/judge/project/domains/integrate）。
这是 v3 遗留的 workflow→math 顶层依赖，v4 §三 的目标位置是各
`math/*/checkers.py`，阶段6 迁移；此处保持原有依赖形状，不新增债务。
"""

from cas.syntax import term as T
from cas.syntax import pattern as P
from cas.syntax.term import Expr, S
from cas.syntax.match import matches
from cas.kernel.evidence import Accepted, Rejected, UnknownResult
from cas.kernel.verdict import Reason
from cas.math.domains.poly import Poly, p_deriv, to_term
from cas.math.domains.ratfunc import RatFunc, rf_deriv, rf_to_term
from cas.math.domcond import dom_condition
from cas.math.judge import back_substitute
from cas.math.qarith import fold
from cas.math.project import project, zero_of, normalize as proj_normalize


# ---------------------------------------------------------------------------
# 谓词与判等助手（原先在 workflow.py，随验证器一并搬来）
# ---------------------------------------------------------------------------

def _is_eq(t) -> bool:
    return isinstance(t, Expr) and t.head.name == "Eq"


def _is_piecewise(t) -> bool:
    from cas.math.piecewise import is_piecewise
    return is_piecewise(t)


def _eq_equal(a, b) -> bool:
    """等式判等：两侧差值经投影判零（K(x) ⊇ K[x] ⊇ ℚ）。"""
    if not _is_eq(a) or not _is_eq(b):
        return a is b
    la, ra = a.args
    lb, rb = b.args
    d = T.plus(T.plus(la, T.neg(ra)), T.neg(T.plus(lb, T.neg(rb))))
    z = zero_of(d)
    if z is True:
        return True
    if z is False:
        return False
    return fold(T.plus(la, T.neg(ra))) is fold(T.plus(lb, T.neg(rb)))


def _normalize_eq(t):
    """等式或表达式的域标准形：投影命中则取域标准形，落空原样返回。"""
    if _is_eq(t):
        lhs, rhs = t.args
        hit = project(T.plus(lhs, T.neg(rhs)))
        if hit is not None:
            return T.eq(proj_normalize(hit), T.ZERO)
        return t
    hit = project(t)
    if hit is not None:
        return proj_normalize(hit)
    return t


def _cross_diff(src, got, x):
    """单项交叉验证：域层导数（另一实现）重建期望值 vs 项层结果。

    None 表示源在投影域外（无独立通道，交上层未决）；YES 域层重建与项层
    结果在有理函数域判等；NO 不等；其余为诚实未决。"""
    hit = project(src)
    if hit is None:
        return None
    if hit.element is None:
        expected = T.ZERO                      # 常数格（ℤ/ℚ）导数为 0
    else:
        vs = hit.domain.vars
        if x not in vs:
            expected = T.ZERO
        else:
            idx = vs.index(x)
            ring = hit.domain.ring
            if isinstance(hit.element, Poly):
                expected = to_term(ring, p_deriv(ring, hit.element, idx))
            elif isinstance(hit.element, RatFunc):
                expected = rf_to_term(ring, rf_deriv(ring, hit.element, idx))
            else:
                return None
    from cas.math.domains.ratfunc import ratfunc_domain
    allv = tuple(sorted(T.free_vars(expected) | T.free_vars(got),
                        key=lambda s: s.name))
    if not allv:
        return True if fold(T.plus(expected, T.neg(got))) is T.ZERO else False
    rfd = ratfunc_domain(*allv)
    if rfd.equal(expected, got) is True:
        return True
    if rfd.equal(expected, got) is False:
        return False
    return None


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
# 八个 checker
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
        if not _eq_equal(content, exp):
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
        if _eq_equal(content, _normalize_eq(pred)):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "内容不是前驱的域标准形")


class RuleInstanceChecker:
    """图书馆规则在 (path, substitution) 处的**一次实例**。

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
        from cas.math.rules import library_ruleset
        rule = library_ruleset().rules.get(d.rule)
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
        if _eq_equal(content, substituted) or _eq_equal(content, _normalize_eq(substituted)):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "内容与代换结果不符")


class SolveChecker:
    """回代判官：代入证书后域标准形判零。**不重跑求解公式**。"""
    id = "solve.back_substitute"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None or not _is_eq(pred):
            return Rejected(Reason.FRAGMENT, "前驱不是等式")
        d = proposal.evidence.payload
        if not (_is_eq(content) and content.args[0] is d.var
                and content.args[1] is d.solution):
            return Rejected(Reason.FRAGMENT, "内容不是该变量等于该解")
        z = back_substitute(pred, d.var, d.solution).zero
        if z is True:
            return _ok(proposal, context)
        if z is False:
            return Rejected(Reason.FRAGMENT, "回代不判零：非解")
        return UnknownResult(Reason.FRAGMENT, "回代判零在投影外，未决")


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


class DiffChecker:
    """独立交叉验证：域层导数（另一实现）复核项层微分结果。

    等式前驱一律否证（等式两边求导不保真）；源在域外时没有独立通道，
    诚实未决——不冒充验证通过。"""
    id = "calculus.derivative"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        if _is_eq(pred):
            return Rejected(Reason.FRAGMENT, "等式前驱不可求导")
        d = proposal.evidence.payload
        x = d.var
        if _is_piecewise(pred):
            from cas.math.piecewise import fold_nested, branches
            if not _is_piecewise(content):
                return UnknownResult(Reason.FRAGMENT, "分段源与非分段结果，无独立通道")
            sbs = branches(fold_nested(pred))
            gbs = branches(fold_nested(content))
            if len(sbs) != len(gbs):
                return UnknownResult(Reason.FRAGMENT, "分支数不同，不冒充否决")
            for (sv, sc), (gv, gc) in zip(sbs, gbs):
                if sc is not gc:
                    return UnknownResult(Reason.FRAGMENT, "分支条件不同")
                r = _cross_diff(sv, gv, x)
                if r is None:
                    return UnknownResult(Reason.FRAGMENT, "该支在投影域外")
                if r is not True:
                    return Rejected(Reason.FRAGMENT, "域层导数与该支不符")
            return _ok(proposal, context)
        r = _cross_diff(pred, content, x)
        if r is None:
            return UnknownResult(Reason.FRAGMENT, "源在投影域外，无独立通道")
        if r is not True:
            return Rejected(Reason.FRAGMENT, "域层导数与项层结果不符")
        return _ok(proposal, context)


class IntegrateChecker:
    """独立复核：d/dx antideriv == 被积式（走微分层，另一套实现）；
    定积分再核 值 == antideriv(b) − antideriv(a)（精确求值）。"""
    id = "calculus.antiderivative"

    def check(self, proposal, context, services):
        content, bad = _one_conclusion(proposal)
        if bad is not None:
            return bad
        pred = _premise(proposal)
        if pred is None:
            return Rejected(Reason.FRAGMENT, "缺前驱")
        d = proposal.evidence.payload
        f, x, G = pred, d.var, d.antideriv
        from cas.math.integrate import verify_antideriv
        if not verify_antideriv(G, f, x):
            return Rejected(Reason.FRAGMENT, "微分层复核不通过")
        if d.bounds is None:
            want = T.eq(T.mk(S("Integrate"), (T.mk_bound(x, f),)), G)
            if _eq_equal(content, want):
                return _ok(proposal, context)
            return Rejected(Reason.FRAGMENT, "内容与原函数等式不符")
        a_t, b_t = d.bounds
        if _is_piecewise(f) or not (T.is_num(a_t) and T.is_num(b_t)):
            return UnknownResult(Reason.FRAGMENT, "分段/代数限定积分独立复核未接")
        Fa = fold(T.subst(G, {x: a_t}))
        Fb = fold(T.subst(G, {x: b_t}))
        val = fold(T.plus(Fb, T.neg(Fa)))
        want = T.eq(T.mk(S("DefIntegrate"), (T.mk_bound(x, f), a_t, b_t)), val)
        if _eq_equal(content, want):
            return _ok(proposal, context)
        return Rejected(Reason.FRAGMENT, "定积分值与端点差不符")


# ---------------------------------------------------------------------------
# 判定服务（工作流侧实现 v4 §6.7 KernelServices）
# ---------------------------------------------------------------------------

class WorkflowServices:
    """把 cas.math.decide 接到内核服务接口上（内核源码不 import 数学模块）。

    作用域假设作为判定上下文——条件清偿因此在正确的分支上下文里进行。
    """

    def __init__(self, scopes):
        self._scopes = scopes

    def decide(self, proposition, scope_id):
        from cas.math.decide import decide as _decide
        from cas.kernel.context import Context
        ctx = Context()
        for a in self._scopes.assumptions(scope_id):
            ctx.assume(a.proposition)
        return _decide(proposition, ctx)


def register(store) -> None:
    """把 checker 注册进账本。**显式调用**，不在 import 期改全局状态。"""
    for ck in (ClaimChecker(), BothSidesChecker(), NormalizeChecker(),
               RuleInstanceChecker(), SubstChecker(), SolveChecker(),
               SplitChecker(), DiffChecker(), IntegrateChecker()):
        if ck.id not in store.checkers:
            store.checkers.register(ck.id, ck)
