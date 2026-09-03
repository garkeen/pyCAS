# -*- coding: utf-8 -*-
"""工作流引擎：步骤 DAG + 带类型推导边 + 守卫传播。

步骤不是等式链条——步骤间的逻辑关系由推导类型（derivation）决定：
rewrite 是等价，both-sides 可逆时是等价、不可逆时是蕴含，solve 是
"解集等价"，split 是析取。验证器按推导类型分派到域判定器。

验证独立性（架构总纲条款）：验证器不重跑求解算法。
· Solve：求解器输出解，验证器只做回代判官（代入 + 域标准形判零）
· Diff ：项层微分的结果由域层导数（独立实现）交叉验证
· 规则重写：信任锚是图书馆准入纪律，验证器复核匹配产物

逻辑层 = 命题复合（and3/or3）+ 域特定可判定原子（domain.equal/
decide/dom_condition）。不含运行时量词推理——全称事实是图书馆
引理，按模式匹配实例化。

守卫条件：步骤创建时自动从内容经 dom_condition 提取定义域约束，
存入步骤载荷；BothSides 传播前驱守卫 + 运算元守卫；mul/div 额外
要求运算元 ≠ 0，由 decide 在已积累守卫的上下文中检查。守卫按指针
去重；Split 分支上被切割的条件从守卫中清偿。

域归属：步骤创建时经投影层（cas/project）成员测试记录所属域——
域由投影赋予，不做叶嗅探。
"""

from dataclasses import dataclass

from cas import term as T
from cas.term import Expr, Sym, S, N
from cas.verdict import YES, NO, unknown
from cas.domains.poly import Poly, p_deriv, to_term
from cas.domains.ratfunc import RatFunc, rf_deriv, rf_to_term
from cas.domcond import dom_condition
from cas.context import Context
from cas.decide import decide
from cas.judge import back_substitute
from cas.qarith import fold
from cas.project import project, zero_of, normalize as proj_normalize


# ---------------------------------------------------------------------------
# 推导类型：封闭 ADT 层次
# ---------------------------------------------------------------------------

class Derivation:
    """推导类型。每种类型自带验证规则，分派到域判定器 + 命题复合。"""
    pass


@dataclass(frozen=True, slots=True)
class Claim(Derivation):
    """断言入账——无前驱，守卫自动提取。逻辑地位：假设。"""
    pass


@dataclass(frozen=True, slots=True)
class BothSides(Derivation):
    """等式两边同施加运算。
    可逆（add/sub/mul by ≠0/div by ≠0）⟺ 等价；
    不可逆（mul by 0）⟹ 蕴含且信息丢失。"""
    pred: int              # 前驱步骤 id
    op: str                # "add" | "sub" | "mul" | "div"
    operand: object        # 运算元（Term）


@dataclass(frozen=True, slots=True)
class Rewrite(Derivation):
    """重写——域标准形（rule=""）或图书馆规则应用（rule=规则 id）。"""
    pred: int
    rule: str = ""


@dataclass(frozen=True, slots=True)
class Solve(Derivation):
    """输入等式输出解。逻辑地位：解集等价（完备时 ⟺）。

    solution 是求解器交出的证书；验证器只做回代判官，不重跑求解。"""
    pred: int
    var: Sym
    solution: object       # Term（解的值）


@dataclass(frozen=True, slots=True)
class Split(Derivation):
    """条件分支切割——一步析取为两步（condition 与 ¬condition）。
    negate=False 是条件成立分支，negate=True 是否定分支。
    排中律保证两支覆盖全空间。"""
    pred: int
    condition: object      # 切割条件（Term）
    negate: bool = False


@dataclass(frozen=True, slots=True)
class Subst(Derivation):
    """代换——前驱中某变量替换为值，纯句法操作。蕴含。"""
    pred: int
    var: Sym
    value: object           # Term


@dataclass(frozen=True, slots=True)
class Diff(Derivation):
    """对前驱表达式求导。

    等式不是合法输入：等式两边求导不保真（点解方程 x=3 会"推出" 1=0），
    验证器对标 dead。隐函数求导是带依赖声明的独立命令（未建）。"""
    pred: int
    var: Sym


@dataclass(frozen=True, slots=True)
class Integrate(Derivation):
    """积分——前驱被积式关于 var 求原函数（antideriv），或定积分（bounds=(a,b)）。

    逻辑地位：不定为"原函数等式"，定为"积分值等式"。验证器独立于积分器：
    用微分层复核 d/dx antideriv == 被积式，定积分再核 值 == antideriv(b)−antideriv(a)。"""
    pred: int
    var: Sym
    antideriv: object          # 声称的原函数（Wit 证书）
    bounds: tuple = None       # (a, b) 项 | None=不定


# ---------------------------------------------------------------------------
# 步骤：不可变记录
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Step:
    id: int
    content: object        # Term（等式 / 表达式 / 不等式）
    derivation: Derivation
    guards: tuple          # (Term, ...) 守卫条件（已清偿的不在内）
    status: str = "open"   # "open" | "dead"
    note: str = ""
    target: tuple = ()     # 操作对象路径（架构 2.3 步骤七字段之 target）
    reads: tuple = ()      # 本步读取/咨询过的条件
    clears: tuple = ()     # 本步清偿的未确认条件
    domain: str = ""       # 内容所属域（投影赋予）


# ---------------------------------------------------------------------------
# 工作流
# ---------------------------------------------------------------------------

class Workflow:
    """步骤 DAG + 验证器。

    步骤创建时自动提取守卫、验证推导合理性。验证失败标 dead；
    前驱 dead 的步骤沿依赖边级联 dead。步骤引用前驱用 id
    （不可变 DAG），不持 Python 对象引用。
    """

    def __init__(self):
        self._steps: dict[int, Step] = {}
        self._next_id = 0
        self._deps: dict[int, list[int]] = {}   # pred id -> [后继 id]

    def get(self, sid: int) -> Step:
        return self._steps[sid]

    def all_steps(self):
        return [self._steps[i] for i in range(self._next_id)]

    def add(self, content, derivation, note="", target=()) -> Step:
        """创建步骤：守卫收集 → 验证 → 域归属 → 存储 → 死步骤级联。"""
        guards, reads, clears = self._collect(content, derivation)
        verdict = self._verify(content, derivation, guards)
        status = "dead" if verdict is NO else "open"
        domain = self._domain_of(content)
        step = Step(id=self._next_id, content=content,
                    derivation=derivation, guards=guards,
                    status=status, note=note, target=tuple(target),
                    reads=reads, clears=clears, domain=domain)
        self._steps[self._next_id] = step
        self._next_id += 1
        pred_id = getattr(derivation, "pred", None)
        if pred_id is not None:
            self._deps.setdefault(pred_id, []).append(step.id)
            if self._steps[pred_id].status == "dead" and step.status == "open":
                self._mark_dead(step.id, "前驱 dead，级联")
        return self._steps[step.id]

    # --- 死步骤级联 ---

    def _mark_dead(self, sid, why):
        s = self._steps[sid]
        self._steps[sid] = Step(s.id, s.content, s.derivation, s.guards,
                                "dead", why, s.target, s.reads, s.clears,
                                s.domain)
        for dep in list(self._deps.get(sid, ())):
            if self._steps[dep].status == "open":
                self._mark_dead(dep, f"依赖 #{sid} dead，级联")

    # --- 域归属（投影赋予，不嗅探）---

    def _domain_of(self, content) -> str:
        t = content
        if _is_eq(content):
            la, ra = content.args
            t = T.plus(la, T.neg(ra))
        hit = project(t)
        return hit.name if hit is not None else ""

    # --- 守卫收集（去重 + 清偿 + 读写清单）---

    def _collect(self, content, derivation):
        guards = []

        def push(gs):
            for g in gs:
                if not any(g is k for k in guards):
                    guards.append(g)

        reads = ()
        clears = ()
        push(dom_condition(content))
        if isinstance(derivation, BothSides):
            pred = self._steps.get(derivation.pred)
            if pred is not None:
                push(pred.guards)
            push(dom_condition(derivation.operand))
            if derivation.op in ("mul", "div"):
                nz = T.mk(S("Ne"), (derivation.operand, T.ZERO))
                push([nz])
                reads = (nz,)
        elif isinstance(derivation, Split):
            pred = self._steps.get(derivation.pred)
            cond = derivation.condition
            if pred is not None:
                # 切割条件在本分支上已被裁决：从开放守卫中清偿
                push([g for g in pred.guards if g is not cond])
            push(dom_condition(cond))
            clears = (cond,)
        elif isinstance(derivation, (Rewrite, Solve, Subst, Diff, Integrate)):
            pred = self._steps.get(derivation.pred)
            if pred is not None:
                push(pred.guards)
            if isinstance(derivation, Subst):
                push(dom_condition(derivation.value))
        return tuple(guards), reads, clears

    # --- 验证 ---

    def _verify(self, content, derivation, guards):
        if isinstance(derivation, Claim):
            return YES
        if isinstance(derivation, BothSides):
            return self._verify_both_sides(content, derivation, guards)
        if isinstance(derivation, Rewrite):
            return self._verify_rewrite(content, derivation)
        if isinstance(derivation, Solve):
            return self._verify_solve(content, derivation)
        if isinstance(derivation, Split):
            return self._verify_split(content, derivation)
        if isinstance(derivation, Subst):
            return self._verify_subst(content, derivation)
        if isinstance(derivation, Diff):
            return self._verify_diff(content, derivation)
        if isinstance(derivation, Integrate):
            return self._verify_integrate(content, derivation)
        return unknown()

    def _verify_both_sides(self, content, d: BothSides, guards):
        pred = self._steps.get(d.pred)
        if pred is None or not _is_eq(pred.content):
            return NO
        lhs, rhs = pred.content.args
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
            return NO
        if not _eq_equal(content, exp):
            return NO
        # 守卫检查：mul/div 要求运算元 ≠ 0（在已积累守卫上下文中判定）
        if op in ("mul", "div"):
            ctx = Context()
            for g in guards:
                ctx.assume(g)
            r = decide(T.mk(S("Ne"), (d.operand, T.ZERO)), ctx)
            if r is NO:
                return NO          # 运算元为零：变换不可逆，标 dead
            # UNKNOWN 允许——守卫未定，步骤 open 但带条件
        return YES

    def _verify_rewrite(self, content, d: Rewrite):
        pred = self._steps.get(d.pred)
        if pred is None:
            return NO
        if d.rule:
            # 图书馆规则重写：复核规则产物（信任锚 = 图书馆准入纪律）
            from cas.rules import library_ruleset, apply_rule
            rule = library_ruleset().rules.get(d.rule)
            if rule is None:
                return NO
            for path in T.all_paths(pred.content):
                res = apply_rule(rule, pred.content, path)
                if res.ok and _eq_equal(content, res.term):
                    return YES
            return NO
        n = _normalize_eq(pred.content)
        if _eq_equal(content, n):
            return YES
        return NO

    def _verify_subst(self, content, d: Subst):
        pred = self._steps.get(d.pred)
        if pred is None:
            return NO
        substituted = T.subst(pred.content, {d.var: d.value})
        if _eq_equal(content, substituted):
            return YES
        n = _normalize_eq(substituted)
        if _eq_equal(content, n):
            return YES
        return NO

    def _verify_solve(self, content, d: Solve):
        """回代判官（cas/judge）：代入证书后域标准形判零。不重跑求解公式。

        代入结果是分段项时先按有序首中点塌缩（数值点至多落一支，
        取值唯一），再对选出的支值判零。判零实现只有一处，本处只做
        分派与 Verdict 组装。"""
        pred = self._steps.get(d.pred)
        if pred is None or not _is_eq(pred.content):
            return NO
        if not (_is_eq(content) and content.args[0] is d.var
                and content.args[1] is d.solution):
            return NO
        z = back_substitute(pred.content, d.var, d.solution).zero
        if z is True:
            return YES
        if z is False:
            return NO
        # 投影落空（如含超越函数的解）：片段外诚实未决，不退化近似
        return unknown()

    def _verify_split(self, content, d: Split):
        """排中律覆盖验证：分支内容 ⟺ 前驱 ∧ (¬)条件。"""
        pred = self._steps.get(d.pred)
        if pred is None:
            return NO
        cond = d.condition
        branch_cond = T.mk(S("Not"), (cond,)) if d.negate else cond
        expected = T.mk(S("And"), (pred.content, branch_cond))
        if content is expected:
            return YES
        return decide(T.mk(S("Eq"), (content, expected)), Context())

    def _verify_diff(self, content, d: Diff):
        """独立交叉验证：域层导数（另一实现）复核项层微分结果。

        等式前驱一律否证（见 Diff 类 docstring）。源在域内（K[x] 或
        K(x)）时用域导数重建期望值，与步骤内容在有理函数域判等；源在
        域外（超越塔未建）时没有独立通道，诚实返回 UNKNOWN（步骤 open，
        非 dead）。"""
        pred = self._steps.get(d.pred)
        if pred is None:
            return NO
        if _is_eq(pred.content):
            return NO
        x = d.var
        src, got = pred.content, content
        if _is_piecewise(src):
            # 分段源：逐支域层交叉验证。分支条件逐对相同（导数分段
            # 沿用原分区）时每个支值独立投影取域导数，与步骤对应支值
            # 在有理函数域判等；NO 只在携带 K(x) 判等证据时给出。
            # 结构不匹配（未分段表示/分支数不同/条件不同）可能是
            # 等价重划——无否证证据，未决（open），不冒充否决。
            # 分段点（点胞腔）的可导性不在本验证器裁决范围（见 REPL
            # 分段求导通道的未验证标注），逐支成立即视为整体验证通过。
            from cas.piecewise import fold_nested, branches
            if not _is_piecewise(got):
                return unknown()
            sbs = branches(fold_nested(src))
            gbs = branches(fold_nested(got))
            if len(sbs) != len(gbs):
                return unknown()
            for (sv, sc), (gv, gc) in zip(sbs, gbs):
                if sc is not gc:
                    return unknown()
                r = self._cross_diff(sv, gv, x)
                if r is None:              # 该支在投影域外：无独立通道
                    return unknown()
                if r is not YES:
                    return r
            return YES
        r = self._cross_diff(src, got, x)
        if r is None:                        # 源在投影域外：无独立通道
            return unknown()
        return r

    def _cross_diff(self, src, got, x):
        """单项交叉验证：域层导数重建期望值 vs 项层结果。

        返回 None 表示源在投影域外（无独立通道，交上层未决）；
        YES 域层重建与项层结果在有理函数域判等；NO 不等；其余为
        判等所需的域上无法完成的诚实未决。"""
        hit = project(src)
        if hit is None:
            return None
        if hit.element is None:
            expected = T.ZERO              # 常数格（ℤ/ℚ）导数为 0
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
        from cas.domains.ratfunc import ratfunc_domain
        allv = tuple(sorted(T.free_vars(expected) | T.free_vars(got),
                            key=lambda s: s.name))
        if not allv:
            return YES if fold(T.plus(expected, T.neg(got))) is T.ZERO else NO
        rfd = ratfunc_domain(*allv)
        if rfd.equal(expected, got) is True:
            return YES
        if rfd.equal(expected, got) is False:
            return NO
        return unknown()

    def _verify_integrate(self, content, d: Integrate):
        """独立复核：d/dx antideriv == 被积式（走微分层，另一套实现）；
        定积分再核 值 == antideriv(b) − antideriv(a)（精确求值）。"""
        pred = self._steps.get(d.pred)
        if pred is None:
            return NO
        f = pred.content
        x = d.var
        G = d.antideriv
        from cas.integrate import verify_antideriv
        from cas.piecewise import is_piecewise
        if not verify_antideriv(G, f, x):
            return NO
        if d.bounds is None:
            want = T.eq(T.mk(S("Integrate"), (T.mk_bound(x, f),)), G)
            return YES if _eq_equal(content, want) else NO
        a_t, b_t = d.bounds
        if is_piecewise(f) or not (T.is_num(a_t) and T.is_num(b_t)):
            # 分段定积分逐段/代数限需额外通道，独立复核未接——诚实未决
            return unknown()
        Fa = fold(T.subst(G, {x: a_t}))
        Fb = fold(T.subst(G, {x: b_t}))
        val = fold(T.plus(Fb, T.neg(Fa)))
        want = T.eq(T.mk(S("DefIntegrate"), (T.mk_bound(x, f), a_t, b_t)), val)
        return YES if _eq_equal(content, want) else NO


# ---------------------------------------------------------------------------
# 谓词助手
# ---------------------------------------------------------------------------

def _is_eq(t) -> bool:
    return isinstance(t, Expr) and t.head.name == "Eq"


def _is_piecewise(t) -> bool:
    from cas.piecewise import is_piecewise
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
        d = T.plus(lhs, T.neg(rhs))
        hit = project(d)
        if hit is not None:
            return T.eq(proj_normalize(hit), T.ZERO)
        return t
    hit = project(t)
    if hit is not None:
        return proj_normalize(hit)
    return t
