# -*- coding: utf-8 -*-
"""手动交互扩展（自 cas/session.py 拆出）：子项手术（:set/:rsub/:tree）、
等式双侧操作（:add_both 族）、变形工具箱（:expand/:extract/:separate/
:complete_square）、微积分战术（:subst/:usub/:parts/:fold/:intro_eq/
:solveq/:lhop/:add_sub）。

Mixin：依赖 SessionBase 状态与义务队列；组装见 cas/session.py。
"""

from cas import term as T
from cas import spec as _spec
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify, expand, cost
from cas.rules import Step
from cas.decide import (
    decide as _decide_fn,
    equivalent as _equivalent_fn,
    T3,
)
from cas.session_core import Obligation
from cas.session_cmds import _quotient_cancel, _neg_pow_of


class ManualOpsMixin:
    # ---------------- 方案命令（人机协作：人选方向，机器算） ----------------

    def subst(self, eq_s):
        """换元（手工通道，通用）。

        :subst t=g(x)：把当前式中 g(x) 全部替换为新变量 t（复合键一次替换）；
        当前式若是惰性积分 Integrate(f, x)，同时把被积式与微分元变换到新变量
        （dx 随换元变换：t=g(x) 经主支逆解 x=h(t)，新被积式 = f(h(t))·h'(t)）。
        反向求逆走 solve 通道（spec.inv 驱动，仿射复合主支逆已支持）。
        正确性由用户后续 !verify 微分回验背书。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d as _d
        from cas.solve import solve as _solve

        eq = parse(eq_s)
        if not (isinstance(eq, T.Expr) and eq.head.name == "Eq"):
            return "usage: :subst t=g(x)  (e.g. :subst t=tan(x/2))"
        lhs, rhs = eq.args
        # 惰性积分：积分变量 x 参与方向判定（free_vars 会跳过被 Bound 绑定的 x）
        is_integ = (isinstance(self.current, T.Expr) and self.current.head.name == "Integrate"
                    and len(self.current.args) == 1 and isinstance(self.current.args[0], T.Bound))
        fv = T.free_vars(self.current)
        if is_integ:
            x, body = T.open_bound(self.current.args[0])
            oldvars = fv | {x}
        else:
            oldvars = fv
        # 方向判定：新变量 = 裸符号 + 不在当前式 + 对侧含当前式变量
        if isinstance(lhs, T.Sym) and lhs not in fv and (T.free_vars(rhs) & oldvars):
            newvar, gexpr = lhs, rhs
        elif isinstance(rhs, T.Sym) and rhs not in fv and (T.free_vars(lhs) & oldvars):
            newvar, gexpr = rhs, lhs
        else:
            return "subst: 等式一边必须是当前式中未出现的新变量（裸符号）"
        before = self.current
        # 惰性积分：换元变换被积式与微分元
        if is_integ:
            # t = g(x) -> 解 x = h(t)
            r = _solve(T.plus(gexpr, T.neg(newvar)), x)
            if r.status != "ok" or not r.solutions:
                return (f"subst: 无法对 {to_str(gexpr)} 求逆（solve: {r.note or r.status}）；"
                        "请给出可求逆的换元（spec.inv 主支逆）")
            ht = r.solutions[0]
            new_body = T.subst(body, {x: ht})
            dht = _d(ht, newvar)
            new_int = T.mk(T.S("Integrate"), (T.mk_bound(newvar, simplify(T.times(new_body, dht))),))
            repl = new_int
            note = f"substitution {to_str(gexpr)} = {newvar.name} (dx -> {to_str(dht)} dt)"
        else:
            # 普通表达式：把 g(x) 替换为新变量（复合键一次全部替换）
            repl = T.subst(self.current, {gexpr: newvar})
            note = f"substitution {to_str(gexpr)} -> {newvar.name}"
        self.current = repl
        self._sid += 1
        self.log.append(Step(self._sid, "scheme:subst", (), before, self.current, "YES",
                             cost(self.current) - cost(before), note=note))
        self._remember(self.current)
        return self.current

    def iparts(self, u_s, detail=False):
        """分部积分（人工干预通道）：用户选 u，内核算 dv = 体/u、v = ∫dv、du，
        ∫体 -> u·v − ∫v·du。自动搜索当前式中体被 u 整除的惰性积分子项。

        detail=True 返回 u/dv/du/v 明细文本（教学/检查用）；否则返回新项。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d
        from cas.integrate import integrate as zz_int
        from cas.decide import equivalent
        from cas.errors import PolyError
        from cas.risch import RischUnsupported

        u = self._parse_in(u_s)
        found = None
        for p in T.all_paths(self.current):
            try:
                tgt = T.term_at(self.current, p)
            except IndexError:
                continue
            if not (isinstance(tgt, T.Expr) and tgt.head.name == "Integrate"
                    and len(tgt.args) == 1 and isinstance(tgt.args[0], T.Bound)):
                continue
            b = tgt.args[0]
            x, body = T.open_bound(b)   # de Bruijn 体还原为自由符号才可参与环运算
            if not isinstance(x, T.Sym):
                continue
            q = simplify(T.div(body, u))
            if equivalent(T.times(u, q), body) is not T3.YES:
                continue
            try:
                v, _ok, _m, _prov = zz_int(q, x)
            except (PolyError, RischUnsupported):
                continue
            du = d(u, x)
            cand = T.times(v, du)
            # 常数符号拉出绑定体：∫(-f) = -∫f（线性，generic 安全）。
            # 指针收敛：循环再现的积分名词与链首驻留同一（:intro_eq/:solveq 可命中，
            # 循环检测可行）。不拉出则 -号留在 Bound 内，名词指针分裂。
            flip = False
            if isinstance(cand, T.Expr) and cand.head.name == "Times" \
                    and T.MONE in cand.args:
                rest = T.mk(T.S("Times"),
                            tuple(a for a in cand.args if a is not T.MONE))
                cand = rest
                flip = True
            new_int = T.mk(T.S("Integrate"), (T.mk_bound(x, cand),))
            core = T.times(u, v)
            repl = T.plus(core, new_int) if flip else T.plus(core, T.neg(new_int))
            found = (p, repl,
                     {"u": u, "dv": q, "du": du, "v": v})
            break
        if found is None:
            return f"parts: no inert integral subterm with body divisible by {to_str(u)}"
        p, repl, det = found
        before = self.current
        self.current = T.replace_at(self.current, p, repl)
        self._sid += 1
        self.log.append(Step(
            self._sid, f"scheme:parts[u={to_str(u)}]", p, before, self.current, "YES",
            cost(self.current) - cost(before), note="integration by parts",
        ))
        self._remember(self.current)
        if detail:
            lines = [
                f"u  = {to_str(det['u'])}",
                f"dv = {to_str(det['dv'])} dx",
                f"du = {to_str(det['du'])} dx",
                f"v  = {to_str(det['v'])}",
                f"=> {to_str(self.current)}",
            ]
            hint = self._named_loop(self.current)
            if hint:
                lines.append(f"[loop] {hint} recurs - extract equation: "
                             f":intro_eq {hint}, then :solveq {hint}")
            return "\n".join(lines)
        return self.current

    def _named_loop(self, t):
        """循环检测：t 中是否指针再现某个已命名的惰性积分名词 -> 名字或 None。

        驻留使指针判等 O(1)；iparts 的符号拉出保证循环再现时名词同一。
        """
        named = [(name, body) for name, (params, body) in self.defs.items()
                 if not params and isinstance(body, T.Expr)
                 and body.head.name == "Integrate"]
        if not named:
            return None
        stack = [t]
        while stack:
            u = stack.pop()
            for name, body in named:
                if u is body:
                    return name
            if isinstance(u, T.Expr):
                stack.extend(u.args)
            elif isinstance(u, T.Bound):
                stack.append(u.body)
        return None

    def fold(self):
        """:fold：线性折叠——current 中与已命名惰性积分体成数值常数倍的名词，
        改写为 常数·命名名词（∫c·g = c·∫g，线性 generic 安全）。

        用途：倍数/负号起点的循环。I := ∫-f 时循环再现的是 ∫f = -I，
        指针天然不同一；fold 用线性性归一后 :intro_eq/:solveq 的循环消解
        才能命中。这是通用机制（常数倍关系判定），不是针对特定例子的特化。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from fractions import Fraction

        named = [(name, body) for name, (params, body) in self.defs.items()
                 if not params and isinstance(body, T.Expr)
                 and body.head.name == "Integrate"]
        if not named:
            return "fold: no named inert integrals (:name := integrate(...))"
        cur = self.current
        repls = []   # (path, 命名名词体, 倍数)
        seen_nouns = set()
        for p in list(T.all_paths(cur)):
            try:
                sub = T.term_at(cur, p)
            except IndexError:
                continue
            if not (isinstance(sub, T.Expr) and sub.head.name == "Integrate"
                    and len(sub.args) == 1 and isinstance(sub.args[0], T.Bound)):
                continue
            if sub._h in seen_nouns:
                continue
            seen_nouns.add(sub._h)
            xv, body_n = T.open_bound(sub.args[0])
            for name, body in named:
                if body is sub:
                    break   # 已是命名名词本身
                xb, body_o = T.open_bound(body.args[0])
                if xv is not xb:
                    continue
                q = _quotient_cancel(body_n, body_o)
                if T.is_num(q):
                    c = T.num_val(q)
                    if c != 0:
                        repls.append((p, body, c))
                        break
        if not repls:
            return f"{to_str(cur)}   [fold: no constant-multiple integrals]"
        # 内层路径先替换（嵌套名词时外层路径索引不变）
        for p, body, c in sorted(repls, key=lambda r: -len(r[0])):
            cur = T.replace_at(cur, p, T.times(T.N(c), body))
        before = self.current
        self.current = simplify(cur)
        if self.current is before:
            return f"{to_str(before)}   [fold: no change]"
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:fold", (), before, self.current, "YES",
            cost(self.current) - cost(before),
            note=f"linearity fold of {len(repls)} integral(s)",
        ))
        self._remember(self.current)
        out = to_str(self.current)
        hint = self._named_loop(self.current)
        if hint:
            out += f"\n[loop] {hint} recurs - extract equation: :intro_eq {hint}, then :solveq {hint}"
        return out

    def add_sub(self, t_s):
        """:add_sub <t>：加零凑形 A -> A + t - t（表达式层借用形战术）。

        结构保真：t 以 quote 包裹、和式走纯驻留构造（_intern_expr）——
        否则 mk 的同类项归并当场消掉 +t-t，等式塌成 A=A。
        t 的定义域照常闸门并创建义务：后续 :intro_eq 提取等式时，
        该守卫必须先行结算（硬闸门）——机器知道的守卫不允许蒸发。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        if isinstance(self.current, T.Expr) and self.current.head.name == "Eq":
            return "add_sub: current is an equation (use :add_both/:sub_both)"
        t = parse(t_s.strip())
        provs, err = self._term_domain_gate(t, f"borrowing {to_str(t)}")
        if err:
            return err
        qt = T.quote(t)
        nq = T._intern_expr(T.S("Times"), (T.MONE, qt))
        before = self.current
        new = T._intern_expr(T.S("Plus"), (before, qt, nq))
        self.current = new
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:add_sub", (), before, new, "YES",
            cost(new) - cost(before),
            note=f"added and subtracted {to_str(t)} (borrowed form)",
        ))
        self._remember(new)
        out = to_str(new)
        return out + self._proviso_suffix(provs)

    def intro_eq(self, lhs_s):
        """:intro_eq <lhs|%N>：等式链提取——把当前式声明为 Eq(lhs, current)。

        计算即等式链：step log 每步的 before->after 都是一条等式；本命令把
        链上节点显式提取为一等方程（循环分部的 I = A - I）。

        守卫结算（硬闸门）：派生等式的守卫 = 链上所有步骤条件的合取。
        规则 guard 已在 commit 时入账本；开放义务（域条件等）未决时拒绝
        建立等式——机器知道的守卫不允许蒸发。先 :ans 作答使条件入账，
        再重试。手写方程（feed 层）不受此限：断言自由但由断言者担责。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        if isinstance(self.current, T.Expr) and self.current.head.name == "Eq":
            return "intro_eq: current is already an equation"
        if self.obligations:
            gs = "; ".join(f"#{o.oid} {to_str(o.question)}" for o in self.obligations)
            return (f"intro_eq refused: derivation chain has open guards ({gs}) - "
                    f"the equation holds only under them. Resolve with "
                    f":ans <oid> <fact> first, then retry.")
        lhs = self._expand_defs(parse(lhs_s.strip()), bare_ok=True)
        # 纯驻留构造：mk 会把 current 中的借用形（'t - 't）当场归并塌掉，
        # 等式将失去其守卫载体——Eq 必须原样保结构
        eq = T._intern_expr(T.S("Eq"), (lhs, self.current))
        before = self.current
        self.current = eq
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:intro_eq", (), before, eq, "YES",
            cost(eq) - cost(before),
            note=f"chain equation: {to_str(lhs)} = current",
        ))
        self._remember(eq)
        return to_str(eq)

    def solveq(self, unknown_s):
        """把当前等式当线性方程解出指定未知项（未知 → z 提系数）。

        eˣsin x 消循环的关键步：I = A − I -> I = A/2。
        """
        self._check_locked()
        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Eq"):
            return "solveq: current must be an equation"
        from cas.solve import _linear_split, _free

        unknown = self._parse_in(unknown_s)
        # 裸符号且是变量定义 -> 解析为宏体（:solveq I 直接按名字解循环方程）
        if isinstance(unknown, T.Sym) and unknown.name in self.defs \
                and self.defs[unknown.name][0] == ():
            unknown = self.defs[unknown.name][1]
        z = T.S("_solveq_z")
        f = T.subst(T.plus(self.current.args[0], T.neg(self.current.args[1])), {unknown: z})
        f = simplify(expand(f))   # 负号分配/同类项归并（与 solve 同款预处理）
        if z not in T.free_vars(f):
            return "solveq: unknown not found in equation"
        lin = _linear_split(f, z)
        if lin is None:
            return "solveq: only linear equations supported"
        a, b = lin
        if not (_free(a, z) and _free(b, z)):
            return "solveq: only linear equations supported"
        if a is T.ZERO:
            return "solveq: unknown cancels out"
        sol = simplify(T.div(T.neg(b), a))
        before = self.current
        self.current = sol
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:solveq", (), before, sol, "YES",
            cost(sol) - cost(before), note=f"solved linear equation for {to_str(unknown)}",
        ))
        self._remember(sol)
        if not T.is_num(a):
            return f"{to_str(sol)}   [proviso: {to_str(T.mk(T.S('Ne'), (a, T.ZERO)))}]"
        return sol

    # ---------------- 手动交互扩展：子项手术 / 等式代数 / 变形工具箱 / 微积分战术 ----------------

    def tree(self):
        """:tree：带路径的子项树（只读）。path 寻址命令的可视化选择器。"""
        if self.current is None:
            return "empty session"
        out = []
        stack = [(self.current, ())]
        while stack:
            t, p = stack.pop()
            out.append((p, t))
            if isinstance(t, T.Expr):
                for i, a in enumerate(t.args):
                    stack.append((a, p + (i,)))
            elif isinstance(t, T.Bound):
                stack.append((t.body, p + (0,)))
        lines = []
        for p, t in sorted(out, key=lambda pt: pt[0]):
            ps = ".".join(str(i) for i in p) or "()"
            lines.append(f"{ps:12s}{'  ' * len(p)}{to_str(t)}")
        return "\n".join(lines)

    def _resolve_target(self, path_s):
        """可选 path 参数 -> (子项, path, None)；path_s 为空取当前式。出错返回错误文本。"""
        if self.current is None:
            return None, None, "empty session"
        if not path_s:
            return self.current, (), None
        try:
            path = tuple(int(i) for i in str(path_s).split("."))
            sub = T.term_at(self.current, path)
        except (ValueError, IndexError):
            return None, None, f"no subterm at path {path_s}"
        return sub, path, None

    @staticmethod
    def _eqv_tag(eqv):
        """equivalent 提交态标注（YES->VERIFIED / PROBABLE；UNKNOWN/NO 由调用方拒绝）。"""
        return {T3.YES: "VERIFIED", T3.PROBABLE: "PROBABLE"}.get(eqv, "UNVERIFIED")

    def _new_domain_conditions(self, old, new):
        """new 相对 old 新引入的定义域约束（:set/:rsub 换入项的域收窄检测）。

        公共域采样只在重叠域上比对等价——换入定义域更窄的项会静默收窄表达式
        的定义范围。恒真约束（decide=YES，如偶次幂非负公理）与 old 已携带的
        约束跳过；其余作为 proviso 显式记账。
        """
        from cas.domain import dom_condition

        old_list = list(dom_condition(old))
        out = []
        for c in dom_condition(new):
            if _decide_fn(c, self.ctx) is T3.YES:
                continue
            if any(c is o for o in old_list):
                continue
            if not any(c is p for p in out):
                out.append(c)
                self._oid += 1
                self.obligations.append(Obligation(
                    self._oid, c, [self._sid + 1],
                    note="domain condition introduced by replacement",
                ))
        return out

    def set_at(self, path_s, expr_s):
        """        :set <path> <expr>：直接子项手术。

        equivalent(旧子项, 新子项) 三态闸门：YES->提交标 VERIFIED /
        PROBABLE->提交标 PROBABLE；UNKNOWN 拒绝（不可验证的篡改不放行——
        先 :assume 事实或定义规则再重试）；NO 拒绝。永不静默错。
        """
        self._check_locked()
        old, path, err = self._resolve_target(path_s)
        if err:
            return err
        new = self._parse_in(expr_s)
        if old is new:
            return "set: replacement identical"
        eqv = _equivalent_fn(old, new, self.ctx)
        if eqv is T3.NO:
            return f"set refused: {to_str(old)} and {to_str(new)} are not equivalent"
        if eqv is T3.UNKNOWN:
            return (f"set refused: cannot verify {to_str(old)} ~ {to_str(new)} "
                    "(UNKNOWN); :assume the fact or define a rule, then retry")
        tag = self._eqv_tag(eqv)
        provs = self._new_domain_conditions(old, new)
        before = self.current
        self.current = T.replace_at(self.current, path, new)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:set", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=f"subterm replace [{tag}]",
        ))
        self._remember(self.current)
        out = to_str(self.current)
        if tag != "VERIFIED":
            out += f"   [{tag}]"
        return out + self._proviso_suffix(provs)

    def rsub(self, s):
        """        :rsub <old>=<new>：全式结构替换（T.subst 复合键一次命中）。

        equivalent 三态闸门同 :set（YES/PROBABLE 提交，UNKNOWN/NO 拒绝）；
        old 未出现则报 not found。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        if "=" not in s:
            return "usage: :rsub <old>=<new>"
        olds, news = s.split("=", 1)
        old = self._parse_in(olds.strip())
        new = self._parse_in(news.strip())
        nxt = T.subst(self.current, {old: new})
        if nxt is self.current:
            return f"rsub: {to_str(old)} not found in current expression"
        eqv = _equivalent_fn(old, new, self.ctx)
        if eqv is T3.NO:
            return f"rsub refused: {to_str(old)} and {to_str(new)} are not equivalent"
        if eqv is T3.UNKNOWN:
            return (f"rsub refused: cannot verify {to_str(old)} ~ {to_str(new)} "
                    "(UNKNOWN); :assume the fact or define a rule, then retry")
        tag = self._eqv_tag(eqv)
        provs = self._new_domain_conditions(old, new)
        before = self.current
        self.current = nxt
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:rsub", (), before, self.current, "YES",
            cost(self.current) - cost(before),
            note=f"replace {to_str(old)} -> {to_str(new)} [{tag}]",
        ))
        self._remember(self.current)
        out = to_str(self.current)
        if tag != "VERIFIED":
            out += f"   [{tag}]"
        return out + self._proviso_suffix(provs)

    # 等式双侧操作（Maxima eqnflag / Mathematica 等式算术的显式命令化；
    # mk 保持纯规范化纪律，不引入隐式线程化）

    def _require_eq(self):
        """等式命令前置检查 -> (lhs, rhs, None) 或 (None, None, 错误文本)。"""
        if self.current is None:
            return None, None, "empty session"
        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Eq"):
            return None, None, "current must be an equation (L = R)"
        return self.current.args[0], self.current.args[1], None

    def _commit_eq(self, new_eq, note):
        before = self.current
        self.current = new_eq
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:eq", (), before, self.current, "YES",
            cost(self.current) - cost(before), note=note,
        ))
        self._remember(self.current)
        return to_str(self.current)

    @staticmethod
    def _proviso_suffix(provs):
        if not provs:
            return ""
        return "   [proviso: " + " && ".join(to_str(c) for c in provs) + "]"

    def _term_domain_gate(self, t, what):
        """操作数 t 的定义域三态闸门 -> (provisos, None) 或 (None, 错误文本)。

        等式双侧操作引入的项必须在解点有定义，否则解集被静默收窄
        （借用形 +ln(x-k)-ln(x-k) 类操作的核心风险）。NO 拒绝（与账本矛盾，
        ex falso 纪律）/ UNKNOWN 记 proviso 并创建义务（条件显式在案，
        可 :ans 作答——守卫不静默丢失）。
        """
        from cas.domain import dom_condition

        provs = []
        for c in dom_condition(t):
            r = _decide_fn(c, self.ctx)
            if r is T3.NO:
                return None, f"domain empty: {what} requires {to_str(c)} (contradicted)"
            if r is T3.UNKNOWN and not any(c is p for p in provs):
                provs.append(c)
                self._oid += 1
                self.obligations.append(Obligation(
                    self._oid, c, [self._sid + 1],
                    note=f"domain condition of {what}",
                ))
        return provs, None

    def eq_add_both(self, t_s):
        """:add_both <t>：两边加 t。群运算安全，但 t 的定义域约束照常闸门
        （加一个 ln(x-k) 会把解集收窄到 x>k——必须显式记账，绝不静默）。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(t, f"adding {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.plus(L, t), T.plus(R, t))),
            f"added {to_str(t)} to both sides")
        return out + self._proviso_suffix(provs)

    def eq_sub_both(self, t_s):
        """:sub_both <t>：两边减 t（移项 = sub_both + 归一）。域闸门同 add_both。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(t, f"subtracting {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.plus(L, T.neg(t)), T.plus(R, T.neg(t)))),
            f"subtracted {to_str(t)} from both sides")
        return out + self._proviso_suffix(provs)

    def eq_mul_both(self, t_s):
        """:mul_both <t>：两边乘 t。正向蕴含恒成立，t 的定义域约束照常闸门
        （乘一个未定义项使两侧无定义；反向需 t!=0，由求解端回验负责）。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(t, f"multiplying by {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.times(L, t), T.times(R, t))),
            f"multiplied both sides by {to_str(t)}")
        return out + self._proviso_suffix(provs)

    def eq_div_both(self, t_s):
        """:div_both <t>：两边除 t。域闸门三态（含 t!=0 与 t 自身定义域）：
        NO 拒绝（域空）/ UNKNOWN 记 proviso / YES 无条件。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        t = self._parse_in(t_s)
        provs, err = self._term_domain_gate(T.div(T.ONE, t),
                                            f"dividing by {to_str(t)}")
        if err:
            return err
        out = self._commit_eq(
            T.mk(T.S("Eq"), (T.div(L, t), T.div(R, t))),
            f"divided both sides by {to_str(t)}")
        return out + self._proviso_suffix(provs)

    def eq_neg_both(self):
        """:neg_both：两边取负。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        return self._commit_eq(
            T.mk(T.S("Eq"), (T.neg(L), T.neg(R))), "negated both sides")

    def eq_swap(self):
        """:swap：交换等式两侧。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        return self._commit_eq(T.mk(T.S("Eq"), (R, L)), "swapped sides")

    def eq_zero_form(self):
        """:zero_form：L = R -> L - R = 0（喂给 !solveineq/Sturm 前的规范形）。"""
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        z = simplify(T.plus(L, T.neg(R)))
        return self._commit_eq(T.mk(T.S("Eq"), (z, T.ZERO)), "moved to zero form")

    def eq_apply_both(self, name_s):
        """:apply_both <fn>：对等式两边应用一元函数。

        域闸门：f(L)/f(R) 的 dom_condition 逐个 decide（NO 拒绝 / UNKNOWN 记 proviso）。
        单射性读 spec.injective 声明：False 提示"仅正向蕴含，后续解须回验"；
        None 提示未声明。sqrt 特例直写 Power(1/2)。
        """
        self._check_locked()
        L, R, err = self._require_eq()
        if err:
            return err
        name = name_s.strip()
        if name == "sqrt":
            fL, fR, inj = T.sqrt(L), T.sqrt(R), None
        else:
            sp = _spec.get(name) or _spec.get(name[0].upper() + name[1:] if len(name) > 1 else name)
            if sp is None or sp.arity != 1:
                return f"apply_both: unknown unary function {name}"
            head = T.S(sp.name)
            fL, fR, inj = T.mk(head, (L,)), T.mk(head, (R,)), sp.injective
        from cas.domain import dom_condition

        provs = []
        for side in (fL, fR):
            for c in dom_condition(side):
                r = _decide_fn(c, self.ctx)
                if r is T3.NO:
                    return f"domain empty: applying {name} requires {to_str(c)} (contradicted)"
                if r is T3.UNKNOWN and not any(c is p for p in provs):
                    provs.append(c)
                    self._oid += 1
                    self.obligations.append(Obligation(
                        self._oid, c, [self._sid + 1],
                        note=f"domain condition of applying {name}",
                    ))
        notes = []
        if inj is False:
            notes.append(f"{name} is not injective: forward implication only, "
                         "later solutions must be re-verified")
        elif inj is None:
            notes.append(f"injectivity of {name} undeclared: proceed with care")
        out = self._commit_eq(T.mk(T.S("Eq"), (fL, fR)), f"applied {name} to both sides")
        out += self._proviso_suffix(provs)
        if notes:
            out += "   [note: " + "; ".join(notes) + "]"
        return out

    # 变形工具箱（反向化简/凑形；ops 层为主实现，命令为薄封装）

    def _reshape_drive(self, name, fn, path_s, args=()):
        """变形命令统一驱动。

        解析目标（可选 path）-> fn(子项, *args) -> (新项, None) 或 (None, 错误文本)。
        目标为等式且未给 path 时对两侧分别应用（Mathematica 等式线程语义），
        任一侧失败即整体拒绝（永不半改）。有变化才提交 scheme:<name> 步。
        """
        self._check_locked()
        sub, path, err = self._resolve_target(path_s)
        if err:
            return err
        if isinstance(sub, T.Expr) and sub.head.name == "Eq" and not path_s:
            targets = [(sub.args[0], path + (0,)), (sub.args[1], path + (1,))]
        else:
            targets = [(sub, path)]
        before = self.current
        cur = self.current
        changed = False
        for tsub, tpath in targets:
            res, msg = fn(tsub, *args)
            if msg:
                return msg
            if res is not tsub:
                cur = T.replace_at(cur, tpath, res)
                changed = True
        if not changed:
            return f"{to_str(before)}   [{name}: no change]"
        self.current = cur
        self._sid += 1
        self.log.append(Step(
            self._sid, f"scheme:{name}", tuple(path), before, cur, "YES",
            cost(cur) - cost(before), note=name,
        ))
        self._remember(cur)
        return to_str(cur)

    def expand_at(self, path_s=None):
        """:expand [path]：展开乘积/幂（暴露 simplify.expand）；等式作用两侧。"""
        return self._reshape_drive("expand", lambda t: (expand(t), None), path_s)

    def extract(self, f_s, path_s=None):
        """:extract <f> [path]：提公因子 ab+ac -> a(b+c)。

        逐项整除（每项经 mk 消去同名因子，负幂残留 = 不可整除的诚实信号），
        以 f·Σq_i 重组；equivalent=YES 背书。仅对和式目标有意义。
        """
        f = self._parse_in(f_s)

        def fn(t):
            if not (isinstance(t, T.Expr) and t.head.name == "Plus"):
                return None, f"extract: {to_str(t)} is not a sum (nothing to factor out of)"
            qs = []
            for a in t.args:
                qa = simplify(T.div(a, f))
                if _neg_pow_of(qa, f):
                    return None, (f"extract refused: {to_str(f)} is not "
                                  f"a common factor of {to_str(t)}")
                qs.append(qa)
            res = T.times(f, T.mk(T.S("Plus"), tuple(qs)))
            if res is t:
                return t, None
            # 构造本身 = 分配律逆（结构可靠），验证接受 PROBABLE
            # （超越因子如 ln(x-k) 的等价判定采样最高只到 PROBABLE）
            if _equivalent_fn(res, t, self.ctx) not in (T3.YES, T3.PROBABLE):
                return None, "extract refused: verification failed"
            return res, None

        return self._reshape_drive("extract", fn, path_s)

    def separate_at(self, path_s=None):
        """:separate [path]：(a+b)/c -> a/c + b/c（ops.separate；:together 的对偶）。"""
        from cas.ops import separate

        return self._reshape_drive("separate", lambda t: (separate(t), None), path_s)

    def complete_square(self, var_s, path_s=None):
        """:complete_square <var> [path]：二次型配方 a x^2+b x+c -> a(x+h)^2+k。

        系数经 ops.coefficient 提取（非多项式诚实拒绝）；该侧无 x^2 项视为
        无变化（等式另一侧可独立配方）；结果构造后 equivalent 背书。
        """
        from cas.ops import coefficient
        from cas.errors import PolyError

        x = T.S(var_s)

        def fn(t):
            try:
                a = coefficient(t, x, 2)
                b = coefficient(t, x, 1)
                c = coefficient(t, x, 0)
            except PolyError:
                return None, f"complete_square: {to_str(t)} is not polynomial in {var_s}"
            if T.is_num(a) and T.num_val(a) == 0:
                return t, None
            h = simplify(T.div(b, T.times(T.N(2), a)))
            k = simplify(T.plus(c, T.neg(T.div(T.pw(b, T.N(2)), T.times(T.N(4), a)))))
            res = T.plus(T.times(a, T.pw(T.plus(x, h), T.N(2))), k)
            if _equivalent_fn(res, t, self.ctx) is T3.NO:
                return None, "complete_square: internal verification failed (refused)"
            return res, None

        return self._reshape_drive("complete_square", fn, path_s)

    # 微积分战术补全

    def usub(self, eq_s):
        """:usub t=g(x)：正向换元（当前式须为惰性积分）。

        两级策略：
        ① 精确微分分解：body/g'(x) 把 g(x)->t 代入后无 x -> 干净换元 ∫f(t)dt
          （defint_auto 的探测逻辑人选版，避免逆函数路线的丑陋形态）；
        ② 退化：主支逆路线 x=h(t) 全代入（与 :subst 同款语义）。
        正确性由用户后续 !verify 微分回验背书。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d as _d
        from cas.solve import solve as _solve

        eq = parse(eq_s)
        if not (isinstance(eq, T.Expr) and eq.head.name == "Eq"):
            return "usage: :usub t=g(x)  (current must be an inert integral)"
        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Integrate"
                and len(self.current.args) == 1 and isinstance(self.current.args[0], T.Bound)):
            return "usub: current must be an inert integral (integrate(f, x))"
        lhs, rhs = eq.args
        x, body = T.open_bound(self.current.args[0])
        fv = T.free_vars(body) | {x}
        if isinstance(lhs, T.Sym) and lhs not in fv and (T.free_vars(rhs) & fv):
            newvar, gexpr = lhs, rhs
        elif isinstance(rhs, T.Sym) and rhs not in fv and (T.free_vars(lhs) & fv):
            newvar, gexpr = rhs, lhs
        else:
            return "usub: 等式一边必须是当前式中未出现的新变量（裸符号）"
        before = self.current
        gp = _d(gexpr, x)
        # 一级：精确微分分解（顶层因子消去——mk 不拆 (a*b)^-1，直接 div 会留残渣）
        q = _quotient_cancel(body, gp)
        q2 = T.subst(q, {gexpr: newvar})
        if x not in T.free_vars(q2):
            new_int = T.mk(T.S("Integrate"), (T.mk_bound(newvar, q2),))
            note = f"u-substitution {to_str(gexpr)} = {newvar.name} (exact differential)"
        else:
            # 二级：主支逆路线
            r = _solve(T.plus(gexpr, T.neg(newvar)), x)
            if r.status != "ok" or not r.solutions:
                return (f"usub: neither exact differential nor invertible substitution "
                        f"({to_str(gexpr)} = {newvar.name}; solve: {r.note or r.status})")
            ht = r.solutions[0]
            nb = T.subst(body, {x: ht})
            dht = _d(ht, newvar)
            new_int = T.mk(T.S("Integrate"),
                           (T.mk_bound(newvar, simplify(T.times(nb, dht))),))
            note = (f"u-substitution {to_str(gexpr)} = {newvar.name} "
                    f"(inverse route x = {to_str(ht)})")
        self.current = new_int
        self._sid += 1
        self.log.append(Step(self._sid, "scheme:usub", (), before, self.current, "YES",
                             cost(self.current) - cost(before), note=note))
        self._remember(self.current)
        return self.current

    def lhop(self, var_s, point_s):
        """:lhop <var> <point>：手动洛必达一步。

        当前式经 num_den 提取分子分母，在 point 处须为 0/0 或 ±∞/±∞ 不定形
        （limits.limit 判定），否则诚实拒绝并报告两端极限；一步 = D(F)/D(G)。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.ops import num_den
        from cas.limits import limit
        from cas.diff import d as _d

        F, G = num_den(self.current)
        x = T.S(var_s)
        pt = self._parse_bound(point_s)

        def _is_inf(v):
            if v is T.INFINITY:
                return True
            return (isinstance(v, T.Expr) and v.head.name == "Times"
                    and any(a is T.INFINITY for a in v.args))

        lf = limit(F, x, pt)
        lg = limit(G, x, pt)
        zero_zero = lf is T.ZERO and lg is T.ZERO
        inf_inf = _is_inf(lf) and _is_inf(lg)
        if not (zero_zero or inf_inf):
            fmt = lambda v: to_str(v) if v is not None else "UNKNOWN"
            return (f"lhop: not an indeterminate form at {point_s} "
                    f"(numerator -> {fmt(lf)}, denominator -> {fmt(lg)})")
        nf = _d(F, x)
        ng = _d(G, x)
        before = self.current
        self.current = T.div(nf, ng)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:lhop", (), before, self.current, "YES",
            cost(self.current) - cost(before),
            note="l'Hopital 0/0" if zero_zero else "l'Hopital inf/inf",
        ))
        self._remember(self.current)
        return self.current
