# -*- coding: utf-8 -*-
"""会话核心（自 cas/session.py 拆出）：SessionBase——状态、账本交互、
规则应用/自动重写、用户定义展开、历史、撤销/重放。

组装关系：cas/session.py 把本类与 KernelOpsMixin / ManualOpsMixin /
DispatchMixin 合成为 Session；命令 handler 见 cas/session_cmds.py。
"""

import os

from dataclasses import dataclass, field

from cas import term as T
from cas.decide import (
    eval_guard as _eval_guard,
    T3,
)
from cas.context import Context
from cas.parser import parse
from cas.pprint import to_str
from cas.rules import RuleSet, Step, apply_rule
from cas.simplify import simplify, cost
from cas.errors import BudgetExceeded, ParseError
from cas import loader
from cas import spec as _spec
from cas.session_cmds import (
    KernelCmd,
    _k_apart, _k_isteps, _k_bsub, _k_together, _k_collect,
    _k_num_den, _k_mulfrac, _k_coefficient,
    _k_verify, _k_solve, _k_factor, _k_integrate, _k_dsolve,
    _k_limit, _k_series, _k_defint, _k_sum, _k_msolve, _k_gsolve,
    _k_solveineq, _k_solveset,
)


@dataclass
class Obligation:
    oid: int
    question: T.Term
    affects: list
    note: str = ""
    pending: list = field(default_factory=list)


class SessionBase:
    def __init__(self, budget=100000):
        self.current = None
        self.log = []
        self.obligations = []
        self.ctx = Context()
        self.rules = RuleSet()
        self.budget = budget
        self.locked = None
        self.load_error = None
        self.history = []   # 产出过的表达式（%N 复用，REPL 交互标配）
        self.transcript = []  # 命令转录（DSL：可保存/可回放，计算可复现的地基）
        self.defs = {}      # 用户定义：头名/变量名 -> (参数元组, 体)；空参 = 变量
        self._sid = 0
        self._oid = 0
        rules_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
        if os.path.isdir(rules_dir):
            try:
                loader.load_dir(rules_dir, self.rules)
            except Exception as e:
                # 不静默吞错：记录并在 REPL 报告（永不静默错原则）
                self.load_error = f"{e.__class__.__name__}: {e}"
        # FunctionSpec 自动生成的规则（奇偶性等，origin='spec'）
        _spec.gen_rules(self.rules)
        # 手动算法命令（: 前缀；用户主动触发，结果入账可撤销）
        self.kernel = {
            "apart": KernelCmd("apart <num> <den>", _k_apart),
            "isteps": KernelCmd("isteps <expr> [var] (strategy step tree)", _k_isteps),
            "bsub": KernelCmd("backward sub: :bsub x=h(t) <expr> <var> <lo> <hi>", _k_bsub),
            "together": KernelCmd("together <expr> (common denominator)", _k_together),
            "collect": KernelCmd("collect <expr> <var>", _k_collect),
            "numerator": KernelCmd("numerator <expr>", _k_num_den("numerator")),
            "denominator": KernelCmd("denominator <expr>", _k_num_den("denominator")),
            "mulfrac": KernelCmd("mulfrac <expr> <factor> (multiply num&den)", _k_mulfrac("mulfrac")),
            "divfrac": KernelCmd("divfrac <expr> <factor> (divide num&den)", _k_mulfrac("divfrac")),
            "coefficient": KernelCmd("coefficient <expr> <var> [k]", _k_coefficient),
        }
        # 自动求解命令（! 前缀；算法黑盒直出，verify 背书）
        self.solver = {
            "verify": KernelCmd("verify <F> <x> <f>", _k_verify),
            "solve": KernelCmd("solve <expr> [var]", _k_solve),
            "factor": KernelCmd("factor <expr>", _k_factor),
            "integrate": KernelCmd("integrate <expr> [var] (var required for multi-variable expr)", _k_integrate),
            "dsolve": KernelCmd("dsolve <eq with D(y,x)> <y> [x]", _k_dsolve),
            "limit": KernelCmd("limit <expr> <var> <point> (point may be +/-inf)", _k_limit),
            "series": KernelCmd("series <expr> <var> <point> <order> (Taylor + O term)", _k_series),
            "defint": KernelCmd("defint <expr> <var> <lo> <hi>", _k_defint),
            "sum": KernelCmd("sum <expr> <var> [<lo> <hi>] (Faulhaber power sum + diff verify)", _k_sum),
            "mat": KernelCmd("show matrix [[a,b],[c,d]]", lambda s, r: s.mat(r.strip())),
            "mdet": KernelCmd("determinant [[a,b],[c,d]]", lambda s, r: s.mdet(r.strip())),
            "mrank": KernelCmd("rank [[a,b],[c,d]]", lambda s, r: s.mrank(r.strip())),
            "minv": KernelCmd("inverse [[a,b],[c,d]]", lambda s, r: s.minv(r.strip())),
            "msolve": KernelCmd("solve system: !msolve [[a,b],[c,d]] [e,f]", _k_msolve),
            "gsolve": KernelCmd("polynomial system: !gsolve f1 && f2 for x,y (Groebner elimination)", _k_gsolve),
            "charpoly": KernelCmd("charpoly [[a,b],[c,d]] = det(lam*I - M)", lambda s, r: s.mcharpoly(r.strip())),
            "eigenvalues": KernelCmd("eigenvalues [[a,b],[c,d]]", lambda s, r: s.meigenvalues(r.strip())),
            "eigenvectors": KernelCmd("eigenvectors [[a,b],[c,d]]", lambda s, r: s.meigenvectors(r.strip())),
            "solveineq": KernelCmd("solveineq <expr> <op> 0 <var>", _k_solveineq),
            "solveset": KernelCmd("solveset <expr> <var> (set-valued solutions)", _k_solveset),
        }

    def _check_locked(self):
        if self.locked:
            raise ValueError(f"session locked: {self.locked} (ex falso; undo or start over)")

    def feed(self, s):
        self._check_locked()
        self.current = self._expand_defs(parse(s), bare_ok=True)
        self._remember(self.current)
        return self.current

    # ---------------- 用户定义（交互式 CAS 标配：f(x) := 体 / a := 体） ----------------

    # Protected 属性（mathics attributes.py 同款）：内建头一律拒绝覆盖。
    # 清单纪律：新增结构头/绑定词头时必须同步加入（代码评审验收点）。
    _RESERVED = {"Plus", "Times", "Power", "Eq", "Ne", "Lt", "Le", "Gt", "Ge",
                 "And", "Or", "Not", "Bound", "Quote", "D", "Attr", "Piecewise",
                 "Integrate", "Sum", "Product", "Limit", "Conjugate", "RootOf",
                 "Infinity", "Undefined", "FiniteSet", "Interval", "Union", "O"}
    # Sqrt 由 parser 直重写为 Power，无此头

    def _check_def_name(self, name):
        from cas.spec import SPECS

        # 裸符号不capitalize（Sym 保持原名），但函数头会首字母大写——
        # 两种形态都不得与保留头/spec 头冲突
        cap = name[0].upper() + name[1:] if len(name) > 1 else name
        if name in self._RESERVED or cap in self._RESERVED or name in SPECS or cap in SPECS:
            raise ParseError(f"cannot redefine built-in: {name}")

    def define(self, sig_s, body_s):
        """函数定义 f(x, y) := 体：feed 时对 f(...) 出现做宏展开（参数代入）。"""
        sig = parse(sig_s)
        if not (isinstance(sig, T.Expr) and sig.args and all(isinstance(a, T.Sym) for a in sig.args)):
            raise ParseError("usage: name(x, y) := expr")
        name = sig.head.name
        self._check_def_name(name)
        self.defs[name] = (tuple(sig.args), parse(body_s))
        return f"defined: {name}({', '.join(a.name for a in sig.args)})"

    def assign(self, name_s, body_s):
        """变量定义 a := 体：feed 时对同名符号全局代入（宏语义，非方程）。"""
        v = parse(name_s)
        if not isinstance(v, T.Sym):
            raise ParseError("usage: name := expr")
        self._check_def_name(v.name)
        self.defs[v.name] = ((), parse(body_s))
        return f"assigned: {v.name}"

    def undef(self, name_s):
        v = parse(name_s)
        nm = v.head.name if isinstance(v, T.Expr) else getattr(v, "name", None)
        if nm in self.defs:
            del self.defs[nm]
            return f"undefined: {nm}"
        return f"no definition: {name_s}"

    def _subst_defs(self, t):
        """单遍定义展开（显式栈后序重建）：函数头按参数代入，变量直接替换。

        保指针重建：子项无变化时复用原节点（Bound 不驻留，每次重建都生新指针，
        不复用会导致不动点判等失效）。
        """
        order = []
        stack = [t]
        while stack:
            u = stack.pop()
            order.append(u)
            if isinstance(u, T.Expr):
                stack.extend(u.args)
            elif isinstance(u, T.Bound):
                stack.append(u.body)
        val = {}
        for u in reversed(order):
            if isinstance(u, T.Expr):
                new_args = tuple(val[a] for a in u.args)
                d_ = self.defs.get(u.head.name)
                if d_ is not None and len(d_[0]) == len(new_args):
                    val[u] = T.subst(d_[1], dict(zip(d_[0], new_args)))
                elif all(na is oa for na, oa in zip(new_args, u.args)):
                    val[u] = u
                else:
                    val[u] = T.mk(u.head, new_args)
            elif isinstance(u, T.Bound):
                nb = val[u.body]
                val[u] = u if nb is u.body else T._mk_bound_canon(u.hint, nb)
            else:
                d_ = self.defs.get(u.name, None) if isinstance(u, T.Sym) else None
                val[u] = d_[1] if d_ is not None and d_[0] == () else u
        return val[t]

    def _expand_defs(self, t, bare_ok=False):
        """定义展开到不动点；轮数上限兼防递归定义死循环（永不静默错）。

        bare_ok=False 时裸符号不展开（内核参数位，变量名作主语优先）；
        feed 交互输入 bare_ok=True（变量定义求值语义，函数定义仍需调用才展开）。
        """
        if not self.defs or (isinstance(t, T.Sym) and not bare_ok):
            return t
        for _ in range(20):
            nxt = self._subst_defs(t)
            if nxt is t:
                return t
            t = nxt
        raise BudgetExceeded(message="definition expansion too deep (recursive definition?)")

    def _remember(self, t):
        if isinstance(t, T.Term) and t not in (T.ZERO, T.ONE):
            self.history.append(t)

    def expand_history(self, line):
        """%N 引用第 N 个历史产出，裸 % 引用最近一个（Mathematica %/%% 同款最小版）。

        插入位置上下文未知，按最高优先级渲染补括号（多和项嵌入乘法不破语义）。"""
        import re

        def rep(m):
            n = m.group(1)
            if not n:
                if not self.history:
                    raise ParseError("no history yet")
                t = self.history[-1]
            else:
                i = int(n)
                if not (1 <= i <= len(self.history)):
                    raise ParseError(f"no history %{i} (have {len(self.history)})")
                t = self.history[i - 1]
            return to_str(t, prec=99, src=True)

        return re.sub(r"%(\d*)", rep, line)

    def _parse_in(self, s):
        """会话内输入统一入口：解析 + 用户定义展开。

        裸符号豁免：内核参数位裸符号常作主语（如 !integrate f 的积分变量），
        变量名优先于宏语义。
        """
        return self._expand_defs(parse(s), bare_ok=False)

    def _guard_eval(self, guard, sub):
        return _eval_guard(guard, sub, self.ctx)

    def suggest(self, path=None):
        if self.current is None:
            return []
        paths = [tuple(path)] if path is not None else list(T.all_paths(self.current))
        out = []
        for p in paths:
            tgt = T.term_at(self.current, p)
            for r in self.rules.for_term(tgt):
                res = apply_rule(r, self.current, p, self._guard_eval)
                if res.guard in ("YES", "UNKNOWN"):
                    out.append((r.id, res.guard, p))
        return out

    def apply(self, rid, path=None):
        """应用规则。path=None 时自动全式搜索首个匹配位置（规则主路径，
        不再要求用户手工指定路径）。返回新项；不适用时返回说明字符串。"""
        self._check_locked()
        r = self.rules.rules.get(rid)
        if r is None:
            return f"no rule {rid}"
        if path is None:
            if self.current is None:
                return "empty session"
            found = None
            for p in T.all_paths(self.current):
                res = apply_rule(r, self.current, p, self._guard_eval, self.budget)
                if res.guard != "NOMATCH":
                    found = (p, res)
                    break
            if found is None:
                return f"rule {rid} does not match anywhere"
            path, res = found
        else:
            res = apply_rule(r, self.current, path, self._guard_eval, self.budget)
        if res.guard == "NOMATCH":
            return f"rule {rid} does not match at {path}"
        if res.guard == "UNKNOWN":
            self._oid += 1
            q = T.instantiate(r.guard, res.subst)
            obl = Obligation(self._oid, q, [self._sid + 1], note=f"guard of {rid}")
            obl.pending.append({"rule": rid, "path": tuple(path)})
            self.obligations.append(obl)
            return f"guard UNKNOWN: {to_str(q)}  (obligation #{self._oid} created; answer then :ans {self._oid} <fact>)"
        return self._commit(r, path, res)

    def _commit(self, r, path, res):
        """提交一次已计算好的规则应用（res 必须是在 self.current 上算出的）。

        提交后 remember 当前式：规则应用也产出可引用表达式（% 指向最近推导结果，
        而非 feed 时的原始式；Mathematica Out 语义同款）。
        """
        self._sid += 1
        before = self.current
        self.current = res.term
        st = Step(self._sid, r.id, tuple(path), before, self.current, res.guard, cost(res.term) - cost(before))
        self.log.append(st)
        self._remember(self.current)
        if r.guard is not None:
            g = T.instantiate(r.guard, res.subst)
            cst, _ = self.ctx.check_and_assume(g, origin=f"step{self._sid}", kind="guard")
            if cst is T3.NO:
                self.locked = f"contradiction after step {self._sid}"
        return self.current

    def _eq_rewrite_step(self):
        """等式即规则：账本等式双向替换，仅接受 cost 严格下降（防循环）。"""
        for e in self.ctx.entries:
            f = e.fact
            if not (isinstance(f, T.Term) and isinstance(f, T.Expr) and f.head.name == "Eq"):
                continue
            u, v = f.args
            for pat, rep in ((u, v), (v, u)):
                nxt = T.subst(self.current, {pat: rep})
                if nxt is self.current:
                    continue
                if cost(nxt) < cost(self.current):
                    self._sid += 1
                    self.log.append(Step(
                        self._sid, f"eq[{e.origin}]", (), self.current, nxt, "YES",
                        cost(nxt) - cost(self.current),
                    ))
                    self.current = nxt
                    return True
        return False

    def auto(self):
        """自动重写：构造器规范化 + 账本等式 + auto 规则，cost 不增才接受，每步入 step log。

        停机保证：cost 单调不增（等式替换严格下降）+ 已见项集合防振荡 + 轮数上限。
        """
        self._check_locked()
        if self.current is None:
            return None
        auto_rules = sorted(
            (r for r in self.rules.rules.values() if r.auto),
            key=lambda r: r.priority,
        )
        seen = {self.current._h}
        for _ in range(10):
            s0 = simplify(self.current, self.budget)
            if s0 is not self.current:
                self._sid += 1
                self.log.append(Step(
                    self._sid, "norm", (), self.current, s0, "YES",
                    cost(s0) - cost(self.current),
                ))
                self.current = s0
                seen.add(s0._h)
            if self._eq_rewrite_step():
                seen.add(self.current._h)
                continue
            changed = False
            for p in T.all_paths(self.current):
                try:
                    T.term_at(self.current, p)
                except IndexError:
                    continue
                for r in auto_rules:
                    res = apply_rule(r, self.current, p, self._guard_eval, self.budget)
                    if res.guard != "YES":
                        continue
                    if res.term._h in seen:
                        continue
                    if cost(res.term) <= cost(self.current):
                        self._commit(r, p, res)
                        seen.add(res.term._h)
                        changed = True
                        break
                if changed:
                    break
            if not changed:
                break
        return self.current

    def assume(self, s):
        f = self._parse_in(s)
        st, why = self.ctx.check_and_assume(f, origin="user")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            self.locked = f"contradiction: {to_str(f)} vs ledger"
            return f"CONTRADICTION LOCKED: {self.locked}"
        return f"assumed: {to_str(f)}"

    def declare(self, var_s, prop):
        """声明变量属性（属性入 ledger，kind='attr'，decide 区间通道消费）。

        符号类属性（positive/negative/nonnegative/nonpositive）映射为不等式事实；
        离散类属性（integer/even/odd/real）存为 Attr 条目（even/odd 隐含 integer）。
        """
        v = T.S(var_s)
        prop = prop.lower()
        sign_map = {
            "positive": T.gt(v, T.ZERO),
            "negative": T.lt(v, T.ZERO),
            "nonnegative": T.ge(v, T.ZERO),
            "nonpositive": T.le(v, T.ZERO),
        }
        if prop in sign_map:
            return self._assume_fact(sign_map[prop])
        if prop in ("integer", "real", "even", "odd"):
            props = ["integer", prop] if prop in ("even", "odd") else [prop]
            for p in props:
                st, why = self.ctx.check_and_assume(
                    T.mk(T.S("Attr"), (v, T.S(p))), origin="user", kind="attr"
                )
                if st is T3.NO:
                    return f"declaration rejected ({why}): {var_s} {p}"
            return f"declared: {var_s} {prop}"
        return f"unknown property: {prop}"

    def _assume_fact(self, f):
        st, why = self.ctx.check_and_assume(f, origin="user")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            self.locked = f"contradiction: {to_str(f)} vs ledger"
            return f"CONTRADICTION LOCKED: {self.locked}"
        return f"assumed: {to_str(f)}"

    def answer(self, oid, s):
        self._check_locked()
        f = self._parse_in(s)
        obl = next((o for o in self.obligations if o.oid == oid), None)
        if obl is None:
            return f"no obligation #{oid}"
        st, why = self.ctx.check_and_assume(f, origin=f"obl{oid}", kind="answer")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            return f"answer rejected: {to_str(f)} contradicts ledger"
        pending = list(obl.pending)
        for p in pending:
            rid = p["rule"]
            r = self.rules.rules.get(rid)
            if r is None:
                obl.pending.remove(p)
                continue
            # 重放用全式搜索（旧 path 可能因期间变换失效）
            found = None
            for path in T.all_paths(self.current):
                res = apply_rule(r, self.current, path, self._guard_eval, self.budget)
                if res.guard != "NOMATCH":
                    found = (path, res)
                    break
            if found is None:
                obl.pending.remove(p)
                continue
            path, res = found
            if res.guard == "YES":
                self._commit(r, path, res)
                obl.pending.remove(p)
        if not obl.pending:
            if obl in self.obligations:
                self.obligations.remove(obl)
            return f"answered #{oid}: {to_str(f)}"
        return f"answered #{oid} (assumed); obligation kept: still undecidable"

    def undo(self, n=1):
        for _ in range(n):
            if not self.log:
                return
            st = self.log.pop()
            self.current = st.before
            self.ctx.drop_origin(f"step{st.sid}")
            # 撤掉引发矛盾锁的那一步 -> 解锁
            if self.locked and f"step {st.sid}" in self.locked:
                self.locked = None
        return self.current

    def replay(self, from_sid=0):
        steps = [s for s in self.log if s.sid > from_sid]
        base = next((s.before for s in self.log if s.sid == from_sid), None)
        if base is None and from_sid == 0:
            base = self.log[0].before if self.log else None
        if base is None:
            return "nothing to replay"
        # 清旧 step 账本条目（重放会重新入账，防陈旧事实累积）
        self.ctx.entries = [
            e for e in self.ctx.entries
            if not (isinstance(e.origin, str) and e.origin.startswith("step"))
        ]
        self.current = base
        for st in steps:
            if st.rule_id.startswith("kernel:"):
                # 内核算法步：不可规则重放，直接恢复其输出（正确性由 verify 背书）
                self.current = st.after
                continue
            r = self.rules.rules.get(st.rule_id)
            if r is None:
                return f"replay stuck at {st.rule_id}"
            res = apply_rule(r, self.current, st.path, self._guard_eval, self.budget)
            if res.guard != "YES":
                return f"replay diverged at step {st.sid} ({res.guard})"
            self._commit(r, st.path, res)
        return self.current

    def _kernel_step(self, algo, result, before=None):
        """内核算法调用入账：单算法调用不做微观步骤解释（正确性由 verify 背书），
        只记算法名 + 输入/输出 + 验证态（可解释性的最小诚实单位）。
        命令结果同时成为当前表达式（公式区展示，可继续交互）。"""
        self._sid += 1
        self.log.append(Step(
            self._sid, "kernel:" + algo, (), before, result, "YES", 0,
            note=f"algorithm={algo}",
        ))
        self._remember(result)
        self.current = result

    def steps(self):
        """可解释步骤文本：规则步 = 逐条推导（规则名/位置/守卫/前后式/cost 变化）；
        算法步 = 算法名 + 验证态（单算法调用无微观步骤可讲，verify 背书即解释）。"""
        if not self.log:
            return ["(no steps)"]
        out = []
        for st in self.log:
            if st.rule_id.startswith("kernel:"):
                src = to_str(st.before) + " " if st.before is not None else ""
                out.append(f"#{st.sid} [algorithm] {src}-> {to_str(st.after)}   ({st.note})")
            else:
                at = f" at {st.path}" if st.path else ""
                note = f"  ({st.note})" if st.note else ""
                out.append(
                    f"#{st.sid} [rule {st.rule_id}]{at}  "
                    f"{to_str(st.before)}  ->  {to_str(st.after)}   "
                    f"(guard={st.guard}, dcost={st.dcost}){note}"
                )
        return out

    def show(self):
        return to_str(self.current) if self.current is not None else "(empty)"
