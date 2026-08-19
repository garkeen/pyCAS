import os

from dataclasses import dataclass, field

from cas import term as T
from cas import context as context_mod
from cas.decide import (
    eval_guard as _eval_guard,
    decide as _decide_fn,
    contradicted as _contradicted_fn,
    T3,
)
from cas.context import Context
from cas.parser import parse
from cas.pprint import to_str
from cas.rules import Rule, RuleSet, Step, apply_rule
from cas.simplify import simplify, cost, expand
from cas.errors import BudgetExceeded, ParseError
from cas import loader
from cas import spec as _spec


@dataclass
class Obligation:
    oid: int
    question: T.Term
    affects: list
    note: str = ""
    pending: list = field(default_factory=list)


@dataclass
class KernelCmd:
    """内核命令注册条目（机械算法黑盒快捷通道）。

    新增内核算法 = 注册一条 KernelCmd，REPL/帮助表自动可见，不再改分发代码。
    """
    help: str
    fn: object   # (session, rest: str) -> str


def _k_verify(s, rest):
    # 从末尾切两次：变量与目标式不含空格时 F 可含空格（% 展开后常见）
    parts = rest.rsplit(None, 2)
    if len(parts) != 3:
        return "usage: :verify <F> <x> <f>"
    return s.verify(*parts)


def _k_solve(s, rest):
    if not rest.strip():
        return "usage: :solve <expr> [var]"
    # 变量名只可能是末尾单个标识符：只从末尾分一次，避免切碎含空格的表达式
    parts = rest.rsplit(None, 1)
    if len(parts) == 2 and parts[1].isidentifier():
        return s.solve(parts[0], parts[1])
    return s.solve(rest.strip(), None)


def _k_factor(s, rest):
    if not rest.strip():
        return "usage: :factor <expr>"
    return s.factor(rest.strip())


def _k_apart(s, rest):
    args = rest.split()
    if len(args) != 2:
        return "usage: :apart <numerator> <denominator>"
    return s.apart(args[0], args[1])


def _k_integrate(s, rest):
    if not rest.strip():
        return "usage: :integrate <expr>"
    return s.integrate(rest.strip())


def _k_limit(s, rest):
    parts = rest.rsplit(None, 2)
    if len(parts) != 3 or not parts[1].isidentifier():
        return "usage: :limit <expr> <var> <point>"
    return s.mlimit(parts[0], parts[1], parts[2])


def _k_series(s, rest):
    parts = rest.rsplit(None, 3)
    if len(parts) != 4 or not parts[1].isidentifier():
        return "usage: :series <expr> <var> <point> <order>"
    return s.mseries(parts[0], parts[1], parts[2], parts[3])


def _k_isteps(s, rest):
    """积分策略步树（manualintegrate 同款）：推导即数据，不执行计算。"""
    from cas.istrategy import explain, format_steps

    parts = rest.rsplit(None, 1)
    if not parts:
        return "usage: :isteps <expr> [var]"
    t = s._parse_in(parts[0])
    if len(parts) == 2 and parts[1].isidentifier():
        x = T.S(parts[1])
    else:
        vs = sorted(T.free_vars(t), key=lambda v: v.name)
        if len(vs) != 1:
            return "usage: :isteps <expr> <var> (expr has multiple variables)"
        x = vs[0]
    return "\n".join(format_steps(explain(t, x)))


def _k_defint(s, rest):
    parts = rest.rsplit(None, 3)
    if len(parts) != 4 or not parts[1].isidentifier():
        return "usage: :defint <expr> <var> <lo> <hi>"
    return s.mdefint(parts[0], parts[1], parts[2], parts[3])


def _k_msolve(s, rest):
    idx = rest.find("]] ")
    if idx >= 0:
        spec = rest[: idx + 2]
        rhs = rest[idx + 3:].strip()
        if rhs.startswith("[") and rhs.endswith("]"):
            return s.msolve(spec, rhs)
    return "usage: :msolve [[a,b],[c,d]] [e,f]"


def _k_together(s, rest):
    from cas import ops
    from cas.parser import parse as _parse

    if not rest.strip():
        return "usage: :together <expr>"
    return to_str(ops.together(_parse(rest.strip())))


def _k_collect(s, rest):
    from cas import ops
    from cas.parser import parse as _parse

    parts = rest.rsplit(None, 1)
    if len(parts) != 2 or not parts[1].isidentifier():
        return "usage: :collect <expr> <var>"
    return to_str(ops.collect(_parse(parts[0]), T.S(parts[1])))


def _k_num_den(kind):
    def fn(s, rest):
        from cas import ops
        from cas.parser import parse as _parse

        if not rest.strip():
            return f"usage: :{kind} <expr>"
        t = _parse(rest.strip())
        return to_str(ops.numerator(t) if kind == "numerator" else ops.denominator(t))
    return fn


def _k_coefficient(s, rest):
    from cas import ops
    from cas.parser import parse as _parse

    parts = rest.split()
    if len(parts) < 2:
        return "usage: :coefficient <expr> <var> [k]"
    k = int(parts[2]) if len(parts) > 2 else 1
    expr_s = " ".join(parts[:1])
    return to_str(ops.coefficient(_parse(expr_s), T.S(parts[1]), k))


def _k_solveineq(s, rest):
    from cas.ineq import solve_poly_ineq
    from cas.parser import parse as _parse

    parts = rest.rsplit(None, 1)
    if len(parts) != 2 or not parts[1].isidentifier():
        return "usage: :solveineq <expr> <op> 0 <var>   (e.g. :solveineq x^2-1 > 0 x)"
    f = _parse(parts[0])
    if not (isinstance(f, T.Expr) and f.head.name in ("Gt", "Ge", "Lt", "Le")):
        return "need a comparison like x^2-1 > 0"
    if f.args[1] is not T.ZERO:
        return "right side must be 0"
    _ivs, out = solve_poly_ineq(f.args[0], f.head.name, T.S(parts[1]))
    return f"{parts[1]} in {out}"


def _k_solveset(s, rest):
    """解集一等结构：方程 -> FiniteSet，不等式 -> 区间并（solveset 形态）。"""
    from cas import sets as _sets

    parts = rest.rsplit(None, 1)
    if len(parts) != 2 or not parts[1].isidentifier():
        return "usage: :solveset <expr> <var>   (e.g. :solveset x^2 = 1 x / :solveset x^2-1 > 0 x)"
    f = s._parse_in(parts[0])
    var = T.S(parts[1])
    if isinstance(f, T.Expr) and f.head.name in ("Lt", "Le", "Gt", "Ge"):
        if f.args[1] is not T.ZERO:
            f = T.mk(T.S(f.head.name), (T.plus(f.args[0], T.neg(f.args[1])), T.ZERO))
        st, note = _sets.ineq_set(f.args[0], f.head.name, var)
        if st is None:
            return f"honest refusal: {note}"
        return f"{parts[1]} in {to_str(st)}"
    try:
        st, provisos = _sets.solve_set(f, var)
    except ValueError as e:
        return f"unsupported: {e}"
    out = f"{parts[1]} in {to_str(st)}"
    if provisos:
        out += "   [provisos: " + ", ".join(to_str(p) for p in provisos) + "]"
    return out


class Session:
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
        # 内核命令注册表（机械算法快捷通道；新增算法只需注册，不改 REPL）
        self.kernel = {
            "verify": KernelCmd("verify <F> <x> <f>", _k_verify),
            "solve": KernelCmd("solve <expr> [var]", _k_solve),
            "factor": KernelCmd("factor <expr>", _k_factor),
            "apart": KernelCmd("apart <num> <den>", _k_apart),
            "integrate": KernelCmd("integrate <expr>", _k_integrate),
            "isteps": KernelCmd("isteps <expr> [var] (strategy step tree)", _k_isteps),
            "limit": KernelCmd("limit <expr> <var> <point> (point may be +/-inf)", _k_limit),
            "series": KernelCmd("series <expr> <var> <point> <order> (Taylor + O term)", _k_series),
            "defint": KernelCmd("defint <expr> <var> <lo> <hi>", _k_defint),
            "mat": KernelCmd("show matrix [[a,b],[c,d]]", lambda s, r: s.mat(r.strip())),
            "mdet": KernelCmd("determinant [[a,b],[c,d]]", lambda s, r: s.mdet(r.strip())),
            "mrank": KernelCmd("rank [[a,b],[c,d]]", lambda s, r: s.mrank(r.strip())),
            "minv": KernelCmd("inverse [[a,b],[c,d]]", lambda s, r: s.minv(r.strip())),
            "msolve": KernelCmd("solve system: :msolve [[a,b],[c,d]] [e,f]", _k_msolve),
            "charpoly": KernelCmd("charpoly [[a,b],[c,d]] = det(lam*I - M)", lambda s, r: s.mcharpoly(r.strip())),
            "eigenvalues": KernelCmd("eigenvalues [[a,b],[c,d]]", lambda s, r: s.meigenvalues(r.strip())),
            "eigenvectors": KernelCmd("eigenvectors [[a,b],[c,d]]", lambda s, r: s.meigenvectors(r.strip())),
            "together": KernelCmd("together <expr> (common denominator)", _k_together),
            "collect": KernelCmd("collect <expr> <var>", _k_collect),
            "numerator": KernelCmd("numerator <expr>", _k_num_den("numerator")),
            "denominator": KernelCmd("denominator <expr>", _k_num_den("denominator")),
            "coefficient": KernelCmd("coefficient <expr> <var> [k]", _k_coefficient),
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
                val[u] = u if nb is u.body else T.mk_bound(u.hint, nb)
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
            return to_str(t, prec=99)

        return re.sub(r"%(\d*)", rep, line)

    def _parse_in(self, s):
        """会话内输入统一入口：解析 + 用户定义展开。

        裸符号豁免：内核参数位裸符号常作主语（如 :integrate f 的积分变量），
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
        """提交一次已计算好的规则应用（res 必须是在 self.current 上算出的）。"""
        self._sid += 1
        before = self.current
        self.current = res.term
        st = Step(self._sid, r.id, tuple(path), before, self.current, res.guard, cost(res.term) - cost(before))
        self.log.append(st)
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

    def verify(self, Fs, xs, fs):
        from cas.diff import verify

        F = self._parse_in(Fs)
        x = parse(xs)
        f = self._parse_in(fs)
        return verify(F, x, f, self.budget)

    def solve(self, fs, vs=None):
        from cas.solve import solve

        f = self._parse_in(fs)
        if vs:
            var = T.S(vs)
        else:
            var = None
            for p in T.all_paths(f):
                t = T.term_at(f, p)
                if isinstance(t, T.Sym) and t.name not in ("e", "pi"):
                    var = t
                    break
        if var is None:
            return "no variable to solve for"
        r = solve(f, var, self.budget)
        if r.status == "identity":
            return "identity: 0 = 0 for all " + var.name
        if r.status == "contradiction":
            return "contradiction: no solution"
        if r.status == "unsupported":
            return "unsupported: " + (r.note or "cannot solve")
        out = ", ".join(to_str(s) for s in r.solutions) or "(none)"
        if r.provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in r.provisos) + "]"
        return var.name + " = " + out

    def mat(self, spec):
        from cas.matrix import Matrix

        return Matrix.parse(spec).show()

    def mdet(self, spec):
        from cas.matrix import Matrix
        from cas.pprint import to_str

        return to_str(Matrix.parse(spec).det())

    def mrank(self, spec):
        from cas.matrix import Matrix

        return str(Matrix.parse(spec).rank())

    def minv(self, spec):
        from cas.matrix import Matrix

        m = Matrix.parse(spec).inv()
        return m.show() if m is not None else "singular"

    def msolve(self, spec, rhs):
        from cas.matrix import Matrix
        from cas.parser import parse
        from cas.pprint import to_str

        b = [parse(c.strip()) for c in rhs.strip()[1:-1].split(",")]
        r = Matrix.parse(spec).solve(b)
        if r.unique is not None:
            return ", ".join(
                f"x{i + 1} = {to_str(v)}" for i, v in enumerate(r.unique)
            )
        if r.particular is None:
            return "no solution"
        parts = ", ".join(f"x{i + 1} = {to_str(v)}" for i, v in enumerate(r.particular))
        basis = "; ".join(
            "(" + ", ".join(to_str(v) for v in vec) + ")" for vec in r.null_basis
        )
        return f"infinite: {parts}  + t*({basis})"

    def mcharpoly(self, spec):
        from cas.matrix import Matrix

        t, lam = Matrix.parse(spec).charpoly()
        return f"{to_str(t)}   (in {lam.name})"

    def meigenvalues(self, spec):
        from cas.matrix import Matrix

        r = Matrix.parse(spec).eigenvalues()
        if r.status == "ok":
            out = ", ".join(to_str(v) for v in r.solutions) or "(none)"
            if r.provisos:
                out += "   [proviso: " + " && ".join(to_str(g) for g in r.provisos) + "]"
            return out
        return "unsupported: " + (r.note or r.status)

    def meigenvectors(self, spec):
        from cas.matrix import Matrix, MatrixError

        try:
            pairs = Matrix.parse(spec).eigenvectors()
        except MatrixError as e:
            return str(e)
        lines = []
        for v, basis in pairs:
            vecs = "; ".join("(" + ", ".join(to_str(c) for c in b) + ")" for b in basis)
            lines.append(f"lam = {to_str(v)}: {vecs or '(none found)'}")
        return "\n".join(lines)

    def _pick_var(self, t):
        for p in T.all_paths(t):
            v = T.term_at(t, p)
            if isinstance(v, T.Sym) and v.name not in ("e", "pi"):
                return v
        return None

    def factor(self, s):
        from cas.factor import factor_str
        from cas.poly import Poly

        t = self._parse_in(s)
        x = self._pick_var(t)
        if x is None:
            return "no variable"
        return factor_str(Poly.from_term(t, (x,)))

    def apart(self, num_s, den_s):
        from cas.poly import Poly
        from cas.apart import apart as zz_apart

        t1 = self._parse_in(num_s)
        t2 = self._parse_in(den_s)
        x = self._pick_var(t1) or self._pick_var(t2)
        if x is None:
            return "no variable"
        f = Poly.from_term(t1, (x,))
        g = Poly.from_term(t2, (x,))
        q, terms = zz_apart(f, g)
        out = []
        if not q.is_zero():
            out.append(str(q))
        for nn, dd, k in terms:
            s_ = f"({nn})/({dd})"
            out.append(f"{s_}^{k}" if k > 1 else s_)
        return " + ".join(out) if out else "0"

    def _kernel_step(self, algo, result, before=None):
        """内核算法调用入账：单算法调用不做微观步骤解释（正确性由 verify 背书），
        只记算法名 + 输入/输出 + 验证态（可解释性的最小诚实单位）。"""
        self._sid += 1
        self.log.append(Step(
            self._sid, "kernel:" + algo, (), before, result, "YES", 0,
            note=f"algorithm={algo}",
        ))
        self._remember(result)

    def integrate(self, s):
        from cas.integrate import integrate as zz_int
        from cas.pprint import to_str as ps

        t = self._parse_in(s)
        x = self._pick_var(t)
        if x is None:
            return "no variable"
        res, ok, method = zz_int(t, x)
        self._kernel_step(f"integrate[{method}]", res, before=t)
        out = ps(res)
        tag = "VERIFIED" if ok else "UNVERIFIED"
        return f"{out}   [{tag}, method: {method}]"

    def mlimit(self, expr_s, var_s, point_s):
        """:limit 入口：三值诚实（UNKNOWN 直接显示，永不静默错）；point 可为 ±inf。"""
        from cas.limits import limit

        t = self._parse_in(expr_s)
        ps = point_s.strip().lower()
        if ps in ("inf", "+inf", "infinity", "+infinity"):
            pt = T.INFINITY
        elif ps in ("-inf", "-infinity"):
            pt = T.neg(T.INFINITY)
        else:
            pt = parse(point_s)
        r = limit(t, T.S(var_s), pt)
        if r is None:
            return "UNKNOWN"
        self._remember(r)
        return to_str(r)

    def mseries(self, expr_s, var_s, point_s, order_s):
        """:series 入口：Taylor 展开为截断多项式 + O 项（O 为一等项头）。"""
        from cas.series import series_term, SeriesError

        t = self._parse_in(expr_s)
        try:
            r = series_term(t, T.S(var_s), parse(point_s), int(order_s))
        except SeriesError as e:
            return f"honest refusal: {e}"
        self._remember(r)
        return to_str(r)

    def _parse_bound(self, s):
        """限字面量：inf/-inf -> ±Infinity 项，其余按表达式解析。"""
        ps = s.strip().lower()
        if ps in ("inf", "+inf", "infinity", "+infinity"):
            return T.INFINITY
        if ps in ("-inf", "-infinity"):
            return T.neg(T.INFINITY)
        return parse(s)

    def mdefint(self, expr_s, var_s, lo_s, hi_s):
        """:defint 入口：自动正向换元探测 + Newton-Leibniz + 奇点拆分 + 数值交叉核对。"""
        from cas.integrate import defint_auto

        t = self._parse_in(expr_s)
        val, status, note = defint_auto(t, T.S(var_s), self._parse_bound(lo_s), self._parse_bound(hi_s))
        if val is not None:
            self._kernel_step(f"defint[{note}]", val, before=t)
            return f"{to_str(val)}   [{status}, method: {note}]"
        return f"{status}: {note}"

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
                out.append(
                    f"#{st.sid} [rule {st.rule_id}]{at}  "
                    f"{to_str(st.before)}  ->  {to_str(st.after)}   "
                    f"(guard={st.guard}, dcost={st.dcost})"
                )
        return out

    def show(self):
        return to_str(self.current) if self.current is not None else "(empty)"

    # ---------------- 转录 DSL（计算可复现/可保存/可回放） ----------------

    # 只读命令不入转录；变更类命令（:rule/:value/:refine/:assume 等）必须入录，
    # 否则回放无法重建推导（转录即 DSL 立场）。
    _NO_RECORD = {":help", ":log", ":steps", ":hist", ":ctx", ":obls", ":defs",
                  ":q", ":quit", ":save", ":replay", ":rules", ":latex"}

    def rules_fingerprint(self):
        """规则集指纹：回放确定性校验用（规则变了回放即失效，永不静默错）。

        只覆盖非会话规则：origin='session' 的 :rule 内联定义由转录自身重建，
        不计入指纹（否则保存后回放必被自己的新规则拒死）。
        """
        import hashlib

        h = hashlib.sha1()
        for rid in sorted(self.rules.rules):
            r = self.rules.rules[rid]
            if r.origin == "session":
                continue
            h.update(f"{rid}|{to_str(r.pattern)}|{to_str(r.template)}|{r.priority}".encode())
        return h.hexdigest()[:12]

    def handle(self, line):
        """分发一条命令/表达式，返回输出文本（None = 无输出）。

        REPL 与回放共用同一入口——转录即 DSL，重放转录即重建推导。
        """
        line = line.strip()
        if not line:
            return None
        first = line.split(None, 1)[0]
        try:
            out = self._dispatch(line)
        except (BudgetExceeded, ParseError) as e:
            out = f"error: {e}"
        except Exception as e:
            out = f"error: {e.__class__.__name__}: {e}"
        if first not in self._NO_RECORD:
            self.transcript.append(line)
        return out

    def save_transcript(self, path):
        """保存转录（头部含规则指纹，回放时校验）。"""
        lines = ["# pyCAS transcript v1", f"# rules: {self.rules_fingerprint()}"]
        lines.extend(self.transcript)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines) + "\n")
        return f"saved {len(self.transcript)} commands to {path}"

    def replay_file(self, path):
        """回放转录文件：跳注释头，逐条走 handle（与 REPL 完全同路径）。"""
        with open(path, "r", encoding="utf-8") as fh:
            raw = fh.readlines()
        cmds = []
        fp = None
        for ln in raw:
            ln = ln.rstrip("\n")
            if ln.startswith("# rules: "):
                fp = ln.split(": ", 1)[1].strip()
            elif not ln.startswith("#"):
                cmds.append(ln)
        if fp is not None and fp != self.rules_fingerprint():
            return (f"refused: rules fingerprint mismatch "
                    f"(file={fp}, session={self.rules_fingerprint()})")
        outs = []
        for c in cmds:
            if not c.strip():
                continue
            o = self.handle(c)
            if o:
                outs.append(o)
        return f"replayed {len(cmds)} commands\n" + "\n".join(outs)

    def commands(self):
        out = {
            ":s": "suggest [path]",
            ":a": "apply <rule-id> [path]",
            ":u": "undo [n]",
            ":auto": "core simplify",
            ":parts": "integration by parts on inert integral: :parts <u>",
            ":solveq": "solve current linear equation for unknown: :solveq <term>",
            ":rule": "define session theorem inline: :rule id = lhs -> rhs [guard ... as ... auto]",
            ":unrule": "remove a session rule",
            ":rules": "list all rules (origin/prio/guard/direction)",
            ":value": "evaluate inert forms (Quote/'integrate/D nouns) in current expr",
            ":refine": "ledger-driven simplification (abs/sqrt/exp-log by assumptions)",
            ":latex": "LaTeX output of current expression",
            ":save": "save command transcript (DSL): :save <path>",
            ":replay": "replay a transcript: :replay <path>",
            ":steps": "explain the derivation (rules step-by-step; algorithms by name)",
            ":hist": "produced expressions (%N to reuse, % = latest)",
            ":defs": "list user definitions (name := expr / f(x) := expr)",
            ":undef": "remove a definition",
            ":assume": "assume <fact>",
            ":ans": "answer <oid> <fact>",
            ":obls": "list obligations",
            ":log": "step log",
            ":ctx": "ledger",
        }
        for name, c in self.kernel.items():
            out[":" + name] = c.help
        out[":load"] = "reload rules dir"
        out[":q"] = "quit"
        return out


    def _dispatch(self, line):
        """全部分支返回文本（不打印）：REPL 与回放共用。分支顺序纪律：
        精确命令 > 内核注册表 > 前缀命令（:steps 被 :s 吞、:save 被 :s 吞的同款 bug 防三次）。"""
        if line == ":help":
            return "\n".join(f"{k:12s} {v}" for k, v in self.commands().items())
        if line == ":steps":
            return "\n".join(self.steps())
        if line == ":hist":
            out = [f"%{i}  {to_str(h)}" for i, h in enumerate(self.history, 1)]
            return "\n".join(out) if out else "(empty)"
        if line == ":defs":
            out = []
            for nm, (ps_, body) in self.defs.items():
                sig = f"{nm}({', '.join(p.name for p in ps_)})" if ps_ else nm
                out.append(f"{sig} := {to_str(body)}")
            return "\n".join(out) if out else "(none)"
        if line.startswith(":save "):
            return self.save_transcript(line[6:].strip())
        if line.startswith(":replay "):
            return self.replay_file(line[8:].strip())
        if line.startswith(":rule "):
            return self.add_rule(line[6:])
        if line.startswith(":unrule "):
            return self.unrule(line[8:].strip())
        if line == ":rules":
            return self.list_rules()
        if line == ":value":
            return self.value()
        if line == ":refine":
            return self.mrefine()
        if line == ":latex":
            return self.mlatex()
        if line.startswith(":") and line.split(None, 1)[0][1:] in self.kernel:
            # 内核命令注册表分发（先于前缀匹配，避免 :solve 被 :s 吞掉）
            parts = line.split(None, 1)
            name = parts[0][1:]
            rest = self.expand_history(parts[1].strip()) if len(parts) > 1 else ""
            return self.kernel[name].fn(self, rest)
        if line.startswith(":parts "):
            res = self.iparts(line[7:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":solveq "):
            res = self.solveq(line[8:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":s"):
            arg = line[2:].strip()
            path = tuple(int(i) for i in arg.split(".")) if arg else ()
            out = [f"{rid:20s} guard={g:8s} {('dir=' + d) if d else ''}"
                   for rid, g, d in self.suggest(path)]
            return "\n".join(out)
        if line.startswith(":a "):
            parts = line[3:].split()
            rid = parts[0]
            path = tuple(int(i) for i in parts[1].split(".")) if len(parts) > 1 else None
            n0 = len(self.log)
            res = self.apply(rid, path)
            out = [to_str(res) if isinstance(res, T.Term) else res]
            out += ["  " + ln for ln in self.steps()[n0:]]
            return "\n".join(out)
        if line.startswith(":undef "):
            return self.undef(line[7:].strip())
        if line.startswith(":u"):
            n = int(line[2:] or 1)
            return to_str(self.undo(n)) if self.log else "no steps"
        if line == ":auto":
            n0 = len(self.log)
            out = [to_str(self.auto())]
            out += ["  " + ln for ln in self.steps()[n0:]]
            return "\n".join(out)
        if line.startswith(":assume "):
            return self.assume(self.expand_history(line[8:]))
        if line.startswith(":declare "):
            parts = line[9:].split()
            if len(parts) == 2:
                return self.declare(parts[0], parts[1])
            return "usage: :declare <var> <property>"
        if line.startswith(":ans "):
            parts = line[5:].split(None, 1)
            oid = int(parts[0])
            return self.answer(oid, self.expand_history(parts[1]))
        if line == ":obls":
            out = [f"#{o.oid}  {to_str(o.question)}   affects steps {o.affects}"
                   for o in self.obligations]
            return "\n".join(out) if out else "(none)"
        if line == ":log":
            out = [f"#{st.sid} {st.rule_id:18s} at {st.path}  {to_str(st.before)}  ->  {to_str(st.after)}"
                   for st in self.log]
            return "\n".join(out) if out else "(no steps)"
        if line == ":ctx":
            out = [f"[{e.kind}:{e.origin}] {to_str(e.fact)}" for e in self.ctx.entries]
            return "\n".join(out) if out else "(empty ledger)"
        if line == ":load":
            import os

            rd = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
            return f"loaded {loader.load_dir(rd, self.rules)} rules"
        if ":=" in line:
            # 用户定义：f(x) := 体（函数）/ a := 体（变量），宏展开语义；右侧支持 % 历史
            lhs, rhs = line.split(":=", 1)
            lhs = lhs.strip()
            rhs = self.expand_history(rhs.strip())
            if "(" in lhs:
                return self.define(lhs, rhs)
            return self.assign(lhs, rhs)
        self.feed(self.expand_history(line))
        return self.show()

    # ---------------- 方案命令（人机协作：人选方向，机器算） ----------------

    def iparts(self, u_s):
        """分部积分（人工干预通道）：用户选 u，内核算 dv = 体/u、v = ∫dv、du，
        ∫体 -> u·v − ∫v·du。自动搜索当前式中体被 u 整除的惰性积分子项。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d
        from cas.integrate import integrate as zz_int
        from cas.decide import equivalent
        from cas.errors import PolyError

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
                v, _ok, _m = zz_int(q, x)
            except PolyError:
                continue
            du = d(u, x)
            new_int = T.mk(T.S("Integrate"), (T.mk_bound(x, T.times(v, du)),))
            found = (p, T.plus(T.times(u, v), T.neg(new_int)))
            break
        if found is None:
            return f"parts: no inert integral subterm with body divisible by {to_str(u)}"
        p, repl = found
        before = self.current
        self.current = T.replace_at(self.current, p, repl)
        self._sid += 1
        self.log.append(Step(
            self._sid, f"scheme:parts[u={to_str(u)}]", p, before, self.current, "YES",
            cost(self.current) - cost(before), note="integration by parts",
        ))
        self._remember(self.current)
        return self.current

    def solveq(self, unknown_s):
        """把当前等式当线性方程解出指定未知项（未知 → z 提系数）。

        eˣsin x 消循环的关键步：I = A − I -> I = A/2。
        """
        self._check_locked()
        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Eq"):
            return "solveq: current must be an equation"
        from cas.solve import _linear_split, _free

        unknown = self._parse_in(unknown_s)
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

    # ---------------- 会话规则/名词动词切换/Refine（第一批采购清单） ----------------

    def add_rule(self, text):
        """:rule 内联定理定义（maxima tellsimp 同款）：语法同规则文件行
        （rule id = lhs -> rhs [guard ... as ... prio ... auto]），origin='session'。
        规则库从文件升级为会话参与者；转录自动收录，回放时重建。"""
        self._check_locked()
        body = text.strip()
        if not body.startswith("rule "):
            body = "rule " + body
        r = loader.parse_rule_line(body, origin="session")
        existed = r.id in self.rules.rules
        self.rules.add(r)
        return f"{'redefined' if existed else 'defined'}: {r.id}"

    def unrule(self, rid):
        """删除会话内联规则（文件规则不可删——文件是定理库本体）。"""
        r = self.rules.rules.get(rid)
        if r is None:
            return f"no rule: {rid}"
        if r.origin != "session":
            return f"rule {rid} comes from {r.origin}; only session rules can be removed"
        self.rules.remove(rid)
        return f"removed: {rid}"

    def list_rules(self):
        out = []
        for rid in sorted(self.rules.rules):
            r = self.rules.rules[rid]
            g = f" guard {to_str(r.guard)}" if r.guard is not None else ""
            d = f" as {r.direction}" if r.direction else ""
            a = " auto" if r.auto else ""
            out.append(f"{rid:16s} [{r.origin:10s} prio {r.priority:3d}] "
                       f"{to_str(r.pattern)} -> {to_str(r.template)}{g}{d}{a}")
        return "\n".join(out) if out else "(no rules)"

    def value(self):
        """名词 -> 动词：全式求值惰性形式（Quote 脱壳、惰性 Integrate 实算、D 名词微分）。

        求值失败（如不可积）的惰性头保持名词（诚实）。每次求值入账 kernel 步。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.diff import d as dd
        from cas.integrate import integrate as zz_int
        from cas.errors import PolyError

        changed = False
        order = []
        stack = [self.current]
        while stack:
            u = stack.pop()
            order.append(u)
            if isinstance(u, T.Expr):
                stack.extend(u.args)
            elif isinstance(u, T.Bound):
                stack.append(u.body)
        val = {}
        for u in reversed(order):
            if isinstance(u, T.Bound):
                val[u] = T._mk_bound_canon(u.hint, val[u.body])
                continue
            if not isinstance(u, T.Expr):
                val[u] = u
                continue
            args = tuple(val[a] for a in u.args)
            name = u.head.name
            r = None
            if name == "Quote":
                r = args[0]
            elif name == "Integrate" and len(args) == 1 and isinstance(args[0], T.Bound):
                x, body = T.open_bound(args[0])
                try:
                    r = zz_int(body, x)[0]
                except PolyError:
                    r = None   # 不可积：保持名词
            elif name == "D" and len(args) == 2:
                r = dd(args[0], args[1])
            if r is not None:
                val[u] = r
                changed = True
            elif any(a is not b for a, b in zip(args, u.args)):
                val[u] = T.mk(u.head, args)
            else:
                val[u] = u
        if not changed:
            return f"{to_str(self.current)}   [no inert form evaluated]"
        before = self.current
        self.current = val[self.current]
        self._kernel_step("value", self.current, before=before)
        self._remember(self.current)
        return to_str(self.current)

    def mrefine(self):
        """:refine：账本驱动化简（decide 的第二大消费者）——只重写 decide=YES 的结构，
        判不动的保持原样（永不静默错）。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.refine import refine as zz_refine

        r, changed = zz_refine(self.current, self.ctx)
        if not changed:
            return f"{to_str(self.current)}   [no refinement: ledger decides nothing more]"
        before = self.current
        self.current = r
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:refine", (), before, r, "YES",
            cost(r) - cost(before), note="ledger-driven simplification",
        ))
        self._remember(r)
        return to_str(r)

    def mlatex(self):
        """:latex：当前式的 LaTeX 输出（纯展示层）。"""
        from cas.latex import to_latex

        if self.current is None:
            return "empty session"
        return to_latex(self.current)


def run():
    """REPL：表达式即当前式；%N 复用历史产出；命令转录可保存/回放。
    分发全部走 Session.handle（与回放同路径）。"""
    s = Session()
    print("pyCAS session. :help for commands; expression to make current; %N reuses history.")
    if s.load_error:
        print(f"warning: rules load failed: {s.load_error}")
    while True:
        try:
            line = input(">> ")
        except EOFError:
            break
        if line.strip() in (":q", ":quit"):
            break
        out = s.handle(line)
        if out:
            print(out)


if __name__ == "__main__":
    run()
