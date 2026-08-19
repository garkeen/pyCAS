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
from cas.simplify import simplify, cost
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
    parts = rest.split()
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
            "mat": KernelCmd("show matrix [[a,b],[c,d]]", lambda s, r: s.mat(r.strip())),
            "mdet": KernelCmd("determinant [[a,b],[c,d]]", lambda s, r: s.mdet(r.strip())),
            "mrank": KernelCmd("rank [[a,b],[c,d]]", lambda s, r: s.mrank(r.strip())),
            "minv": KernelCmd("inverse [[a,b],[c,d]]", lambda s, r: s.minv(r.strip())),
            "msolve": KernelCmd("solve system: :msolve [[a,b],[c,d]] [e,f]", _k_msolve),
            "together": KernelCmd("together <expr> (common denominator)", _k_together),
            "collect": KernelCmd("collect <expr> <var>", _k_collect),
            "numerator": KernelCmd("numerator <expr>", _k_num_den("numerator")),
            "denominator": KernelCmd("denominator <expr>", _k_num_den("denominator")),
            "coefficient": KernelCmd("coefficient <expr> <var> [k]", _k_coefficient),
            "solveineq": KernelCmd("solveineq <expr> <op> 0 <var>", _k_solveineq),
        }

    def _check_locked(self):
        if self.locked:
            raise ValueError(f"session locked: {self.locked} (ex falso; undo or start over)")

    def feed(self, s):
        self._check_locked()
        self.current = parse(s)
        self._remember(self.current)
        return self.current

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
        f = parse(s)
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
        f = parse(s)
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

        F = parse(Fs)
        x = parse(xs)
        f = parse(fs)
        return verify(F, x, f, self.budget)

    def solve(self, fs, vs=None):
        from cas.solve import solve

        f = parse(fs)
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

    def _pick_var(self, t):
        for p in T.all_paths(t):
            v = T.term_at(t, p)
            if isinstance(v, T.Sym) and v.name not in ("e", "pi"):
                return v
        return None

    def factor(self, s):
        from cas.factor import factor_str
        from cas.poly import Poly

        t = parse(s)
        x = self._pick_var(t)
        if x is None:
            return "no variable"
        return factor_str(Poly.from_term(t, (x,)))

    def apart(self, num_s, den_s):
        from cas.poly import Poly
        from cas.apart import apart as zz_apart

        t1 = parse(num_s)
        t2 = parse(den_s)
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

        t = parse(s)
        x = self._pick_var(t)
        if x is None:
            return "no variable"
        res, ok, method = zz_int(t, x)
        self._kernel_step(f"integrate[{method}]", res, before=t)
        out = ps(res)
        tag = "VERIFIED" if ok else "UNVERIFIED"
        return f"{out}   [{tag}, method: {method}]"

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

    def commands(self):
        out = {
            ":s": "suggest [path]",
            ":a": "apply <rule-id> [path]",
            ":u": "undo [n]",
            ":auto": "core simplify",
            ":steps": "explain the derivation (rules step-by-step; algorithms by name)",
            ":hist": "produced expressions (%N to reuse, % = latest)",
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


def run():
    """REPL：表达式即当前式；%N 复用历史产出；规则步逐条可解释，
    算法步报算法名与验证态（单算法调用不做微观解释，verify 背书即解释）。"""
    s = Session()
    print("pyCAS session. :help for commands; expression to make current; %N reuses history.")
    if s.load_error:
        print(f"warning: rules load failed: {s.load_error}")
    while True:
        try:
            line = input(">> ").strip()
        except EOFError:
            break
        if not line:
            continue
        if line in (":q", ":quit"):
            break
        try:
            if line == ":help":
                for k, v in s.commands().items():
                    print(f"{k:12s} {v}")
            elif line.startswith(":") and line.split(None, 1)[0][1:] in s.kernel:
                # 内核命令注册表分发（先于前缀匹配，避免 :solve 被 :s 吞掉）
                parts = line.split(None, 1)
                name = parts[0][1:]
                rest = s.expand_history(parts[1].strip()) if len(parts) > 1 else ""
                print(s.kernel[name].fn(s, rest))
            elif line == ":steps":
                for ln in s.steps():
                    print(ln)
            elif line == ":hist":
                for i, h in enumerate(s.history, 1):
                    print(f"%{i}  {to_str(h)}")
                if not s.history:
                    print("(empty)")
            elif line.startswith(":s"):
                arg = line[2:].strip()
                path = tuple(int(i) for i in arg.split(".")) if arg else ()
                for rid, g, d in s.suggest(path):
                    print(f"{rid:20s} guard={g:8s} {('dir=' + d) if d else ''}")
            elif line.startswith(":a "):
                parts = line[3:].split()
                rid = parts[0]
                path = tuple(int(i) for i in parts[1].split(".")) if len(parts) > 1 else None
                n0 = len(s.log)
                res = s.apply(rid, path)
                print(to_str(res) if isinstance(res, T.Term) else res)
                for ln in s.steps()[n0:]:
                    print("  " + ln)   # 规则应用当场给可解释反馈
            elif line.startswith(":u"):
                n = int(line[2:] or 1)
                print(to_str(s.undo(n)) if s.log else "no steps")
            elif line == ":auto":
                n0 = len(s.log)
                print(to_str(s.auto()))
                for ln in s.steps()[n0:]:
                    print("  " + ln)
            elif line.startswith(":assume "):
                print(s.assume(s.expand_history(line[8:])))
            elif line.startswith(":declare "):
                parts = line[9:].split()
                if len(parts) == 2:
                    print(s.declare(parts[0], parts[1]))
                else:
                    print("usage: :declare <var> <property>")
            elif line.startswith(":ans "):
                parts = line[5:].split(None, 1)
                oid = int(parts[0])
                print(s.answer(oid, s.expand_history(parts[1])))
            elif line == ":obls":
                for o in s.obligations:
                    print(f"#{o.oid}  {to_str(o.question)}   affects steps {o.affects}")
                if not s.obligations:
                    print("(none)")
            elif line == ":log":
                for st in s.log:
                    print(f"#{st.sid} {st.rule_id:18s} at {st.path}  {to_str(st.before)}  ->  {to_str(st.after)}")
                if not s.log:
                    print("(no steps)")
            elif line == ":ctx":
                for e in s.ctx.entries:
                    print(f"[{e.kind}:{e.origin}] {to_str(e.fact)}")
                if not s.ctx.entries:
                    print("(empty ledger)")
            elif line == ":load":
                import os

                rd = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
                print(f"loaded {loader.load_dir(rd, s.rules)} rules")
            else:
                s.feed(s.expand_history(line))
                print(s.show())
        except (BudgetExceeded, ParseError) as e:
            print(f"error: {e}")
        except Exception as e:
            print(f"error: {e.__class__.__name__}: {e}")


if __name__ == "__main__":
    run()
