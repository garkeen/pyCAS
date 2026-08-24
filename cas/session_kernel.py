# -*- coding: utf-8 -*-
"""内核算法命令包装（自 cas/session.py 拆出）：! 前缀自动求解与算法
入口的 Session 方法——solve/factor/apart/线性代数/积分/极限/级数/定积分
+ 名词动词切换（:value 族）+ refine/LaTeX。

Mixin：依赖 SessionBase 提供的状态（current/log/budget/rules）；
组装见 cas/session.py。
"""

from cas import term as T
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify, expand, cost
from cas.rules import Step, apply_rule
from cas.session_cmds import _eval_inert, _const_exact


class KernelOpsMixin:
    def verify(self, Fs, xs, fs):
        from cas.diff import verify

        F = self._parse_in(Fs)
        x = parse(xs)
        f = self._parse_in(fs)
        return verify(F, x, f, self.budget)

    def solve(self, fs, vs=None):
        from cas.solve import solve, check_solution

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
        out = ", ".join(to_str(s_) for s_ in r.solutions) or "(none)"
        # 解代回验证（check_solution 接入管线——此前存在但未被调用）
        tag = None
        if r.solutions:
            checks = [check_solution(f, sol, var) for sol in r.solutions]
            if all(c == "VERIFIED" for c in checks):
                tag = "VERIFIED"
            else:
                bad = sum(1 for c in checks if c != "VERIFIED")
                tag = f"UNVERIFIED ({bad}/{len(checks)} solutions failed substitution)"
        if r.provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in r.provisos) + "]"
        if r.note:
            out += "   [note: " + r.note + "]"
        if tag:
            out += f"   [{tag}]"
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

        m = Matrix.parse(spec)
        inv_m = m.inv()
        if inv_m is None:
            return "singular"
        # 证书检查：M·M^-1 == I（逐项指针比对，驻留免费）
        prod = m.mul(inv_m)
        n = len(m.rows)
        ok = all(prod.rows[i][j] is (T.ONE if i == j else T.ZERO)
                 for i in range(n) for j in range(n))
        return inv_m.show() + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, M*M^-1 = I]"

    def msolve(self, spec, rhs):
        from cas.matrix import Matrix
        from cas.parser import parse
        from cas.pprint import to_str

        b = [parse(c.strip()) for c in rhs.strip()[1:-1].split(",")]
        m = Matrix.parse(spec)
        r = m.solve(b)
        if r.unique is not None:
            # 证书检查：M·x == b（逐行内积代回）
            ok = True
            for i, row in enumerate(m.rows):
                acc = T.ZERO
                for cell, v in zip(row, r.unique):
                    acc = T.plus(acc, T.times(cell, v))
                acc_s = simplify(acc)
                acc_c = _const_exact(acc_s)
                bi_c = _const_exact(b[i])
                if acc_c is not None and bi_c is not None:
                    if acc_c != bi_c:      # Ga 精确等词（P5 注册语义）
                        ok = False
                        break
                elif simplify(acc) is not b[i]:
                    ok = False
                    break
            out = ", ".join(
                f"x{i + 1} = {to_str(_const_exact(v) or simplify(v))}"
                for i, v in enumerate(r.unique)
            )
            return out + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, M*x = b]"
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

        m = Matrix.parse(spec)
        t, lam = m.charpoly()
        r = m.eigenvalues()
        if r.status == "ok":
            # 证书检查：charpoly(lambda_i) == 0（逐个代回 + 展开归零）
            ok = all(
                simplify(expand(T.subst(t, {lam: val}))) is T.ZERO
                for val in r.solutions
            )
            out = ", ".join(to_str(v) for v in r.solutions) or "(none)"
            if r.provisos:
                out += "   [proviso: " + " && ".join(to_str(g) for g in r.provisos) + "]"
            return out + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, charpoly(lambda) = 0]"
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
        """因式分解 + 乘回验证（证书检查：展开积与原式归零比对，比重算更廉价）。"""
        from cas.factor import factor as zz_factor
        from cas.poly import Poly

        t = self._parse_in(s)
        x = self._pick_var(t)
        if x is None:
            return "no variable"
        p = Poly.from_term(t, (x,))
        c, factors = zz_factor(p)
        prod = T.N(c) if c != 1 else T.ONE
        for g, m in factors:
            base = g.to_term()
            for _ in range(m):
                prod = T.times(prod, base)
        ok = simplify(expand(prod)) is t or \
            simplify(T.plus(expand(prod), T.neg(t))) is T.ZERO
        out = []
        if c != 1:
            out.append(str(c))
        for g, m in factors:
            s_ = str(g)
            if "+" in s_ or "-" in s_[1:]:
                s_ = f"({s_})"
            out.append(f"{s_}^{m}" if m > 1 else s_)
        body = " * ".join(out) if out else str(c)
        return f"{body}   [{'VERIFIED' if ok else 'UNVERIFIED'}, method: Zassenhaus]"

    def apart(self, num_s, den_s):
        from cas.poly import Poly
        from cas.apart import apart as zz_apart, apart_term, find_atom
        from cas.pprint import to_str as ps

        t1 = self._parse_in(num_s)
        t2 = self._parse_in(den_s)
        atom = find_atom(t1, t2)
        if atom is not None:
            # 复合项作原子变量（如 Log(x)）：多项式除法推广到非多项式头
            res = apart_term(t1, t2, atom)
            self._kernel_step("apart[composite-atom]", res, before=T.div(t1, t2))
            return ps(res)
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

    def integrate_current(self):
        """对当前惰性积分名词求值（∫f dt 的 f 已含换元变量；等价 :value 的积分分支）。

        与 !integrate <expr> 区分：<expr> 指被积式；此处求值 current 本身。
        """
        from cas.integrate import integrate as zz_int
        from cas.pprint import to_str as ps

        if not (isinstance(self.current, T.Expr) and self.current.head.name == "Integrate"
                and len(self.current.args) == 1 and isinstance(self.current.args[0], T.Bound)):
            return "integrate: current is not an inert integral"
        x, body = T.open_bound(self.current.args[0])
        try:
            res, ok, method, provisos = zz_int(body, x)
        except Exception as e:
            return f"integrate: {type(e).__name__}: {e}"
        self._kernel_step(f"integrate[{method}]", res, before=self.current)
        tag = "VERIFIED" if ok else "UNVERIFIED"
        out = f"{ps(res)}   [{tag}, method: {method}]"
        if provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in provisos) + "]"
        return out

    def integrate(self, s, var_s=None):
        from cas.integrate import integrate as zz_int
        from cas.risch import RischNonElementary
        from cas.pprint import to_str as ps
        from cas.structure import analyze

        t = self._parse_in(s)
        pb = getattr(self, "_principal_branch", None)
        if var_s:
            x = T.S(var_s)
            if x not in T.free_vars(t):
                return f"integrate: variable {var_s} not in expression"
        else:
            vs = sorted(T.free_vars(t), key=lambda v: v.name)
            if len(vs) != 1:
                n = str(len(vs)) if vs else "no"
                return f"integrate: specify the integration variable (expr has {n} free variable)"
            x = vs[0]
        # 统一管线 P1：入口单次结构分析（结果一等对象，随 step log 留痕）
        self._last_analysis = analyze(t, x)
        try:
            res, ok, method, provisos = zz_int(
            t, x, principal=getattr(self, "_principal_branch", None))
        except RischNonElementary as e:
            # Risch 决策程序的证明性拒答——区别于 unsupported 的定理结论
            self._sid += 1
            self.log.append(Step(
                self._sid, "kernel:integrate[risch nonelementary]", (), t, t,
                "YES", 0, note=f"proved: {e.reason}",
            ))
            return f"NOT ELEMENTARY (proved)   [Risch decision: {e.reason}]"
        self._kernel_step(f"integrate[{method}]", res, before=t)
        out = ps(res)
        tag = "VERIFIED" if ok else "UNVERIFIED"
        out = f"{out}   [{tag}, method: {method}]"
        if provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in provisos) + "]"
        return out

    def _limit_probe(self, t, x, pt, claimed):
        """极限数值探针（仅验证/抽查通道，只产一致/未知，绝不产否证）。

        检验收敛趋势（极限定义的数值形态）：双侧误差 |f(a±d)-L| 随 d 缩小
        而缩小。±inf/复杂点不覆盖（返回 False，输出诚实标 UNVERIFIED）。
        """
        import math

        from cas.evalnum import eval_approx

        if T.is_num(pt):
            ptv = float(T.num_val(pt))
        elif isinstance(pt, T.Const) and pt.name in ("pi", "e"):
            ptv = math.pi if pt.name == "pi" else math.e
        elif pt is T.INFINITY or (isinstance(pt, T.Expr) and pt.head.name == "Times"
                                  and any(a is T.INFINITY for a in pt.args)):
            # 无穷远点：大样本收敛趋势（x -> ±大数，误差须缩小）
            sgn = -1.0 if isinstance(pt, T.Expr) and T.MONE in pt.args else 1.0
            try:
                lv2 = eval_approx(claimed, {})
            except Exception:
                return False
            if lv2 is None:
                return False
            errs = []
            for d in (1000.0, 4000.0):
                try:
                    fv = eval_approx(t, {x: sgn * d})
                except Exception:
                    fv = None
                if fv is not None:
                    errs.append(abs(fv - lv2))
            return len(errs) == 2 and errs[1] <= max(errs[0] / 2, 1e-9)
        else:
            return False
        try:
            lv = eval_approx(claimed, {})
        except Exception:
            return False
        if lv is None:
            return False
        agree = 0
        for sgn in (1.0, -1.0):
            errs = []
            for d in (0.125, 0.03125):
                try:
                    fv = eval_approx(t, {x: ptv + sgn * d})
                except Exception:
                    fv = None
                if fv is None:
                    continue
                errs.append(abs(fv - lv))
            if len(errs) == 2 and errs[1] <= max(errs[0] / 2, 1e-9):
                agree += 1
        return agree >= 2

    def mlimit(self, expr_s, var_s, point_s):
        """!limit 入口：三值诚实（UNKNOWN 直接显示，永不静默错）；point 可为 ±inf。

        有限极限附数值探针背书（PROBABLE——采样支持非证明）；探针不覆盖
        或不一致时诚实标 UNVERIFIED。发散结论（±Infinity）无廉价证书，裸输出。
        """
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
        out = to_str(r)
        is_inf = r is T.INFINITY or (isinstance(r, T.Expr) and r.head.name == "Times"
                                     and any(a is T.INFINITY for a in r.args))
        if is_inf:
            return out
        if self._limit_probe(t, T.S(var_s), pt, r):
            return out + "   [PROBABLE, numeric probe]"
        return out + "   [UNVERIFIED]"

    def mseries(self, expr_s, var_s, point_s, order_s):
        """!series 入口：Taylor 展开为截断多项式 + O 项（O 为一等项头）。

        独立验证通道：前若干系数与逐阶导数（diff 引擎）交叉核对——
        级数引擎与微分引擎是两条独立路径，系数 c_k 应等于 f^(k)(a)/k!。
        """
        from cas.series import series, series_term, SeriesError
        from cas.diff import d as _d
        from math import factorial

        t = self._parse_in(expr_s)
        x = T.S(var_s)
        a = parse(point_s)
        n = int(order_s)
        try:
            r = series_term(t, x, a, n)
            k0, coeffs = series(t, x, a, n)
        except SeriesError as e:
            return f"honest refusal: {e}"
        # 交叉核对（最多前 3 个系数，控制成本）
        # 注意：series() 返回的 coeffs 已是 Taylor 系数 c_k = f^(k)(a)/k!，
        # 与 diff 引擎的 f^(k)(a)/k! 直接比对（勿重复除阶乘）
        ok = True
        try:
            for idx, ck in enumerate(coeffs[:3]):
                dk = t
                for _ in range(k0 + idx):
                    dk = _d(dk, x)
                expect = simplify(T.div(T.subst(dk, {x: a}), T.N(factorial(k0 + idx))))
                got = simplify(T.N(ck))
                if simplify(T.plus(expect, T.neg(got))) is not T.ZERO:
                    ok = False
                    break
        except Exception:
            ok = False   # 验证通道自身失败：诚实 UNVERIFIED，不静默
        self._remember(r)
        kmax = k0 + min(3, len(coeffs)) - 1
        return to_str(r) + f"   [{'VERIFIED' if ok else 'UNVERIFIED'}, coeff check k <= {kmax}]"

    def _parse_bound(self, s):
        """限字面量：inf/-inf -> ±Infinity 项，其余按表达式解析。"""
        ps = s.strip().lower()
        if ps in ("inf", "+inf", "infinity", "+infinity"):
            return T.INFINITY
        if ps in ("-inf", "-infinity"):
            return T.neg(T.INFINITY)
        return parse(s)

    def mdefint(self, expr_s, var_s, lo_s, hi_s):
        """!defint 入口：自动正向换元探测 + Newton-Leibniz + 奇点拆分 + 数值交叉核对。"""
        from cas.integrate import defint_auto

        t = self._parse_in(expr_s)
        val, status, note = defint_auto(t, T.S(var_s), self._parse_bound(lo_s), self._parse_bound(hi_s))
        if val is not None:
            self._kernel_step(f"defint[{note}]", val, before=t)
            return f"{to_str(val)}   [{status}, method: {note}]"
        return f"{status}: {note}"

    def value(self):
        """名词 -> 动词：全式求值惰性形式（Quote 脱壳、惰性 Integrate 实算、D 名词微分）。

        求值失败（如不可积）的惰性头保持名词（诚实）。每次求值入账 kernel 步。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        r, changed = _eval_inert(self.current, self.budget)
        if not changed:
            return f"{to_str(self.current)}   [no inert form evaluated]"
        before = self.current
        self.current = r
        self._kernel_step("value", self.current, before=before)
        self._remember(self.current)
        return to_str(self.current)

    def simplify_at(self, path):
        """只化简指定路径的子项，其余子树指针不变（子项操作通道）。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        sub = T.term_at(self.current, path)
        nxt = simplify(sub, self.budget)
        if nxt is sub:
            return f"{to_str(sub)}   [no simplification at path {path}]"
        before = self.current
        self.current = T.replace_at(self.current, path, nxt)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:simplify_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=f"simplify at path {tuple(path)}",
        ))
        self._remember(self.current)
        return to_str(self.current)

    def auto_at(self, path):
        """对指定路径的子项跑自动重写（simplify 不动点 + auto 规则），其余不动。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        sub = T.term_at(self.current, path)
        auto_rules = sorted(
            (r for r in self.rules.rules.values() if r.auto),
            key=lambda r: r.priority,
        )
        seen = {sub._h}
        for _ in range(10):
            s0 = simplify(sub, self.budget)
            if s0 is not sub:
                sub = s0
                seen.add(sub._h)
            changed = False
            for p in T.all_paths(sub):
                for r in auto_rules:
                    res = apply_rule(r, sub, p, self._guard_eval, self.budget)
                    if res.guard == "YES" and res.term._h not in seen \
                            and cost(res.term) <= cost(sub):
                        sub = res.term
                        seen.add(sub._h)
                        changed = True
                        break
                if changed:
                    break
            if not changed:
                break
        if sub is T.term_at(self.current, path):
            return f"{to_str(sub)}   [no auto-rewrite at path {path}]"
        before = self.current
        self.current = T.replace_at(self.current, path, sub)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:auto_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=f"auto at path {tuple(path)}",
        ))
        self._remember(self.current)
        return to_str(self.current)

    def value_at(self, path):
        """只求值指定路径子项中的惰性头（Quote/Integrate/D），其余不动。"""
        self._check_locked()
        if self.current is None:
            return "empty session"
        sub = T.term_at(self.current, path)
        r, changed = _eval_inert(sub, self.budget)
        if not changed:
            return f"{to_str(sub)}   [no inert form at path {path}]"
        before = self.current
        self.current = T.replace_at(self.current, path, r)
        self._sid += 1
        self.log.append(Step(
            self._sid, "scheme:value_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before),
            note=f"evaluate inert forms at path {tuple(path)}",
        ))
        self._remember(self.current)
        return to_str(self.current)

    def integrate_at(self, path):
        """对指定路径子项做积分并原地替换，其余不动。

        子项是惰性 Integrate 名词时求值该积分（点选积分号即算它），
        否则对其做不定积分。两个语义都经既有内核算法 + 验证。
        """
        self._check_locked()
        if self.current is None:
            return "empty session"
        from cas.integrate import integrate as zz_int
        from cas.errors import PolyError
        from cas.risch import RischUnsupported

        sub = T.term_at(self.current, path)
        if isinstance(sub, T.Expr) and sub.head.name == "Integrate" \
                and len(sub.args) == 1 and isinstance(sub.args[0], T.Bound):
            x, body = T.open_bound(sub.args[0])
            try:
                res, ok, method, provisos = zz_int(body, x)
            except (PolyError, RischUnsupported):
                return f"unsupported integrand at path {path}"
            note = f"evaluate Integrate at path {tuple(path)}"
        else:
            x = self._pick_var(sub)
            if x is None:
                return "no variable in subterm"
            try:
                res, ok, method, provisos = zz_int(sub, x)
            except (PolyError, RischUnsupported):
                return f"unsupported integrand at path {path}"
            note = f"algorithm=integrate[{method}] at path {tuple(path)}"
        before = self.current
        self.current = T.replace_at(self.current, path, res)
        self._sid += 1
        self.log.append(Step(
            self._sid, "kernel:integrate_at", tuple(path), before, self.current, "YES",
            cost(self.current) - cost(before), note=note,
        ))
        self._remember(self.current)
        out = f"{to_str(res)}   [{'VERIFIED' if ok else 'UNVERIFIED'}, method: {method}]"
        if provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in provisos) + "]"
        return out

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
