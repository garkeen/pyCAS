# -*- coding: utf-8 -*-
"""pyCAS v3 交互式 REPL。

命令：
  <表达式>              断言方程/表达式入账（Claim）
  both <op> <expr>      两边施加运算（add/sub/mul/div）
  norm                  域标准形重写
  solve <var>           线性求解（战术层求解，验证器独立回代判定；分段
                        方程自动走逐支求解通道：点解入账、区域解/条件解如实报告）
  subst <var> = <expr>  代换
  split <cond>          条件切割（加 <cond> 分支；前缀 ! 取否定分支）
  diff <var>            对当前表达式关于 <var> 微分（域层导数交叉验证；分段
                        自动走审慎通道，分段点显式标注未验证；等式拒答——
                        隐函数求导为独立命令，未建）
  rules                 列出图书馆规则
  apply <rid>           应用指定图书馆规则
  check                 回代验证当前解
  steps                 列出全部步骤
  undo                  撤销最近一步（仅回退指针）
  quit

运行：python repl.py
"""

import sys
sys.path.insert(0, ".")

from cas.syntax import term as T
from cas.syntax.term import S, Sym
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.qarith import fold
from cas.math.judge import back_substitute, guard_report
from cas.errors import TacticsError
from cas.math.tactics import solve_linear, solve_piecewise
from cas.math.diff import differentiate, DiffError, differentiate_piecewise
from cas.math.cad import CadError
from cas.math.integrate import integrate_term, definite_integrate, IntegrateError
from cas.math.piecewise import is_piecewise
from cas.kernel.verdict import YES, NO
from cas.workflow.workflow import (Workflow, Claim, BothSides, Rewrite, Solve,
                          Subst, Split, Diff, Integrate, _is_eq, _normalize_eq)


def _fmt(t):
    """显示前 ℚ 折叠（Times(-1,2) → -2 等）。"""
    return to_str(fold(t))


def _iso_str(cell):
    """点胞腔隔离区间的显示：精确有理根直接给出，无理根给隔离区间。"""
    a, b = cell.iso
    if a == b:
        return str(a)
    return f"≈({a}, {b})"


class REPL:
    def __init__(self):
        self.wf = Workflow()
        self.current = None
        self.original = None

    def run(self):
        print("pyCAS v3 REPL. 输入 'help' 查看命令。\n")
        while True:
            try:
                line = input("> ").strip()
            except (EOFError, KeyboardInterrupt):
                print()
                break
            if not line:
                continue
            cmd = line.split()[0].lower()
            rest = line[len(cmd):].strip()
            handlers = {
                "help": self.cmd_help,
                "both": self.cmd_both,
                "norm": self.cmd_norm,
                "solve": self.cmd_solve,
                "subst": self.cmd_subst,
                "split": self.cmd_split,
                "diff": self.cmd_diff,
                "integrate": self.cmd_integrate,
                "int": self.cmd_int,
                "rules": self.cmd_rules,
                "apply": self.cmd_apply,
                "check": self.cmd_check,
                "steps": self.cmd_steps,
                "undo": self.cmd_undo,
                "quit": lambda r: exit(0),
            }
            if cmd in handlers:
                handlers[cmd](rest)
            else:
                self.cmd_claim(line)

    def _show_step(self, s):
        d = s.derivation
        kind = type(d).__name__
        extra = ""
        if isinstance(d, (BothSides, Rewrite, Solve, Subst, Split, Diff, Integrate)):
            extra = f" <-#{d.pred}"
        if isinstance(d, BothSides):
            extra += f" {d.op}({_fmt(d.operand)})"
        if isinstance(d, Rewrite) and d.rule:
            extra += f" rule={d.rule}"
        if isinstance(d, Subst):
            extra += f" {_fmt(d.var)}={_fmt(d.value)}"
        if isinstance(d, Solve):
            extra += f" {_fmt(d.var)}={_fmt(d.solution)}"
        if isinstance(d, Split):
            extra += f" {'¬' if d.negate else ''}{_fmt(d.condition)}"
        if isinstance(d, Diff):
            extra += f" d/d{_fmt(d.var)}"
        if isinstance(d, Integrate):
            extra += f" ∫d{_fmt(d.var)}"
            if d.bounds is not None:
                extra += f" [{_fmt(d.bounds[0])},{_fmt(d.bounds[1])}]"
        guards = ""
        if s.guards:
            guards = "  | " + ", ".join(_fmt(g) for g in s.guards)
        dom = f"  ∈{s.domain}" if s.domain else ""
        print(f"  #{s.id:2d} [{s.status:4s}] {kind}{extra}{dom}")
        print(f"        {_fmt(s.content)}{guards}")

    def _cur(self):
        if self.current is None:
            print("  无当前步骤")
            return None
        return self.wf.get(self.current)

    def cmd_help(self, _):
        print(__doc__)

    def cmd_claim(self, line):
        try:
            t = parse(line)
        except Exception as e:
            print(f"  解析错误: {e}")
            return
        s = self.wf.add(t, Claim())
        if self.original is None:
            self.original = s.id
        self.current = s.id
        self._show_step(s)

    def cmd_both(self, rest):
        pred = self._cur()
        if pred is None:
            return
        parts = rest.split(None, 1)
        if len(parts) < 2:
            print("  用法: both <op> <expr>  (op: add/sub/mul/div)")
            return
        op, expr_str = parts[0].lower(), parts[1]
        if op not in ("add", "sub", "mul", "div"):
            print(f"  未知运算: {op}")
            return
        try:
            operand = parse(expr_str)
        except Exception as e:
            print(f"  解析错误: {e}")
            return
        if not _is_eq(pred.content):
            print("  当前步骤不是等式")
            return
        lhs, rhs = pred.content.args
        if op == "add":
            nl, nr = T.plus(lhs, operand), T.plus(rhs, operand)
        elif op == "sub":
            nl, nr = T.plus(lhs, T.neg(operand)), T.plus(rhs, T.neg(operand))
        elif op == "mul":
            nl, nr = T.times(lhs, operand), T.times(rhs, operand)
        else:
            nl = T.times(lhs, T.pw(operand, T.N(-1)))
            nr = T.times(rhs, T.pw(operand, T.N(-1)))
        content = T.eq(nl, nr)
        s = self.wf.add(content, BothSides(pred=self.current, op=op,
                                           operand=operand))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '验证失败'}")
        self.current = s.id
        self._show_step(s)

    def cmd_norm(self, _):
        pred = self._cur()
        if pred is None:
            return
        n = _normalize_eq(pred.content)
        s = self.wf.add(n, Rewrite(pred=self.current))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '规范化结果不匹配'}")
        self.current = s.id
        self._show_step(s)

    def cmd_solve(self, rest):
        pred = self._cur()
        if pred is None:
            return
        var = S(rest.strip())
        if _is_eq(pred.content) and (is_piecewise(pred.content.args[0])
                                     or is_piecewise(pred.content.args[1])):
            self._solve_piecewise(pred, var)
            return
        try:
            sol = solve_linear(pred.content, var)
        except TacticsError as e:
            print(f"  战术拒答: {e}")
            return
        content = T.eq(var, sol)
        s = self.wf.add(content, Solve(pred=self.current, var=var,
                                       solution=sol))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '回代判官否决'}")
        self.current = s.id
        self._show_step(s)

    def _solve_piecewise(self, pred, var):
        """分段方程求解通道：逐支线性求解 + 条件裁决（战术层），
        点解逐个入账（回代判官独立验证），区域解/条件解如实报告。"""
        lhs, rhs = pred.content.args
        if is_piecewise(rhs):              # 分段在右侧：翻转保持分段在左
            lhs, rhs = rhs, lhs
        try:
            res = solve_piecewise(lhs, var, rhs)
        except TacticsError as e:
            print(f"  分段求解拒答: {e}")
            return
        base = self.current
        for sol in res["points"]:
            content = T.eq(var, sol)
            s = self.wf.add(content, Solve(pred=base, var=var,
                                           solution=sol))
            if s.status == "dead":
                print(f"  步骤 dead：{s.note or '回代判官否决'}")
            self.current = s.id
            self._show_step(s)
        for c in res["regions"]:
            print(f"  区域解: {_fmt(c)}（该支上恒成立）")
        for sol, c in res["conditional"]:
            so = _fmt(sol) if sol is not None else "该支值"
            print(f"  条件解: x = {so} 需 {_fmt(c)}（未决）")
        if not (res["points"] or res["regions"] or res["conditional"]):
            print("  无解（各支候选均被分支条件否决）")

    def cmd_subst(self, rest):
        pred = self._cur()
        if pred is None:
            return
        if "=" not in rest:
            print("  用法: subst <var> = <expr>")
            return
        var_str, val_str = rest.split("=", 1)
        var = S(var_str.strip())
        try:
            value = parse(val_str.strip())
        except Exception as e:
            print(f"  解析错误: {e}")
            return
        substituted = T.subst(pred.content, {var: value})
        content = _normalize_eq(substituted)
        s = self.wf.add(content, Subst(pred=self.current, var=var,
                                       value=value))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '代换验证失败'}")
        self.current = s.id
        self._show_step(s)

    def cmd_split(self, rest):
        pred = self._cur()
        if pred is None:
            return
        negate = rest.startswith("!")
        cond_str = rest[1:].strip() if negate else rest
        try:
            cond = parse(cond_str)
        except Exception as e:
            print(f"  解析错误: {e}")
            return
        branch_cond = T.mk(S("Not"), (cond,)) if negate else cond
        content = T.mk(S("And"), (pred.content, branch_cond))
        s = self.wf.add(content, Split(pred=self.current, condition=cond,
                                       negate=negate))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '分支验证失败'}")
        self.current = s.id
        self._show_step(s)

    def cmd_diff(self, rest):
        pred = self._cur()
        if pred is None:
            return
        if _is_eq(pred.content):
            # 等式不是 diff 的合法输入：两边求导不保真（点解方程 x=3 会
            # "推出" 1=0）。隐函数求导是带依赖声明的独立命令（未建）。
            print("  等式不可求导（两边求导不保真）；隐函数求导为独立命令（未建）")
            return
        var = S(rest.strip())
        if is_piecewise(pred.content):
            self._diff_piecewise(pred, var)
            return
        try:
            content = differentiate(pred.content, var)
        except DiffError as e:
            print(f"  微分拒答: {e}")
            return
        s = self.wf.add(content, Diff(pred=self.current, var=var))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '域层导数交叉验证否决'}")
        self.current = s.id
        self._show_step(s)

    def _diff_piecewise(self, pred, var):
        """分段求导通道（审慎）：逐支求导入账，分段点显式标注未验证——
        开区间胞腔上导数成立，分段点可导性须极限层（未建），绝不冒充。"""
        try:
            deriv, bounds = differentiate_piecewise(pred.content, var)
        except (DiffError, CadError) as e:
            print(f"  分段微分拒答: {e}")
            return
        s = self.wf.add(deriv, Diff(pred=self.current, var=var))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '域层导数交叉验证否决'}")
        self.current = s.id
        self._show_step(s)
        if bounds:
            pts = ", ".join(f"x∈[{_iso_str(c)}]" for c in bounds)
            print(f"  ⚠ 分段点 {pts} 处的可导性未验证"
                  "（需连续性与单侧导数校验，极限层未建）")

    def cmd_integrate(self, rest):
        pred = self._cur()
        if pred is None:
            return
        var = S(rest.strip())
        f = pred.content
        try:
            G = integrate_term(f, var)
        except IntegrateError as e:
            print(f"  积分拒答: {e}")
            return
        content = T.eq(T.mk(S("Integrate"), (T.mk_bound(var, f),)), G)
        s = self.wf.add(content, Integrate(pred=self.current, var=var,
                                           antideriv=G))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '原函数独立验证否决'}")
        self.current = s.id
        self._show_step(s)

    def cmd_int(self, rest):
        pred = self._cur()
        if pred is None:
            return
        parts = rest.split()
        if len(parts) < 3:
            print("  用法: int <var> <a> <b>")
            return
        var = S(parts[0])
        try:
            a = fold(parse(parts[1]))
            b = fold(parse(parts[2]))
        except Exception as e:
            print(f"  解析错误: {e}")
            return
        f = pred.content
        try:
            G = integrate_term(f, var)
            V = definite_integrate(f, var, a, b)
        except IntegrateError as e:
            print(f"  定积分拒答: {e}")
            return
        content = T.eq(T.mk(S("DefIntegrate"), (T.mk_bound(var, f), a, b)), V)
        s = self.wf.add(content, Integrate(pred=self.current, var=var,
                                           antideriv=G, bounds=(a, b)))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '定积分独立验证否决'}")
        self.current = s.id
        self._show_step(s)

    def cmd_rules(self, _):
        from cas.math.rules import library_ruleset
        rs = library_ruleset()
        if not rs.rules:
            print("  图书馆无规则")
            return
        for rid, r in rs.rules.items():
            auto = " auto" if r.auto else ""
            guard = f" if {to_str(r.guard)}" if r.guard else ""
            print(f"  {rid:18s} {to_str(r.pattern)} -> {to_str(r.template)}{guard}{auto}")

    def cmd_apply(self, rest):
        pred = self._cur()
        if pred is None:
            return
        rid = rest.strip()
        from cas.math.rules import library_ruleset, apply_rule
        rule = library_ruleset().rules.get(rid)
        if rule is None:
            print(f"  未知规则: {rid}（rules 查看清单）")
            return
        for path in T.all_paths(pred.content):
            res = apply_rule(rule, pred.content, path)
            if res.ok:
                s = self.wf.add(res.term, Rewrite(pred=self.current,
                                                  rule=rid),
                                target=path)
                if s.status == "dead":
                    print(f"  步骤 dead：{s.note or '规则产物复核失败'}")
                self.current = s.id
                self._show_step(s)
                return
        print(f"  规则 {rid} 不匹配当前步骤")

    def cmd_check(self, _):
        if self.original is None or self.current is None:
            print("  无原始方程或当前步骤")
            return
        cur = self.wf.get(self.current)
        orig = self.wf.get(self.original)
        if not _is_eq(cur.content) or not _is_eq(orig.content):
            print("  当前步骤或原始方程不是等式")
            return
        cl, cr = cur.content.args
        if isinstance(cl, Sym) and T.is_num(cr):
            var, val = cl, cr
        elif isinstance(cr, Sym) and T.is_num(cl):
            var, val = cr, cl
        else:
            print("  当前步骤不是 var = value 形式")
            return
        print(f"  回代: {_fmt(orig.content)} at {_fmt(var)}={_fmt(val)}")
        # 判零与守卫的裁决权在 cas/judge（唯一实现），此处只做展示
        bs = back_substitute(orig.content, var, val)
        if bs.zero is None:
            print("        判零未决（选支/域外），不能判定为验证通过")
            return
        if bs.zero is False:
            shown = f"= {bs.exact}" if bs.exact is not None else "≠ 0"
            print(f"        {shown} ✗ FAILED")
            return
        print(f"        = {bs.exact if bs.exact is not None else 0} ✓")
        # 守卫统一交判定管线裁决（全谓词头 + 复合命题），不白名单、不静默
        ok = True
        for c in guard_report(cur.guards, var, val):
            if c.verdict is NO:
                print(f"        守卫失败: {_fmt(c.guard)} → {_fmt(c.subst)} ✗")
                ok = False
            elif c.verdict is not YES:
                print(f"        守卫未决: {_fmt(c.guard)} → {_fmt(c.subst)}"
                      f"（{c.verdict}）")
                ok = False
        if ok:
            print("        守卫全部通过 ✓")
            print("        === VERIFIED ===")
        else:
            print("        存在失败/未决守卫，不能判定为验证通过")

    def cmd_steps(self, _):
        for s in self.wf.all_steps():
            self._show_step(s)

    def cmd_undo(self, _):
        steps = self.wf.all_steps()
        if len(steps) <= 1:
            print("  已是最初步骤")
            return
        last = steps[-1]
        # DAG 不可变：只回退指针，不删除步骤
        self.current = getattr(last.derivation, "pred", None)
        if self.current is not None:
            print(f"  撤回 #{last.id}，回到 #{self.current}")
            self._show_step(self.wf.get(self.current))
        else:
            print("  已是最初步骤")


def main():
    REPL().run()


if __name__ == "__main__":
    main()
