# -*- coding: utf-8 -*-
"""pyCAS v3 交互式 REPL。

命令：
  <表达式>              断言方程/表达式入账（Claim）
  both <op> <expr>      两边施加运算（add/sub/mul/div）
  norm                  域标准形重写
  solve <var>           线性求解（战术层求解，验证器独立回代判定）
  subst <var> = <expr>  代换
  split <cond>          条件切割（加 <cond> 分支；前缀 ! 取否定分支）
  diff <var>            对当前步骤关于 <var> 微分（域层导数交叉验证）
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

from cas import term as T
from cas.term import S, Sym
from cas.parser import parse
from cas.pprint import to_str
from cas.qarith import eval_exact, EvalNumError, fold
from cas.errors import TacticsError
from cas.tactics import solve_linear
from cas.diff import differentiate, DiffError
from cas.decide import decide
from cas.context import Context
from cas.verdict import YES, NO
from cas.workflow import (Workflow, Claim, BothSides, Rewrite, Solve,
                          Subst, Split, Diff, _is_eq, _normalize_eq)


def _fmt(t):
    """显示前 ℚ 折叠（Times(-1,2) → -2 等）。"""
    return to_str(fold(t))


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
        if isinstance(d, (BothSides, Rewrite, Solve, Subst, Split, Diff)):
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
        var = S(rest.strip())
        try:
            if _is_eq(pred.content):
                la, ra = pred.content.args
                content = T.eq(differentiate(la, var),
                               differentiate(ra, var))
            else:
                content = differentiate(pred.content, var)
        except DiffError as e:
            print(f"  微分拒答: {e}")
            return
        s = self.wf.add(content, Diff(pred=self.current, var=var))
        if s.status == "dead":
            print(f"  步骤 dead：{s.note or '域层导数交叉验证否决'}")
        self.current = s.id
        self._show_step(s)

    def cmd_rules(self, _):
        from cas.rules import library_ruleset
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
        from cas.rules import library_ruleset, apply_rule
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
        ol, orr = orig.content.args
        sl = T.subst(ol, {var: val})
        sr = T.subst(orr, {var: val})
        diff = fold(T.plus(sl, T.neg(sr)))
        try:
            v = eval_exact(diff, {})
            if v == 0:
                print(f"  回代: {_fmt(orig.content)} at {_fmt(var)}={_fmt(val)}")
                print(f"        = 0 ✓")
                # 守卫统一交判定管线裁决（全谓词头 + 复合命题），不白名单、不静默
                ok = True
                for g in cur.guards:
                    gsub = fold(T.subst(g, {var: val}))
                    gv = decide(gsub, Context())
                    if gv is NO:
                        print(f"        守卫失败: {_fmt(g)} → {_fmt(gsub)} ✗")
                        ok = False
                    elif gv is not YES:
                        print(f"        守卫未决: {_fmt(g)} → {_fmt(gsub)}（{gv}）")
                        ok = False
                if ok:
                    print("        守卫全部通过 ✓")
                    print("        === VERIFIED ===")
                else:
                    print("        存在失败/未决守卫，不能判定为验证通过")
            else:
                print(f"  回代: {_fmt(orig.content)} at {_fmt(var)}={_fmt(val)}")
                print(f"        = {v} ✗ FAILED")
        except EvalNumError as e:
            print(f"  回代失败: {e}")

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


if __name__ == "__main__":
    REPL().run()
