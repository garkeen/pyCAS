"""pyCAS v3 交互式 REPL。

命令：
  <表达式>           断言方程/表达式入账
  both <op> <expr>   两边施加运算（add/sub/mul/div）
  norm               域标准形重写
  solve <var>        线性求解
  subst <var> = <expr>  代换
  check              回代验证当前解
  steps              列出全部步骤
  undo               撤销最近一步
  quit

运行：python repl.py
"""

import sys
sys.path.insert(0, ".")

from fractions import Fraction as Fr

from cas.term import S, N, Expr, Sym
from cas.parser import parse
from cas.pprint import to_str
from cas.qarith import eval_exact, EvalNumError, fold
from cas.workflow import (Workflow, Claim, BothSides, Rewrite, Solve,
                          Subst, Split, _is_eq, _substitute,
                          _normalize_eq, _coef)
from cas.domains.poly import from_term as poly_from_term
from cas.domains.ratfunc import rf_from_term
from cas.domains.q import Q_RING
from cas import term as T
import library


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
        if isinstance(d, (BothSides, Rewrite, Solve, Subst, Split)):
            extra = f" <-#{d.pred}"
        if isinstance(d, BothSides):
            extra += f" {d.op}({_fmt(d.operand)})"
        if isinstance(d, Subst):
            extra += f" {_fmt(d.var)}={_fmt(d.value)}"
        if isinstance(d, Solve):
            extra += f" {_fmt(d.var)}"
        guards = ""
        if s.guards:
            guards = "  | " + ", ".join(_fmt(g) for g in s.guards)
        print(f"  #{s.id:2d} [{s.status:4s}] {kind}{extra}")
        print(f"        {_fmt(s.content)}{guards}")

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
        if self.current is None:
            print("  无当前步骤")
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
        pred = self.wf.get(self.current)
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
        s = self.wf.add(content, BothSides(pred=self.current, op=op, operand=operand))
        if s.status == "dead":
            print("  步骤 dead：验证失败")
        self.current = s.id
        self._show_step(s)

    def cmd_norm(self, _):
        if self.current is None:
            print("  无当前步骤")
            return
        pred = self.wf.get(self.current)
        n = _normalize_eq(pred.content)
        s = self.wf.add(n, Rewrite(pred=self.current))
        if s.status == "dead":
            print("  步骤 dead：规范化结果不匹配")
        self.current = s.id
        self._show_step(s)

    def cmd_solve(self, rest):
        if self.current is None:
            print("  无当前步骤")
            return
        var = S(rest.strip())
        pred = self.wf.get(self.current)
        if not _is_eq(pred.content):
            print("  当前步骤不是等式")
            return
        lhs, rhs = pred.content.args
        diff = T.plus(lhs, T.neg(rhs))
        # 先试多项式，失败试有理函数（通分后取分子）
        p = poly_from_term(Q_RING, diff, (var,))
        if p is None:
            rf = rf_from_term(Q_RING, diff, (var,))
            if rf is None:
                print("  非多项式且有理函数域不覆盖")
                return
            # 有理方程：num/den = 0 ⟺ num = 0（den ≠ 0 由守卫保证）
            from cas.domains.ratfunc import rf_reduce
            rf = rf_reduce(Q_RING, rf)
            p = rf.num
            if p.is_zero():
                print("  分子恒零：恒等式")
                return
        deg = p.deg_in(0)
        if deg != 1:
            print(f"  {deg} 次方程，当前只支持线性")
            return
        a = _coef(p, 1)
        b = _coef(p, 0)
        if a == 0:
            print("  首项系数为零")
            return
        sol = -b / a
        content = T.eq(var, T.N(sol))
        s = self.wf.add(content, Solve(pred=self.current, var=var))
        if s.status == "dead":
            print("  步骤 dead：求解验证失败")
        self.current = s.id
        self._show_step(s)

    def cmd_subst(self, rest):
        if self.current is None:
            print("  无当前步骤")
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
        pred = self.wf.get(self.current)
        substituted = _substitute(pred.content, var, value)
        content = _normalize_eq(substituted)
        s = self.wf.add(content, Subst(pred=self.current, var=var, value=value))
        if s.status == "dead":
            print("  步骤 dead：代换验证失败")
        self.current = s.id
        self._show_step(s)

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
        if isinstance(cl, Sym) and _is_num(cr):
            var, val = cl, cr
        elif isinstance(cr, Sym) and _is_num(cl):
            var, val = cr, cl
        else:
            print("  当前步骤不是 var = value 形式")
            return
        ol, orr = orig.content.args
        sl = _substitute(ol, var, val)
        sr = _substitute(orr, var, val)
        diff = fold(T.plus(sl, T.neg(sr)))
        try:
            v = eval_exact(diff, {})
            if v == 0:
                print(f"  回代: {_fmt(orig.content)} at {_fmt(var)}={_fmt(val)}")
                print(f"        = 0 ✓")
                ok = True
                for g in cur.guards:
                    gsub = fold(_substitute(g, var, val))
                    if _is_eq(gsub):
                        try:
                            gv = eval_exact(T.plus(gsub.args[0], T.neg(gsub.args[1])), {})
                            head = gsub.head.name
                            if head == "Ne" and gv == 0:
                                print(f"        守卫失败: {_fmt(g)} → {_fmt(gsub)} = 0 ✗")
                                ok = False
                            elif head == "Gt" and not (gv > 0):
                                print(f"        守卫失败: {_fmt(g)} ✗")
                                ok = False
                            elif head == "Ge" and not (gv >= 0):
                                print(f"        守卫失败: {_fmt(g)} ✗")
                                ok = False
                        except EvalNumError:
                            pass
                if ok:
                    print("        守卫全部通过 ✓")
                    print("        === VERIFIED ===")
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
        # 简单实现：移除最后一步，回到前一步
        last = steps[-1]
        # 不真正删除（DAG 不可变），只移动 current 指针
        self.current = last.derivation.pred if hasattr(last.derivation, "pred") else self.current
        if self.current is not None:
            print(f"  撤回 #{last.id}，回到 #{self.current}")
            self._show_step(self.wf.get(self.current))
        else:
            print("  已是最初步骤")


def _is_num(t):
    from cas import term as T
    return T.is_num(t)


if __name__ == "__main__":
    REPL().run()
