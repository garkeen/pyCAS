# -*- coding: utf-8 -*-
"""pyCAS interactive REPL.

Commands:
  <expression>          assert an equation/expression into the ledger (Claim)
  both <op> <expr>      apply an operation to both sides (add/sub/mul/div)
  norm                  rewrite to the domain normal form
  solve <var>           linear solve (the tactic layer solves, an independent
                        checker decides by back-substitution; a piecewise equation
                        automatically takes the per-branch solve channel, where point
                        solutions are committed and region/conditional solutions are
                        reported as they are)
  subst <var> = <expr>  substitute
  split <cond>          case split (add a <cond> branch; a leading ! takes the negated
                        branch)
  diff <var>            differentiate the current expression in <var> (cross-checked
                        by the domain-layer derivative; piecewise takes the cautious
                        channel and marks breakpoints as unverified; equalities are
                        refused, since implicit differentiation is a separate command
                        that does not exist yet)
  rules                 list the rules declared at runtime
  apply <rid>           apply the named rule
  check                 verify the current solution by back-substitution
  steps                 list the steps in the current view
  undo                  undo the most recent visible step (the event view, the
                        step listing and the scope version move one revision back)
  quit

Run: python repl.py
"""

from cas.runtime import get_runtime, new_workflow
from cas.syntax import term as T
from cas.syntax.term import S, Sym, is_eq
from cas.api import (CadError, DiffError, IntegrateError, NO, TacticsError, YES,
                     apply_rule, back_substitute, declared_ruleset,
                     definite_integrate, differentiate,
                     differentiate_piecewise, domain_normal_form, fold,
                     guard_report, integrate_term, is_piecewise, solve_linear,
                     solve_piecewise)
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str, pat_to_str
from cas.workflow.command import (Claim, BothSides, Rewrite, Solve,
                                  Subst, Split, Diff, Integrate)


def _fmt(t):
    """Fold Q arithmetic before display (Times(-1,2) -> -2 and the like)."""
    return to_str(fold(t))


def _iso_str(cell):
    """Display a point-cell isolating interval: an exact rational root is given
    directly, an irrational root as its isolating interval."""
    a, b = cell.iso
    if a == b:
        return str(a)
    return f"≈({a}, {b})"


class REPL:
    def __init__(self):
        # explicit assembly: the application starts assembly, and import time
        # mutates no global state
        get_runtime()
        self.wf = new_workflow()
        self.current = None
        self.original = None

    def run(self):
        print("pyCAS REPL. Type 'help' for commands.\n")
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
        d = s.command
        extra = ""
        if d.pred is not None:
            extra = f" <-#{d.pred}"
        # display dispatch is on the command's **declared name** (data), never on
        # the type
        if d.name == "BothSides":
            extra += f" {d.op}({_fmt(d.operand)})"
        elif d.name == "Rewrite":
            if d.rule:
                extra += f" rule={d.rule}"
        elif d.name == "Subst":
            extra += f" {_fmt(d.var)}={_fmt(d.value)}"
        elif d.name == "Solve":
            extra += f" {_fmt(d.var)}={_fmt(d.solution)}"
        elif d.name == "Split":
            extra += f" {'¬' if d.negate else ''}{_fmt(d.condition)}"
        elif d.name == "Diff":
            extra += f" d/d{_fmt(d.var)}"
        elif d.name == "Integrate":
            extra += f" ∫d{_fmt(d.var)}"
            if d.bounds is not None:
                extra += f" [{_fmt(d.bounds[0])},{_fmt(d.bounds[1])}]"
        guards = ""
        if s.guards:
            guards = "  | " + ", ".join(_fmt(g) for g in s.guards)
        dom = f"  ∈{s.domain}" if s.domain else ""
        print(f"  #{s.id:2d} [{s.status:4s}] {d.name}{extra}{dom}")
        print(f"        {_fmt(s.content)}{guards}")

    def _cur(self):
        if self.current is None:
            print("  no current step")
            return None
        return self.wf.get(self.current)

    def cmd_help(self, _):
        print(__doc__)

    def cmd_claim(self, line):
        try:
            t = parse(line)
        except Exception as e:
            print(f"  parse error: {e}")
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
            print("  usage: both <op> <expr>  (op: add/sub/mul/div)")
            return
        op, expr_str = parts[0].lower(), parts[1]
        if op not in ("add", "sub", "mul", "div"):
            print(f"  unknown operation: {op}")
            return
        try:
            operand = parse(expr_str)
        except Exception as e:
            print(f"  parse error: {e}")
            return
        if not is_eq(pred.content):
            print("  the current step is not an equality")
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
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'verification failed'}")
        self.current = s.id
        self._show_step(s)

    def cmd_norm(self, _):
        pred = self._cur()
        if pred is None:
            return
        n = domain_normal_form(pred.content)
        s = self.wf.add(n, Rewrite(pred=self.current))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'normal form does not match'}")
        self.current = s.id
        self._show_step(s)

    def cmd_solve(self, rest):
        pred = self._cur()
        if pred is None:
            return
        var = S(rest.strip())
        if is_eq(pred.content) and (is_piecewise(pred.content.args[0])
                                     or is_piecewise(pred.content.args[1])):
            self._solve_piecewise(pred, var)
            return
        try:
            sol = solve_linear(pred.content, var)
        except TacticsError as e:
            print(f"  tactic refused: {e}")
            return
        content = T.eq(var, sol)
        s = self.wf.add(content, Solve(pred=self.current, var=var,
                                       solution=sol))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'rejected by the back-substitution judge'}")
        self.current = s.id
        self._show_step(s)

    def _solve_piecewise(self, pred, var):
        """Piecewise equation channel: per-branch linear solve plus condition
        adjudication in the tactic layer, with point solutions committed one by one
        (independently verified by the back-substitution judge) and
        region/conditional solutions reported as they are."""
        lhs, rhs = pred.content.args
        if is_piecewise(rhs):              # piecewise on the right: flip so it is on the left
            lhs, rhs = rhs, lhs
        try:
            res = solve_piecewise(lhs, var, rhs)
        except TacticsError as e:
            print(f"  piecewise solve refused: {e}")
            return
        base = self.current
        for sol in res["points"]:
            content = T.eq(var, sol)
            s = self.wf.add(content, Solve(pred=base, var=var,
                                           solution=sol))
            if s.status == "refused":
                print(f"  step refuted: {s.note or 'rejected by the back-substitution judge'}")
            self.current = s.id
            self._show_step(s)
        for c in res["regions"]:
            print(f"  region solution: {_fmt(c)} (holds identically on that branch)")
        for sol, c in res["conditional"]:
            so = _fmt(sol) if sol is not None else "the branch value"
            print(f"  conditional solution: x = {so} requires {_fmt(c)} (undecided)")
        if not (res["points"] or res["regions"] or res["conditional"]):
            print("  no solution (every branch candidate was refuted by its branch condition)")

    def cmd_subst(self, rest):
        pred = self._cur()
        if pred is None:
            return
        if "=" not in rest:
            print("  usage: subst <var> = <expr>")
            return
        var_str, val_str = rest.split("=", 1)
        var = S(var_str.strip())
        try:
            value = parse(val_str.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        substituted = T.subst(pred.content, {var: value})
        content = domain_normal_form(substituted)
        s = self.wf.add(content, Subst(pred=self.current, var=var,
                                       value=value))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'substitution verification failed'}")
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
            print(f"  parse error: {e}")
            return
        branch_cond = T.mk(S("Not"), (cond,)) if negate else cond
        content = T.mk(S("And"), (pred.content, branch_cond))
        s = self.wf.add(content, Split(pred=self.current, condition=cond,
                                       negate=negate))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'branch verification failed'}")
        self.current = s.id
        self._show_step(s)

    def cmd_diff(self, rest):
        pred = self._cur()
        if pred is None:
            return
        if is_eq(pred.content):
            # An equality is not a legal input to diff: differentiating both sides is
            # unsound (the point solution x=3 would "imply" 1=0). Implicit
            # differentiation is a separate command with an explicit dependency
            # declaration, and does not exist yet.
            print("  an equality cannot be differentiated (differentiating both sides is unsound); implicit differentiation is a separate command that does not exist yet")
            return
        var = S(rest.strip())
        if is_piecewise(pred.content):
            self._diff_piecewise(pred, var)
            return
        try:
            content = differentiate(pred.content, var)
        except DiffError as e:
            print(f"  differentiation refused: {e}")
            return
        s = self.wf.add(content, Diff(pred=self.current, var=var))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'rejected by the domain-layer derivative cross-check'}")
        self.current = s.id
        self._show_step(s)

    def _diff_piecewise(self, pred, var):
        """Piecewise differentiation channel (cautious): commit the per-branch
        derivative and mark breakpoints as explicitly unverified -- the derivative
        holds on the open cells, while differentiability at a breakpoint needs the
        limit layer, which does not exist yet, and is never faked."""
        try:
            deriv, bounds = differentiate_piecewise(pred.content, var)
        except (DiffError, CadError) as e:
            print(f"  piecewise differentiation refused: {e}")
            return
        s = self.wf.add(deriv, Diff(pred=self.current, var=var))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'rejected by the domain-layer derivative cross-check'}")
        self.current = s.id
        self._show_step(s)
        if bounds:
            pts = ", ".join(f"x∈[{_iso_str(c)}]" for c in bounds)
            print(f"  ⚠ differentiability at the breakpoints {pts} is unverified"
                  " (it needs continuity and one-sided derivative checks; the limit layer does not exist yet)")

    def cmd_integrate(self, rest):
        pred = self._cur()
        if pred is None:
            return
        var = S(rest.strip())
        f = pred.content
        try:
            G = integrate_term(f, var)
        except IntegrateError as e:
            print(f"  integration refused: {e}")
            return
        content = T.eq(T.mk(S("Integrate"), (T.mk_bound(var, f),)), G)
        s = self.wf.add(content, Integrate(pred=self.current, var=var,
                                           antideriv=G))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'rejected by the independent antiderivative verification'}")
        self.current = s.id
        self._show_step(s)

    def cmd_int(self, rest):
        pred = self._cur()
        if pred is None:
            return
        parts = rest.split()
        if len(parts) < 3:
            print("  usage: int <var> <a> <b>")
            return
        var = S(parts[0])
        try:
            a = fold(parse(parts[1]))
            b = fold(parse(parts[2]))
        except Exception as e:
            print(f"  parse error: {e}")
            return
        f = pred.content
        try:
            G = integrate_term(f, var)
            V = definite_integrate(f, var, a, b)
        except IntegrateError as e:
            print(f"  definite integration refused: {e}")
            return
        content = T.eq(T.mk(S("DefIntegrate"), (T.mk_bound(var, f), a, b)), V)
        s = self.wf.add(content, Integrate(pred=self.current, var=var,
                                           antideriv=G, bounds=(a, b)))
        if s.status == "refused":
            print(f"  step refuted: {s.note or 'rejected by the independent definite-integral verification'}")
        self.current = s.id
        self._show_step(s)

    def cmd_rules(self, _):
        rs = declared_ruleset()
        if not rs.rules:
            print("  no rules in the runtime declarations")
            return
        for rid, r in rs.rules.items():
            auto = " auto" if r.auto else ""
            guard = f" if {pat_to_str(r.guard)}" if r.guard else ""
            print(f"  {rid:18s} {pat_to_str(r.pattern)} -> {pat_to_str(r.template)}{guard}{auto}")

    def cmd_apply(self, rest):
        pred = self._cur()
        if pred is None:
            return
        rid = rest.strip()
        rule = declared_ruleset().rules.get(rid)
        if rule is None:
            print(f"  unknown rule: {rid} (use rules to list them)")
            return
        for path in T.all_paths(pred.content):
            res = apply_rule(rule, pred.content, path)
            if res.ok:
                s = self.wf.add(res.term, Rewrite(pred=self.current,
                                                  rule=rid,
                                                  path=tuple(path),
                                                  substitution=res.subst),
                                target=path)
                if s.status == "refused":
                    print(f"  step refuted: {s.note or 'rule output failed re-check'}")
                self.current = s.id
                self._show_step(s)
                return
        print(f"  rule {rid} does not match the current step")

    def cmd_check(self, _):
        if self.original is None or self.current is None:
            print("  no original equation or current step")
            return
        cur = self.wf.get(self.current)
        orig = self.wf.get(self.original)
        if not is_eq(cur.content) or not is_eq(orig.content):
            print("  the current step or the original equation is not an equality")
            return
        cl, cr = cur.content.args
        if isinstance(cl, Sym) and T.is_num(cr):
            var, val = cl, cr
        elif isinstance(cr, Sym) and T.is_num(cl):
            var, val = cr, cl
        else:
            print("  the current step is not of the form var = value")
            return
        print(f"  back-substitute: {_fmt(orig.content)} at {_fmt(var)}={_fmt(val)}")
        # adjudication of both the zero test and the guards belongs to the judge
        # (its only implementation); this command only displays the result
        bs = back_substitute(orig.content, var, val)
        if bs.zero is None:
            print("        zero test undecided (branch selection or outside the domain); cannot be accepted as verified")
            return
        if bs.zero is False:
            shown = f"= {bs.exact}" if bs.exact is not None else "≠ 0"
            print(f"        {shown} ✗ FAILED")
            return
        print(f"        = {bs.exact if bs.exact is not None else 0} ✓")
        # guards go to the decision pipeline as a whole (every predicate head and
        # compound proposition), with no whitelist and no silence
        ok = True
        for c in guard_report(cur.guards, var, val):
            if c.verdict is NO:
                print(f"        guard failed: {_fmt(c.guard)} → {_fmt(c.subst)} ✗")
                ok = False
            elif c.verdict is not YES:
                print(f"        guard undecided: {_fmt(c.guard)} → {_fmt(c.subst)}"
                      f" ({c.verdict})")
                ok = False
        if ok:
            print("        every guard passed ✓")
            print("        === VERIFIED ===")
        else:
            print("        a guard failed or is undecided; cannot be accepted as verified")

    def cmd_steps(self, _):
        for s in self.wf.visible_steps():
            self._show_step(s)

    def cmd_undo(self, _):
        steps = self.wf.visible_steps()
        if len(steps) <= 1:
            # keep one visible step, so the REPL always has a current step
            print("  already at the first step")
            return
        last = steps[-1]
        # the logs are immutable: the pointer moves back and the scope version
        # recorded at the previous revision becomes current again; no step is
        # deleted
        self.wf.undo()
        self.current = self.wf.visible_steps()[-1].id
        print(f"  retracted #{last.id}, back at #{self.current}")
        self._show_step(self.wf.get(self.current))


def main():
    REPL().run()


if __name__ == "__main__":
    main()
