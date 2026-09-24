# -*- coding: utf-8 -*-
"""pyCAS interactive REPL.

Surface forms:
  <expr>                a term or equation: claim it (it enters the scope as an
                        assumption; an equation may be self-referential and is
                        never expanded)
  u := <expr>           a definition: a predicative alias, expanded automatically
  A : Real              a declaration of a symbol's sort
  <command> [#N] ...    a command works on the step named by `#N`, or on the focus
                        (the step commands start from) when no reference is given

Commands:
  both <op> <expr>      apply an operation to both sides (add/sub/mul/div)
  norm                  rewrite to the domain normal form
  solve <var>           linear solve (the tactic layer solves, an independent
                        checker decides by back-substitution; a piecewise equation
                        automatically takes the per-branch solve channel)
  subst <var> = <expr>  substitute a variable (the key must be a variable that
                        occurs in the step's content)
  split <cond>          case split (a leading ! takes the negated branch)
  diff <var>            differentiate (an equation is refused: implicit
                        differentiation is a separate command that does not exist
                        yet; a defined symbol is refused as a variable)
  integrate <var>       antiderivative of the step's content
  int <var> <a> <b>     definite integral
  rules                 list the rules declared at runtime
  apply <rid> [#N]      apply the named rule at the first matching position
  check [#N]            verify a step's solution by back-substitution into the
                        equation its derivation started from
  steps                 list the steps in the current view
  show #N               show one step
  focus [#N]            show the focus, or move it to a step
  undo                  move one revision back (nothing is deleted)
  quit

Run: python repl.py
"""

from cas.runtime import bootstrap, get_runtime, new_workflow
from cas.runtime.dispatch import install
from cas.syntax import term as T
from cas.syntax.term import S, Sym, is_eq
from cas.api import (BudgetExceeded, CadError, DiffError, IntegrateError, NO,
                     ScopeError, TacticsError, YES,
                     apply_rule, back_substitute, declared_ruleset,
                     definite_integrate, differentiate, differentiate_piecewise,
                     domain_normal_form, fold, guard_report, integrate_term,
                     is_piecewise, solve_linear_with_condition, solve_piecewise)
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str, pat_to_str
from cas.workflow.command import (Claim, BothSides, Rewrite, Solve,
                                  Subst, Split, Diff, Integrate, Use, Trans)


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


def _split_top(s, sep):
    """Split on the first `sep` found at bracket depth zero.

    Used for the definition and declaration line forms (`u := x^2`, `A : Real`):
    those are surface forms, not terms — a definition is not a term and must not
    be parsed as one.
    """
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            return s[:i], s[i + len(sep):]
    return None


def _take_refs(rest):
    """Split trailing `#N` step references off a command's arguments.

    A reference is recognised only as a whole token, so the number inside an
    expression is never mistaken for one. Returns `(body, refs)`.
    """
    toks = (rest or "").split()
    refs = []
    while toks and toks[-1].startswith("#"):
        try:
            refs.insert(0, int(toks.pop()[1:]))
        except ValueError:
            break
    return " ".join(toks), tuple(refs)




def _parse_path(text):
    text = text.strip()
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1]
    if not text:
        return ()
    separator = "," if "," in text else "."
    try:
        return tuple(int(part) for part in text.split(separator))
    except ValueError:
        raise ValueError("path must contain non-negative integers")
class REPL:
    def __init__(self):
        # the entry point installed the runtime; reaching a REPL before that is
        # a wiring error, and this read reports it instead of assembling behind
        # the caller's back
        get_runtime()
        self.wf = new_workflow()
        # The focus is a *session cursor*: it is the step a command starts from
        # when no explicit `#N` is given. It is not a mathematical dependency —
        # the premises a step actually used are recorded on the step itself.
        self.focus = None
        self.branch_group = None

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
            # surface forms that are not terms: `u := x^2`, `A : Real`
            split = _split_top(line, ":=")
            if split is not None:
                self.cmd_define(*split)
                continue
            split = _split_top(line, ":")
            if split is not None:
                self.cmd_declare(*split)
                continue
            cmd = line.split()[0].lower()
            rest = line[len(cmd):].strip()
            descriptors = get_runtime().commands
            if cmd in descriptors:
                getattr(self, "cmd_" + cmd)(rest)
            else:
                self.cmd_claim(line)

    def _show_step(self, s):
        d = s.command
        extra = ""
        if d.premises:
            extra = " <-" + ", ".join(f"#{p}" for p in d.premises)
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
        elif d.name == "Use":
            extra += f" {d.direction} at {d.path}"
        elif d.name == "Trans":
            extra += " equality composition"
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
        star = "*" if s.id == self.focus else " "
        print(f" {star}#{s.id:2d} [{s.status:4s}] {d.name}{extra}{dom}")
        print(f"        {_fmt(s.content)}{guards}")

    def _step(self, refs, what="work on"):
        """The step a command works on: the explicit `#N`, or else the focus.

        Referencing a step means referencing *its result*: its content is what a
        computation reads, and its judgment is what a verified step may depend on.
        """
        if len(refs) > 1:
            print(f"  this command takes one step reference, got {len(refs)}")
            return None
        sid = refs[0] if refs else self.focus
        if sid is None:
            print(f"  no step to {what} (add a step, or use `focus #N`)")
            return None
        try:
            return self.wf.get(sid)
        except KeyError:
            print(f"  unknown step: #{sid}")
            return None

    def _land(self, s):
        """Make the new step the focus and show it. Refusal and undecided are
        reported with their note: they are different outcomes and must not be
        conflated in the display either."""
        self.focus = s.id
        if s.status == "refused":
            print(f"  step refused: {s.note or 'verification failed'}")
        elif s.status == "undecided":
            print(f"  step undecided: {s.note or 'not re-checked'}")
        self._show_step(s)

    def cmd_help(self, _):
        print("Commands:")
        for name, (help_text, args, _checker_id) in get_runtime().commands.items():
            suffix = f" {args}" if args else ""
            print(f"  {name}{suffix}: {help_text}")

    def cmd_quit(self, _):
        raise SystemExit(0)
    def cmd_claim(self, line):
        try:
            t = parse(line)
        except Exception as e:
            print(f"  parse error: {e}")
            return
        s = self.wf.add(t, Claim())
        self.focus = s.id
        self._show_step(s)

    def cmd_define(self, name, body):
        """`u := <expr>`: a definition, i.e. a predicative alias.

        A definition is not a proposition: its body must not refer to the symbol
        being defined (the alias graph has to stay acyclic), and it is expanded
        automatically — unlike an equation, which enters the scope as an
        assumption and is never expanded.
        """
        try:
            symbol = parse(name.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        if not isinstance(symbol, Sym):
            print("  the left-hand side of a definition must be a single symbol")
            return
        try:
            body_t = parse(body.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        try:
            self.wf.define(symbol, body_t)
        except ScopeError as e:
            print(f"  definition refused: {e}")
            return
        print(f"  definition {_fmt(symbol)} := {_fmt(body_t)}")

    def cmd_declare(self, name, sort):
        """`A : Real`: declare a symbol's sort. A declaration is not a
        proposition: it records which class the symbol belongs to."""
        try:
            symbol = parse(name.strip())
            sort_t = parse(sort.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        if not isinstance(symbol, Sym):
            print("  the declared name must be a single symbol")
            return
        try:
            self.wf.declare(symbol, sort_t)
        except ScopeError as e:
            print(f"  declaration refused: {e}")
            return
        print(f"  declared {_fmt(symbol)} : {_fmt(sort_t)}")

    def cmd_both(self, rest):
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        parts = body.split(None, 1)
        if len(parts) < 2:
            print("  usage: both <op> <expr> [#N]  (op: add/sub/mul/div)")
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
        s = self.wf.add(content, BothSides(pred=pred.id, op=op,
                                           operand=operand))
        self._land(s)

    def cmd_norm(self, rest):
        _body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        # compute on the expanded form (aliases are transparent), while the
        # predecessor keeps the form it was written in
        n = domain_normal_form(self.wf.expand(pred.content))
        s = self.wf.add(n, Rewrite(pred=pred.id))
        self._land(s)

    def cmd_solve(self, rest):
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        var = S(body.strip())
        try:
            content = self.wf.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        if is_eq(content) and (is_piecewise(content.args[0])
                               or is_piecewise(content.args[1])):
            self._solve_piecewise(pred, var, content)
            return
        try:
            sol, condition = solve_linear_with_condition(content, var)
        except TacticsError as error:
            print(f"  tactic refused: {error}")
            return
        s = self.wf.add(T.eq(var, sol), Solve(pred=pred.id, var=var,
                                              solution=sol, condition=condition))
        self._land(s)

    def _solve_piecewise(self, pred, var, content):
        """Piecewise equation channel: per-branch linear solve plus condition
        adjudication in the tactic layer, with point solutions committed one by one
        (independently verified by the back-substitution judge) and
        region/conditional solutions reported as they are."""
        lhs, rhs = content.args
        if is_piecewise(rhs):              # piecewise on the right: flip so it is on the left
            lhs, rhs = rhs, lhs
        try:
            res = solve_piecewise(lhs, var, rhs)
        except TacticsError as e:
            print(f"  piecewise solve refused: {e}")
            return
        base = pred.id
        for sol in res["points"]:
            s = self.wf.add(T.eq(var, sol), Solve(pred=base, var=var,
                                                  solution=sol))
            self._land(s)
        for c in res["regions"]:
            print(f"  region solution: {_fmt(c)} (holds identically on that branch)")
        for sol, c in res["conditional"]:
            so = _fmt(sol) if sol is not None else "the branch value"
            print(f"  conditional solution: x = {so} requires {_fmt(c)} (undecided)")
        if not (res["points"] or res["regions"] or res["conditional"]):
            print("  no solution (every branch candidate was refuted by its branch condition)")

    def cmd_subst(self, rest):
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        if "=" not in body:
            print("  usage: subst <var> = <expr> [#N]")
            return
        var_str, val_str = body.split("=", 1)
        var = S(var_str.strip())
        try:
            value = parse(val_str.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        substituted = T.subst(pred.content, {var: value})
        content = domain_normal_form(substituted)
        s = self.wf.add(content, Subst(pred=pred.id, var=var,
                                       value=value))
        self._land(s)

    def cmd_split(self, rest):
        body, refs = _take_refs(rest)
        if refs:
            print("  split creates branches from the current scope; use enter to choose one")
            return
        if body.startswith("!"):
            body = body[1:].strip()
        try:
            condition = parse(body)
        except Exception as error:
            print(f"  parse error: {error}")
            return
        group = self.wf.split_on(condition)
        self.branch_group = group
        print(f"  branch group #{group.id}: + and - scopes are ready")
        print("  use enter + or enter - to choose a branch")

    def cmd_enter(self, rest):
        body = rest.strip()
        if self.branch_group is None:
            print("  no branch group; use split first")
            return
        if body in ("+", "-"):
            index = 0 if body == "+" else 1
            scope = self.branch_group.cases[index].scope
        else:
            try:
                scope = int(body)
            except ValueError:
                print("  usage: enter + | enter - | enter <scope-id>")
                return
        self.wf.enter(scope)
        print(f"  entered scope {self.wf.scope}")

    def cmd_merge(self, rest):
        _body, refs = _take_refs(rest)
        if self.branch_group is None or len(refs) != 2:
            print("  usage: merge #result+ #result- (after split and enter)")
            return
        try:
            results = tuple(self.wf.get(sid) for sid in refs)
            self.wf.enter(self.branch_group.parent_lineage)
            result = self.wf.merge_branches(self.branch_group,
                                             results[0].content, results)
        except Exception as error:
            print(f"  merge refused: {error}")
            return
        self._land(result)

    def cmd_use(self, rest):
        body, target_refs = _take_refs(rest)
        parts = body.split()
        if len(parts) != 4 or parts[0].startswith("#") is False \
                or parts[1] not in ("->", "<-") or parts[2] != "at":
            print("  usage: use #S (->|<-) at <path> [#T]")
            return
        try:
            source_id = int(parts[0][1:])
            path = _parse_path(parts[3])
            source = self.wf.get(source_id)
        except (ValueError, KeyError):
            print("  invalid source step or path")
            return
        target = self._step(target_refs, what="use")
        if target is None:
            return
        if not is_eq(source.content):
            print("  the use source is not an equality")
            return
        before, after = source.content.args
        if parts[1] == "<-":
            before, after = after, before
        try:
            content = T.replace_at(target.content, path, after)
        except (IndexError, TypeError):
            print("  path is outside the target step")
            return
        s = self.wf.add(content, Use(source=source.id, direction=parts[1],
                                    path=path, target=target.id,
                                    premises=(source.id, target.id)))
        self._land(s)

    def cmd_trans(self, rest):
        body, refs = _take_refs(rest)
        if body:
            print("  usage: trans #A #B")
            return
        if len(refs) != 2:
            print("  usage: trans #A #B")
            return
        try:
            first, second = (self.wf.get(sid) for sid in refs)
        except KeyError:
            print("  unknown step")
            return
        if not (is_eq(first.content) and is_eq(second.content)):
            print("  trans requires two equality steps")
            return
        content = T.eq(first.content.args[0], second.content.args[1])
        s = self.wf.add(content, Trans(premises=refs,
                                       value=(first.content.args[0], first.content.args[1],
                                              second.content.args[1])))
        self._land(s)

    def cmd_diff(self, rest):
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        if is_eq(pred.content):
            # An equality is not a legal input to diff: differentiating both sides is
            # unsound (the point solution x=3 would "imply" 1=0). Implicit
            # differentiation is a separate command with an explicit dependency
            # declaration, and does not exist yet.
            print("  an equality cannot be differentiated (differentiating both sides is unsound); implicit differentiation is a separate command that does not exist yet")
            return
        var = S(body.strip())
        try:
            src = self.wf.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        if is_piecewise(src):
            self._diff_piecewise(pred, var, src)
            return
        try:
            content = differentiate(src, var)
        except DiffError as e:
            print(f"  differentiation refused: {e}")
            return
        s = self.wf.add(content, Diff(pred=pred.id, var=var))
        self._land(s)

    def _diff_piecewise(self, pred, var, src):
        """Piecewise differentiation channel (cautious): commit the per-branch
        derivative and mark breakpoints as explicitly unverified -- the derivative
        holds on the open cells, while differentiability at a breakpoint needs the
        limit layer, which does not exist yet, and is never faked."""
        try:
            deriv, bounds = differentiate_piecewise(src, var)
        except (DiffError, CadError) as e:
            print(f"  piecewise differentiation refused: {e}")
            return
        s = self.wf.add(deriv, Diff(pred=pred.id, var=var))
        self._land(s)
        if bounds:
            pts = ", ".join(f"x∈[{_iso_str(c)}]" for c in bounds)
            print(f"  ⚠ differentiability at the breakpoints {pts} is unverified"
                  " (it needs continuity and one-sided derivative checks; the limit layer does not exist yet)")

    def cmd_integrate(self, rest):
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        var = S(body.strip())
        try:
            f = self.wf.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        try:
            G = integrate_term(f, var)
        except IntegrateError as e:
            print(f"  integration refused: {e}")
            return
        content = T.eq(T.mk(S("Integrate"), (T.mk_bound(var, f),)), G)
        s = self.wf.add(content, Integrate(pred=pred.id, var=var,
                                           antideriv=G))
        self._land(s)

    def cmd_int(self, rest):
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        parts = body.split()
        if len(parts) < 3:
            print("  usage: int <var> <a> <b> [#N]")
            return
        var = S(parts[0])
        try:
            a = fold(parse(parts[1]))
            b = fold(parse(parts[2]))
        except Exception as e:
            print(f"  parse error: {e}")
            return
        try:
            f = self.wf.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        try:
            G = integrate_term(f, var)
            V = definite_integrate(f, var, a, b)
        except IntegrateError as e:
            print(f"  definite integration refused: {e}")
            return
        content = T.eq(T.mk(S("DefIntegrate"), (T.mk_bound(var, f), a, b)), V)
        s = self.wf.add(content, Integrate(pred=pred.id, var=var,
                                           antideriv=G, bounds=(a, b)))
        self._land(s)

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
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        parts = body.split()
        if not parts or (len(parts) != 1 and
                         (len(parts) != 3 or parts[1] != "at")):
            print("  usage: apply <rid> [#N] [at <path>]")
            return
        rid = parts[0]
        rule = declared_ruleset().rules.get(rid)
        if rule is None:
            print(f"  unknown rule: {rid} (use rules to list them)")
            return
        try:
            src = self.wf.expand(pred.content)
            selected = None if len(parts) == 1 else _parse_path(parts[2])
        except (BudgetExceeded, ValueError) as error:
            print(f"  apply refused: {error}")
            return
        matches = []
        for path in T.all_paths(src):
            if selected is not None and tuple(path) != selected:
                continue
            result = apply_rule(rule, src, path)
            if result.ok:
                matches.append((tuple(path), result))
        if selected is not None:
            if not matches:
                print(f"  rule {rid} does not match at {selected}")
                return
            path, result = matches[0]
            self._land(self.wf.add(result.term,
                                    Rewrite(pred=pred.id, rule=rid, path=path,
                                            substitution=result.subst),
                                    target=path))
            return
        if not matches:
            print(f"  rule {rid} does not match this step")
            return
        for path, _result in matches:
            print(f"  match at {path}")

    def _problem_of(self, sid):
        """The equation a step's derivation started from.

        The premise edges are walked back to the root and the first equation on
        the way (root first) is the problem a solution answers. This replaces the
        old cached `original` pointer: the answer is derived from the visible
        graph, so an undo can never leave a stale target behind.
        """
        chain, seen, cur = [], set(), self.wf.get(sid)
        while cur is not None and cur.id not in seen:
            seen.add(cur.id)
            chain.append(cur)
            preds = cur.command.premises
            cur = self.wf.get(preds[0]) if preds else None
        for s in reversed(chain):
            if is_eq(s.content):
                return s
        return None

    def cmd_check(self, rest):
        _body, refs = _take_refs(rest)
        cur = self._step(refs, what="check")
        if cur is None:
            return
        src = self._problem_of(cur.id)
        if src is None:
            print("  no equation in this step's derivation to check against")
            return
        if not is_eq(cur.content):
            print("  the checked step is not an equality")
            return
        cl, cr = cur.content.args
        if isinstance(cl, Sym) and T.is_num(cr):
            var, val = cl, cr
        elif isinstance(cr, Sym) and T.is_num(cl):
            var, val = cr, cl
        else:
            print("  the checked step is not of the form var = value")
            return
        try:
            eq = self.wf.expand(src.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        print(f"  back-substitute: {_fmt(eq)} at {_fmt(var)}={_fmt(val)}")
        # adjudication of both the zero test and the guards belongs to the judge
        # (its only implementation); this command only displays the result
        bs = back_substitute(eq, var, val)
        if bs.zero is None:
            print("        zero test undecided (branch selection or outside the domain); cannot be accepted as verified")
            return
        if bs.zero is False:
            shown = f"= {bs.exact}" if bs.exact is not None else "≠ 0"
            print(f"        {shown} ✗ FAILED")
            return
        print(f"        = {bs.exact if bs.exact is not None else 0} ✓")
        # Guards go to the decision pipeline as a whole (every predicate head and
        # compound proposition, no whitelist and no silence), decided in the
        # assumptions of the scope the checked step lives in -- the same frame the
        # commit used when it tried to discharge them.
        ok = True
        frame = self.wf.assumptions_of(cur.id)
        for c in guard_report(cur.guards, var, val, frame):
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

    def cmd_show(self, rest):
        _body, refs = _take_refs(rest)
        if not refs:
            print("  usage: show #N")
            return
        for sid in refs:
            try:
                self._show_step(self.wf.get(sid))
            except KeyError:
                print(f"  unknown step: #{sid}")

    def cmd_focus(self, rest):
        _body, refs = _take_refs(rest)
        if not refs:
            if self.focus is None:
                print("  no focus")
            else:
                self._show_step(self.wf.get(self.focus))
            return
        sid = refs[-1]
        try:
            self.wf.get(sid)
        except KeyError:
            print(f"  unknown step: #{sid}")
            return
        self.focus = sid
        self._show_step(self.wf.get(sid))

    def cmd_undo(self, _):
        steps = self.wf.visible_steps()
        if len(steps) <= 1:
            # keep one visible step, so the REPL always has a focus
            print("  already at the first step")
            return
        last = steps[-1]
        # the logs are immutable: the pointer moves back and the scope version
        # recorded at the previous revision becomes current again; no step is
        # deleted
        self.wf.undo()
        visible = self.wf.visible_steps()
        # the focus follows the revision, so it can never point at a step that is
        # no longer in view
        self.focus = visible[-1].id
        print(f"  retracted #{last.id}, back at #{self.focus}")
        self._show_step(self.wf.get(self.focus))


def main():
    # explicit assembly: the entry point installs the runtime, and import time
    # mutates no global state
    install(bootstrap())
    REPL().run()


if __name__ == "__main__":
    main()
