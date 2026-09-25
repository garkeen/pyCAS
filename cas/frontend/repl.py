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

from __future__ import annotations

from collections.abc import Sequence
from typing import TypeGuard

from cas.api import (
    Applied,
    ApplyFailed,
    BudgetExceeded,
    CadError,
    DiffError,
    IntegrateError,
    PointCell,
    ScopeError,
    TacticsError,
    apply_rule,
    back_substitute,
    declared_ruleset,
    definite_integrate,
    differentiate,
    differentiate_piecewise,
    domain_normal_form,
    fold,
    format_refutation,
    format_verdict,
    guard_report,
    integrate_term,
    is_piecewise,
    solve_linear_with_condition,
    solve_piecewise,
)
from cas.frontend.parser import parse
from cas.frontend.pprint import pat_to_str, to_str
from cas.frontend.session import CommandHandler, Session
from cas.runtime import bootstrap
from cas.runtime.runtime import Runtime
from cas.syntax import term as T
from cas.syntax.term import Expr, S, Sym, Term
from cas.syntax.termpath import all_paths, replace_at, subst
from cas.workflow.command import (
    BothSides,
    BothSidesPayload,
    Claim,
    CommandName,
    Diff,
    DiffPayload,
    Integrate,
    IntegratePayload,
    Rewrite,
    RewritePayload,
    Solve,
    SolvePayload,
    SplitPayload,
    Subst,
    SubstPayload,
    Trans,
    Use,
    UsePayload,
)
from cas.workflow.states import StepStatus
from cas.workflow.workflow import WorkflowStep


def _fmt(runtime: Runtime, term: Term) -> str:
    """Fold Q arithmetic before display."""
    return to_str(runtime, fold(term))



def _iso_str(cell: PointCell) -> str:
    """Display a point-cell isolating interval."""
    lower, upper = cell.iso
    if lower == upper:
        return str(lower)
    return f"≈({lower}, {upper})"


def _split_top(text: str, separator: str) -> tuple[str, str] | None:
    """Split on the first `sep` found at bracket depth zero.

    Used for the definition and declaration line forms (`u := x^2`, `A : Real`):
    those are surface forms, not terms — a definition is not a term and must not
    be parsed as one.
    """
    depth = 0
    for index, character in enumerate(text):
        if character in "([{":
            depth += 1
        elif character in ")]}":
            depth -= 1
        elif depth == 0 and text.startswith(separator, index):
            return text[:index], text[index + len(separator):]
    return None


def _take_refs(rest: str | None) -> tuple[str, tuple[int, ...]]:
    """Split trailing whole-token ``#N`` references from a command."""
    tokens = (rest or "").split()
    references: list[int] = []
    while tokens and tokens[-1].startswith("#"):
        try:
            references.insert(0, int(tokens.pop()[1:]))
        except ValueError:
            break
    return " ".join(tokens), tuple(references)




def _parse_path(text: str) -> tuple[int, ...]:
    normalized = text.strip()
    if normalized.startswith("(") and normalized.endswith(")"):
        normalized = normalized[1:-1]
    if not normalized:
        return ()
    separator = "," if "," in normalized else "."
    try:
        path = tuple(int(part) for part in normalized.split(separator))
    except ValueError as error:
        raise ValueError("path must contain non-negative integers") from error
    if any(index < 0 for index in path):
        raise ValueError("path must contain non-negative integers")
    return path


def _is_equation(term: Term) -> TypeGuard[Expr]:
    return (
        isinstance(term, Expr)
        and isinstance(term.head, Sym)
        and term.head.name == "Eq"
    )


class REPL:
    def __init__(self, runtime: Runtime) -> None:
        self.session = Session(runtime, self._handler_table())

    def _handler_table(self) -> dict[str, CommandHandler]:
        return {
            "help": lambda _session, text: self.cmd_help(text),
            "quit": lambda _session, text: self.cmd_quit(text),
            "both": lambda _session, text: self.cmd_both(text),
            "norm": lambda _session, text: self.cmd_norm(text),
            "solve": lambda _session, text: self.cmd_solve(text),
            "subst": lambda _session, text: self.cmd_subst(text),
            "split": lambda _session, text: self.cmd_split(text),
            "enter": lambda _session, text: self.cmd_enter(text),
            "merge": lambda _session, text: self.cmd_merge(text),
            "use": lambda _session, text: self.cmd_use(text),
            "trans": lambda _session, text: self.cmd_trans(text),
            "diff": lambda _session, text: self.cmd_diff(text),
            "integrate": lambda _session, text: self.cmd_integrate(text),
            "int": lambda _session, text: self.cmd_int(text),
            "rules": lambda _session, text: self.cmd_rules(text),
            "apply": lambda _session, text: self.cmd_apply(text),
            "check": lambda _session, text: self.cmd_check(text),
            "steps": lambda _session, text: self.cmd_steps(text),
            "show": lambda _session, text: self.cmd_show(text),
            "focus": lambda _session, text: self.cmd_focus(text),
            "undo": lambda _session, text: self.cmd_undo(text),
            "redo": lambda _session, text: self.cmd_redo(text),
        }


    def run(self) -> None:
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
            if cmd in self.session.commands and self._dispatch_command(cmd, rest):
                continue
            self.cmd_claim(line)

    def _dispatch_command(self, command: str, rest: str) -> bool:
        descriptor = self.session.commands.get(command)
        if descriptor is None:
            return False
        descriptor.handler(self.session, rest)
        return True

    def _show_step(self, step: WorkflowStep) -> None:
        command = step.command
        extra = ""
        if command.premises:
            extra = " <-" + ", ".join(
                f"#{premise}" for premise in command.premises
            )
        payload = command.payload
        if (
            command.name is CommandName.BOTH_SIDES
            and isinstance(payload, BothSidesPayload)
        ):
            extra += f" {payload.op}({_fmt(self.session.runtime, payload.operand)})"
        elif command.name is CommandName.REWRITE and isinstance(
            payload,
            RewritePayload,
        ):
            if payload.rule:
                extra += f" rule={payload.rule}"
        elif command.name is CommandName.SUBST and isinstance(
            payload,
            SubstPayload,
        ):
            extra += f" {_fmt(self.session.runtime, payload.var)}={_fmt(self.session.runtime, payload.value)}"
        elif command.name is CommandName.SOLVE and isinstance(
            payload,
            SolvePayload,
        ):
            extra += f" {_fmt(self.session.runtime, payload.var)}={_fmt(self.session.runtime, payload.solution)}"
        elif command.name is CommandName.SPLIT and isinstance(
            payload,
            SplitPayload,
        ):
            extra += (
                f" {'¬' if payload.negate else ''}"
                f"{_fmt(self.session.runtime, payload.condition)}"
            )
        elif command.name is CommandName.USE and isinstance(
            payload,
            UsePayload,
        ):
            extra += f" {payload.direction} at {payload.path}"
        elif command.name is CommandName.TRANS:
            extra += " equality composition"
        elif command.name is CommandName.DIFF and isinstance(
            payload,
            DiffPayload,
        ):
            extra += f" d/d{_fmt(self.session.runtime, payload.var)}"
        elif command.name is CommandName.INTEGRATE and isinstance(
            payload,
            IntegratePayload,
        ):
            word = self.session.runtime.alias_head("integrate")
            symbol = self.session.runtime.binder_print(word) if word is not None else None
            extra += f" {symbol or 'int'}d{_fmt(self.session.runtime, payload.var)}"
            if payload.bounds is not None:
                extra += (
                    f" [{_fmt(self.session.runtime, payload.bounds[0])},"
                    f"{_fmt(self.session.runtime, payload.bounds[1])}]"
                )
        guards = ""
        if step.guards:
            guards = "  | " + ", ".join(_fmt(self.session.runtime, guard) for guard in step.guards)
        domain = f"  ∈{step.domain}" if step.domain else ""
        marker = "*" if step.id == self.session.focus else " "
        print(
            f" {marker}#{step.id:2d} [{step.status.value:4s}] "
            f"{command.name}{extra}{domain}"
        )
        print(f"        {_fmt(self.session.runtime, step.content)}{guards}")
        if step.refutation is not None:
            print(f"        refutation: {format_refutation(step.refutation)}")

    def _step(
        self,
        references: Sequence[int],
        what: str = "work on",
    ) -> WorkflowStep | None:
        """The step a command works on: the explicit `#N`, or else the focus.

        Referencing a step means referencing *its result*: its content is what a
        computation reads, and its judgment is what a verified step may depend on.
        """
        if len(references) > 1:
            print(f"  this command takes one step reference, got {len(references)}")
            return None
        step_id = references[0] if references else self.session.focus
        if step_id is None:
            print(f"  no step to {what} (add a step, or use `focus #N`)")
            return None
        try:
            return self.session.workflow.get(step_id)
        except KeyError:
            print(f"  unknown step: #{step_id}")
            return None

    def _land(self, step: WorkflowStep) -> None:
        """Make the new step the focus and show it. Refusal and undecided are
        reported with their note: they are different outcomes and must not be
        conflated in the display either."""
        self.session.focus = step.id
        if step.status is StepStatus.REFUSED:
            if step.refutation is not None:
                print(f"  step refused: {format_refutation(step.refutation)}")
            else:
                print(f"  step refused: {step.note or 'verification failed'}")
        elif step.status is StepStatus.UNDECIDED:
            print(f"  step undecided: {step.note or 'not re-checked'}")
        self._show_step(step)

    def cmd_help(self, _: str) -> None:
        print("Commands:")
        for descriptor in self.session.commands.values():
            suffix = f" {descriptor.arguments}" if descriptor.arguments else ""
            print(f"  {descriptor.name}{suffix}: {descriptor.help}")

    def cmd_quit(self, _: str) -> None:
        raise SystemExit(0)
    def cmd_claim(self, line: str) -> None:
        try:
            t = parse(self.session.runtime, line)
        except Exception as e:
            print(f"  parse error: {e}")
            return
        s = self.session.workflow.add(t, Claim())
        self.session.focus = s.id
        self._show_step(s)

    def cmd_define(self, name: str, body: str) -> None:
        """`u := <expr>`: a definition, i.e. a predicative alias.

        A definition is not a proposition: its body must not refer to the symbol
        being defined (the alias graph has to stay acyclic), and it is expanded
        automatically — unlike an equation, which enters the scope as an
        assumption and is never expanded.
        """
        try:
            symbol = parse(self.session.runtime, name.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        if not isinstance(symbol, Sym):
            print("  the left-hand side of a definition must be a single symbol")
            return
        try:
            body_t = parse(self.session.runtime, body.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        try:
            self.session.workflow.define(symbol, body_t)
        except ScopeError as e:
            print(f"  definition refused: {e}")
            return
        print(f"  definition {_fmt(self.session.runtime, symbol)} := {_fmt(self.session.runtime, body_t)}")

    def cmd_declare(self, name: str, sort: str) -> None:
        """`A : Real`: declare a symbol's sort. A declaration is not a
        proposition: it records which class the symbol belongs to."""
        try:
            symbol = parse(self.session.runtime, name.strip())
            sort_t = parse(self.session.runtime, sort.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        if not isinstance(symbol, Sym):
            print("  the declared name must be a single symbol")
            return
        try:
            self.session.workflow.declare(symbol, sort_t)
        except ScopeError as e:
            print(f"  declaration refused: {e}")
            return
        print(f"  declared {_fmt(self.session.runtime, symbol)} : {_fmt(self.session.runtime, sort_t)}")

    def cmd_both(self, rest: str) -> None:
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
            operand = parse(self.session.runtime, expr_str)
        except Exception as e:
            print(f"  parse error: {e}")
            return
        equation = pred.content
        if not _is_equation(equation):
            print("  the current step is not an equality")
            return
        lhs, rhs = equation.args
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
        s = self.session.workflow.add(content, BothSides(pred=pred.id, op=op,
                                           operand=operand))
        self._land(s)

    def cmd_norm(self, rest: str) -> None:
        _body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        # compute on the expanded form (aliases are transparent), while the
        # predecessor keeps the form it was written in
        n = domain_normal_form(self.session.runtime, self.session.workflow.expand(pred.content))
        s = self.session.workflow.add(n, Rewrite(pred=pred.id))
        self._land(s)

    def cmd_solve(self, rest: str) -> None:
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        var = S(body.strip())
        try:
            content = self.session.workflow.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        if _is_equation(content) and (
            is_piecewise(content.args[0])
            or is_piecewise(content.args[1])
        ):
            self._solve_piecewise(pred, var, content)
            return
        try:
            sol, condition = solve_linear_with_condition(self.session.runtime, content, var)
        except TacticsError as error:
            print(f"  tactic refused: {error}")
            return
        s = self.session.workflow.add(T.eq(var, sol), Solve(pred=pred.id, var=var,
                                              solution=sol, condition=condition))
        self._land(s)

    def _solve_piecewise(
        self,
        predecessor: WorkflowStep,
        variable: Sym,
        content: Expr,
    ) -> None:
        """Piecewise equation channel: per-branch linear solve plus condition
        adjudication in the tactic layer, with point solutions committed one by one
        (independently verified by the back-substitution judge) and
        region/conditional solutions reported as they are."""
        lhs, rhs = content.args
        if is_piecewise(rhs):
            lhs, rhs = rhs, lhs
        try:
            result = solve_piecewise(self.session.runtime, lhs, variable, rhs)
        except TacticsError as error:
            print(f"  piecewise solve refused: {error}")
            return
        base = predecessor.id
        for solution in result.points:
            step = self.session.workflow.add(
                T.eq(variable, solution),
                Solve(
                    pred=base,
                    var=variable,
                    solution=solution,
                ),
            )
            self._land(step)
        for condition in result.regions:
            print(
                f"  region solution: {_fmt(self.session.runtime, condition)} "
                "(holds identically on that branch)"
            )
        for conditional in result.conditionals:
            rendered = (
                _fmt(self.session.runtime, conditional.solution)
                if conditional.solution is not None
                else "the branch value"
            )
            print(
                f"  conditional solution: x = {rendered} requires "
                f"{_fmt(self.session.runtime, conditional.condition)} (undecided)"
            )
        for refutation in result.refutations:
            print(f"  branch refutation: {format_refutation(refutation)}")
        if not (
            result.points
            or result.regions
            or result.conditionals
        ):
            print(
                "  no solution (every branch candidate was refuted by its "
                "branch condition)"
            )

    def cmd_subst(self, rest: str) -> None:
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
            value = parse(self.session.runtime, val_str.strip())
        except Exception as e:
            print(f"  parse error: {e}")
            return
        substituted = subst(pred.content, {var: value})
        content = domain_normal_form(self.session.runtime, substituted)
        s = self.session.workflow.add(content, Subst(pred=pred.id, var=var,
                                       value=value))
        self._land(s)

    def cmd_split(self, rest: str) -> None:
        body, refs = _take_refs(rest)
        if refs:
            print("  split creates branches from the current scope; use enter to choose one")
            return
        if body.startswith("!"):
            body = body[1:].strip()
        try:
            condition = parse(self.session.runtime, body)
        except Exception as error:
            print(f"  parse error: {error}")
            return
        group = self.session.workflow.split_on(condition)
        self.session.branch_group = group
        print(f"  branch group #{group.id}: + and - scopes are ready")
        print("  use enter + or enter - to choose a branch")

    def cmd_enter(self, rest: str) -> None:
        body = rest.strip()
        if self.session.branch_group is None:
            print("  no branch group; use split first")
            return
        scope: int
        if body in ("+", "-"):
            index = 0 if body == "+" else 1
            scope = self.session.branch_group.cases[index].scope
        else:
            try:
                scope = int(body)
            except ValueError:
                print("  usage: enter + | enter - | enter <scope-id>")
                return
        self.session.workflow.enter(scope)
        print(f"  entered scope {self.session.workflow.scope}")

    def cmd_merge(self, rest: str) -> None:
        _body, refs = _take_refs(rest)
        if self.session.branch_group is None or len(refs) != 2:
            print("  usage: merge #result+ #result- (after split and enter)")
            return
        try:
            results = tuple(self.session.workflow.get(sid) for sid in refs)
            self.session.workflow.enter(self.session.branch_group.parent_lineage)
            result = self.session.workflow.merge_branches(self.session.branch_group,
                                             results[0].content, results)
        except Exception as error:
            print(f"  merge refused: {error}")
            return
        self._land(result)

    def cmd_use(self, rest: str) -> None:
        body, target_refs = _take_refs(rest)
        parts = body.split()
        if len(parts) != 4 or parts[0].startswith("#") is False \
                or parts[1] not in ("->", "<-") or parts[2] != "at":
            print("  usage: use #S (->|<-) at <path> [#T]")
            return
        try:
            source_id = int(parts[0][1:])
            path = _parse_path(parts[3])
            source = self.session.workflow.get(source_id)
        except (ValueError, KeyError):
            print("  invalid source step or path")
            return
        target = self._step(target_refs, what="use")
        if target is None:
            return
        source_equation = source.content
        if not _is_equation(source_equation):
            print("  the use source is not an equality")
            return
        before, after = source_equation.args
        if parts[1] == "<-":
            before, after = after, before
        try:
            content = replace_at(target.content, path, after)
        except (IndexError, TypeError):
            print("  path is outside the target step")
            return
        s = self.session.workflow.add(content, Use(source=source.id, direction=parts[1],
                                    path=path, target=target.id,
                                    premises=(source.id, target.id)))
        self._land(s)

    def cmd_trans(self, rest: str) -> None:
        body, refs = _take_refs(rest)
        if body:
            print("  usage: trans #A #B")
            return
        if len(refs) != 2:
            print("  usage: trans #A #B")
            return
        try:
            first, second = (self.session.workflow.get(sid) for sid in refs)
        except KeyError:
            print("  unknown step")
            return
        first_content = first.content
        second_content = second.content
        if not (
            _is_equation(first_content)
            and _is_equation(second_content)
        ):
            print("  trans requires two equality steps")
            return
        content = T.eq(first_content.args[0], second_content.args[1])
        step = self.session.workflow.add(
            content,
            Trans(
                premises=refs,
                value=(
                    first_content.args[0],
                    first_content.args[1],
                    second_content.args[1],
                ),
            ),
        )
        self._land(step)

    def cmd_diff(self, rest: str) -> None:
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        if _is_equation(pred.content):
            # An equality is not a legal input to diff: differentiating both sides is
            # unsound (the point solution x=3 would "imply" 1=0). Implicit
            # differentiation is a separate command with an explicit dependency
            # declaration, and does not exist yet.
            print("  an equality cannot be differentiated (differentiating both sides is unsound); implicit differentiation is a separate command that does not exist yet")
            return
        var = S(body.strip())
        try:
            src = self.session.workflow.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        if is_piecewise(src):
            self._diff_piecewise(pred, var, src)
            return
        try:
            content = differentiate(self.session.runtime, src, var)
        except DiffError as e:
            print(f"  differentiation refused: {e}")
            return
        s = self.session.workflow.add(content, Diff(pred=pred.id, var=var))
        self._land(s)

    def _diff_piecewise(
        self,
        predecessor: WorkflowStep,
        variable: Sym,
        source: Term,
    ) -> None:
        """Piecewise differentiation channel (cautious): commit the per-branch
        derivative and mark breakpoints as explicitly unverified -- the derivative
        holds on the open cells, while differentiability at a breakpoint needs the
        limit layer, which does not exist yet, and is never faked."""
        try:
            derivative, breakpoints = differentiate_piecewise(self.session.runtime, source, variable)
        except (DiffError, CadError) as error:
            print(f"  piecewise differentiation refused: {error}")
            return
        step = self.session.workflow.add(
            derivative,
            Diff(pred=predecessor.id, var=variable),
        )
        self._land(step)
        if breakpoints:
            points = ", ".join(
                f"x∈[{_iso_str(cell)}]" for cell in breakpoints
            )
            print(
                f"  ⚠ differentiability at the breakpoints {points} is unverified"
                " (it needs continuity and one-sided derivative checks; the "
                "limit layer does not exist yet)"
            )

    def cmd_integrate(self, rest: str) -> None:
        body, refs = _take_refs(rest)
        pred = self._step(refs)
        if pred is None:
            return
        var = S(body.strip())
        try:
            f = self.session.workflow.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        antiderivative_head = self.session.runtime.role_head("antiderivative")
        if antiderivative_head is None:
            print("  the antiderivative role is not declared")
            return
        try:
            G = integrate_term(self.session.runtime, f, var)
        except IntegrateError as e:
            print(f"  integration refused: {e}")
            return
        content = T.eq(T.mk(S(antiderivative_head), (T.mk_bound(var, f),)), G)
        s = self.session.workflow.add(content, Integrate(pred=pred.id, var=var,
                                           antideriv=G))
        self._land(s)

    def cmd_int(self, rest: str) -> None:
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
            a = fold(parse(self.session.runtime, parts[1]))
            b = fold(parse(self.session.runtime, parts[2]))
        except Exception as e:
            print(f"  parse error: {e}")
            return
        try:
            f = self.session.workflow.expand(pred.content)
        except BudgetExceeded as e:
            print(f"  definition expansion refused: {e}")
            return
        try:
            G = integrate_term(self.session.runtime, f, var)
            V = definite_integrate(self.session.runtime, f, var, a, b)
        except IntegrateError as e:
            print(f"  definite integration refused: {e}")
            return
        definite_head = self.session.runtime.role_head("definite_integral")
        if definite_head is None:
            print("  the definite-integral role is not declared")
            return
        content = T.eq(T.mk(S(definite_head), (T.mk_bound(var, f), a, b)), V)
        s = self.session.workflow.add(content, Integrate(pred=pred.id, var=var,
                                           antideriv=G, bounds=(a, b)))
        self._land(s)

    def cmd_rules(self, _: str) -> None:
        rs = declared_ruleset(self.session.runtime)
        if not rs.rules:
            print("  no rules in the runtime declarations")
            return
        for rid, r in rs.rules.items():
            auto = " auto" if r.auto else ""
            guard = f" if {pat_to_str(self.session.runtime, r.guard)}" if r.guard else ""
            print(f"  {rid:18s} {pat_to_str(self.session.runtime, r.pattern)} -> {pat_to_str(self.session.runtime, r.template)}{guard}{auto}")

    def cmd_apply(self, rest: str) -> None:
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
        rule = declared_ruleset(self.session.runtime).rules.get(rid)
        if rule is None:
            print(f"  unknown rule: {rid} (use rules to list them)")
            return
        try:
            src = self.session.workflow.expand(pred.content)
            selected = None if len(parts) == 1 else _parse_path(parts[2])
        except (BudgetExceeded, ValueError) as error:
            print(f"  apply refused: {error}")
            return
        matches: list[tuple[tuple[int, ...], Applied]] = []
        for path in all_paths(src):
            if selected is not None and tuple(path) != selected:
                continue
            result = apply_rule(rule, src, path)
            if isinstance(result, Applied):
                matches.append((tuple(path), result))
            elif isinstance(result, ApplyFailed):
                for refutation in result.refutations:
                    print(f"  rule guard refutation: {format_refutation(refutation)}")
        if selected is not None:
            if not matches:
                print(f"  rule {rid} does not match at {selected}")
                return
            path, applied = matches[0]
            self._land(
                self.session.workflow.add(
                    applied.term,
                    Rewrite(
                        pred=pred.id,
                        rule=rid,
                        path=path,
                        substitution=applied.substitution,
                    ),
                    target=path,
                )
            )
            return
        if not matches:
            print(f"  rule {rid} does not match this step")
            return
        for path, _result in matches:
            print(f"  match at {path}")

    def _problem_of(self, step_id: int) -> WorkflowStep | None:
        """The equation a step's derivation started from.

        The premise edges are walked back to the root and the first equation on
        the way (root first) is the problem a solution answers. This replaces the
        old cached `original` pointer: the answer is derived from the visible
        graph, so an undo can never leave a stale target behind.
        """
        chain: list[WorkflowStep] = []
        seen: set[int] = set()
        current: WorkflowStep | None = self.session.workflow.get(step_id)
        while current is not None and current.id not in seen:
            seen.add(current.id)
            chain.append(current)
            premises = current.command.premises
            current = self.session.workflow.get(premises[0]) if premises else None
        for candidate in reversed(chain):
            if _is_equation(candidate.content):
                return candidate
        return None

    def cmd_check(self, rest: str) -> None:
        _body, refs = _take_refs(rest)
        cur = self._step(refs, what="check")
        if cur is None:
            return
        src = self._problem_of(cur.id)
        if src is None:
            print("  no equation in this step's derivation to check against")
            return
        current_content = cur.content
        if not _is_equation(current_content):
            print("  the checked step is not an equality")
            return
        cl, cr = current_content.args
        if isinstance(cl, Sym) and T.is_num(cr):
            var, val = cl, cr
        elif isinstance(cr, Sym) and T.is_num(cl):
            var, val = cr, cl
        else:
            print("  the checked step is not of the form var = value")
            return
        try:
            equation = self.session.workflow.expand(src.content)
        except BudgetExceeded as error:
            print(f"  definition expansion refused: {error}")
            return
        if not _is_equation(equation):
            print("  the problem equation changed shape after definition expansion")
            return
        print(
            f"  back-substitute: {_fmt(self.session.runtime, equation)} at "
            f"{_fmt(self.session.runtime, var)}={_fmt(self.session.runtime, val)}"
        )
        substitution = back_substitute(self.session.runtime, equation, var, val)
        verdict = substitution.verdict
        if verdict.is_unknown():
            print(
                "        zero test undecided (branch selection or outside the "
                f"domain): {format_verdict(verdict)}; cannot be accepted as verified"
            )
            return
        if verdict.is_no():
            shown = (
                f"= {substitution.exact}"
                if substitution.exact is not None
                else "≠ 0"
            )
            print(f"        {shown} ✗ FAILED: {format_verdict(verdict)}")
            return
        print(
            f"        = "
            f"{substitution.exact if substitution.exact is not None else 0} ✓"
        )
        # Guards go to the decision pipeline as a whole (every predicate head and
        # compound proposition, no whitelist and no silence), decided in the
        # assumptions of the scope the checked step lives in -- the same frame the
        # commit used when it tried to discharge them.
        ok = True
        frame = self.session.workflow.assumptions_of(cur.id)
        for check in guard_report(self.session.runtime, cur.guards, var, val, frame):
            if check.verdict.is_no():
                print(
                    f"        guard failed: {_fmt(self.session.runtime, check.guard)} → "
                    f"{_fmt(self.session.runtime, check.substituted)} ✗ "
                    f"{format_verdict(check.verdict)}"
                )
                ok = False
            elif not check.verdict.is_yes():
                print(
                    f"        guard undecided: {_fmt(self.session.runtime, check.guard)} → "
                    f"{_fmt(self.session.runtime, check.substituted)} ({format_verdict(check.verdict)})"
                )
                ok = False
        if ok:
            print("        every guard passed ✓")
            print("        === VERIFIED ===")
        else:
            print("        a guard failed or is undecided; cannot be accepted as verified")

    def cmd_steps(self, _: str) -> None:
        for s in self.session.workflow.visible_steps():
            self._show_step(s)

    def cmd_show(self, rest: str) -> None:
        _body, refs = _take_refs(rest)
        if not refs:
            print("  usage: show #N")
            return
        for sid in refs:
            try:
                self._show_step(self.session.workflow.get(sid))
            except KeyError:
                print(f"  unknown step: #{sid}")

    def cmd_focus(self, rest: str) -> None:
        _body, refs = _take_refs(rest)
        if not refs:
            if self.session.focus is None:
                print("  no focus")
            else:
                self._show_step(self.session.workflow.get(self.session.focus))
            return
        sid = refs[-1]
        try:
            self.session.workflow.get(sid)
        except KeyError:
            print(f"  unknown step: #{sid}")
            return
        self.session.focus = sid
        self._show_step(self.session.workflow.get(sid))

    def cmd_undo(self, _: str) -> None:
        steps = self.session.workflow.visible_steps()
        if len(steps) <= 1:
            # keep one visible step, so the REPL always has a focus
            print("  already at the first step")
            return
        last = steps[-1]
        # the logs are immutable: the pointer moves back and the scope version
        # recorded at the previous revision becomes current again; no step is
        # deleted
        self.session.workflow.undo()
        visible = self.session.workflow.visible_steps()
        # the focus follows the revision, so it can never point at a step that is
        # no longer in view
        self.session.focus = visible[-1].id
        print(f"  retracted #{last.id}, back at #{self.session.focus}")
        self._show_step(self.session.workflow.get(self.session.focus))

    def cmd_redo(self, _: str) -> None:
        before = self.session.workflow.events.current_revision()
        revision = self.session.workflow.redo()
        if revision == before:
            print("  nothing to redo")
            return
        visible = self.session.workflow.visible_steps()
        # the focus follows the revision, so it can never point at a step that is
        # not in view
        self.session.focus = visible[-1].id if visible else None
        print(f"  redone, back at revision {revision}")
        if self.session.focus is not None:
            self._show_step(self.session.workflow.get(self.session.focus))


def main() -> None:
    # explicit assembly: the entry point constructs a runtime, and import time
    # mutates no global state
    REPL(bootstrap()).run()


if __name__ == "__main__":
    main()
