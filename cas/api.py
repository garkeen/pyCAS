"""Application facade with explicit Runtime injection."""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from typing import TypeAlias

from cas.errors import (
    BudgetExceeded,
    CadError,
    DiffError,
    IntegrateError,
    ScopeError,
    TacticsError,
)
from cas.kernel.scope import Assumptions
from cas.kernel.verdict import YES, No, Refutation, Unknown, Verdict
from cas.math.base.equality import normal_form as _normal_form
from cas.math.cad import PointCell
from cas.math.diff import differentiate as _differentiate
from cas.math.diff import differentiate_piecewise as _differentiate_piecewise
from cas.math.domains.qarith import fold
from cas.math.integrate import definite_integrate as _definite_integrate
from cas.math.integrate import integrate_term as _integrate_term
from cas.math.judge import BackSub, GuardCheck
from cas.math.judge import back_substitute as _back_substitute
from cas.math.judge import guard_report as _guard_report
from cas.math.piecewise import is_piecewise
from cas.math.rules import Applied, ApplyFailed, RuleCatalog, apply_rule
from cas.math.rules import declared_ruleset as _declared_ruleset
from cas.math.tactics import PiecewiseSolutions
from cas.math.tactics import solve_linear as _solve_linear
from cas.math.tactics import solve_linear_with_condition as _solve_linear_with_condition
from cas.math.tactics import solve_piecewise as _solve_piecewise
from cas.runtime.runtime import Runtime
from cas.syntax.term import Expr, Sym, Term

AssumptionInput: TypeAlias = Assumptions | Iterable[Term]

__all__ = (
    "YES",
    "format_verdict", "format_refutation",
    "DiffError", "IntegrateError", "CadError", "TacticsError",
    "ScopeError", "BudgetExceeded",
    "fold", "domain_normal_form",
    "back_substitute", "guard_report",
    "solve_linear", "solve_linear_with_condition", "solve_piecewise",
    "differentiate", "differentiate_piecewise",
    "integrate_term", "definite_integrate",
    "is_piecewise",
    "Applied", "ApplyFailed", "PointCell",
    "declared_ruleset", "apply_rule",
)


def back_substitute(
    runtime: Runtime,
    equation: Expr,
    variable: Sym,
    value: Term,
) -> BackSub:
    return _back_substitute(runtime.math, equation, variable, value)


def guard_report(
    runtime: Runtime,
    guards: Sequence[Term],
    variable: Sym,
    value: Term,
    assumptions: AssumptionInput | None = None,
) -> tuple[GuardCheck, ...]:
    frame: Assumptions
    if isinstance(assumptions, Assumptions):
        frame = assumptions
    elif assumptions is None:
        frame = Assumptions()
    else:
        frame = Assumptions(tuple(assumptions))
    return _guard_report(runtime.math, guards, variable, value, frame)


def solve_linear(runtime: Runtime, content: Term, variable: Sym) -> Term:
    return _solve_linear(runtime.math, content, variable)


def solve_linear_with_condition(
    runtime: Runtime,
    content: Term,
    variable: Sym,
) -> tuple[Term, Term]:
    return _solve_linear_with_condition(runtime.math, content, variable)


def solve_piecewise(
    runtime: Runtime,
    function: Term,
    variable: Sym,
    target: Term,
) -> PiecewiseSolutions:
    return _solve_piecewise(runtime.math, function, variable, target)


def differentiate(runtime: Runtime, term: Term, variable: Sym) -> Term:
    return _differentiate(runtime.math, term, variable)


def differentiate_piecewise(
    runtime: Runtime,
    term: Term,
    variable: Sym,
) -> tuple[Term, list[PointCell]]:
    return _differentiate_piecewise(runtime.math, term, variable)


def integrate_term(runtime: Runtime, integrand: Term, variable: Sym) -> Term:
    return _integrate_term(runtime.math, integrand, variable)


def definite_integrate(
    runtime: Runtime,
    integrand: Term,
    variable: Sym,
    lower: Term,
    upper: Term,
) -> Term:
    return _definite_integrate(runtime.math, integrand, variable, lower, upper)


def domain_normal_form(runtime: Runtime, term: Term) -> Term:
    return _normal_form(runtime.math, term)


def format_refutation(refutation: Refutation) -> str:
    witnesses = ", ".join(repr(witness) for witness in refutation.witnesses)
    causes = "; ".join(format_refutation(cause) for cause in refutation.causes)
    return (
        f"channel={refutation.channel.value}; "
        f"proposition={refutation.proposition!r}; "
        f"witnesses=[{witnesses}]; causes=[{causes}]; "
        f"detail={refutation.detail}"
    )


def format_verdict(verdict: Verdict) -> str:
    if verdict.is_yes():
        return "YES"
    if isinstance(verdict, No):
        return f"NO: {format_refutation(verdict.evidence)}"
    if isinstance(verdict, Unknown):
        return f"UNKNOWN[{verdict.reason.value}]"
    raise TypeError("unsupported verdict")


def declared_ruleset(runtime: Runtime) -> RuleCatalog:
    return _declared_ruleset(runtime.math)
