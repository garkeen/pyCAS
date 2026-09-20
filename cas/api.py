# -*- coding: utf-8 -*-
"""Application facade.

**Frontend may only import `api` / `workflow` / `runtime`.** Previously the
frontend imported seven concrete math modules (`qarith` / `judge` / `tactics` /
`diff` / `cad` / `integrate` / `piecewise`) plus `kernel.verdict` directly,
bypassing that rule. This module is the **single exit** for those facilities; the
gate is `tests/test_v4_invariants.py::test_dependency_frontend_only_api_workflow_runtime`.

The facade only **forwards**: it adds no semantics, caches nothing, and changes no
refusal behaviour. Refusal exceptions (`DiffError` / `IntegrateError` / `CadError` /
`TacticsError`) also leave through here, so the frontend never reaches into
`cas.math.*` for an exception type.

Each math algorithm takes the math context as its first parameter; the facade
supplies the installed runtime's context, because this module is the application's
frontend boundary, not a math algorithm.
"""

from cas.errors import CadError, DiffError, IntegrateError, TacticsError
from cas.kernel.verdict import NO, YES
from cas.math.diff import differentiate as _differentiate
from cas.math.diff import differentiate_piecewise as _differentiate_piecewise
from cas.math.integrate import definite_integrate as _definite_integrate
from cas.math.integrate import integrate_term as _integrate_term
from cas.math.judge import back_substitute as _back_substitute
from cas.math.judge import guard_report as _guard_report
from cas.math.piecewise import is_piecewise
from cas.math.domains.qarith import fold
from cas.math.rules import apply_rule, declared_ruleset as _declared_ruleset
from cas.math.tactics import solve_linear as _solve_linear
from cas.math.tactics import solve_piecewise as _solve_piecewise
from cas.runtime.dispatch import domain_normal_form, get_runtime

__all__ = (
    # verdict singletons (frontend compares read-only, never constructs a verdict)
    "YES", "NO",
    # refusal exceptions
    "DiffError", "IntegrateError", "CadError", "TacticsError",
    # Q literal arithmetic and domain normal form
    "fold", "domain_normal_form",
    # back-substitution judge (verification side; the solver lives in tactics)
    "back_substitute", "guard_report",
    # solving / differentiation / integration / piecewise
    "solve_linear", "solve_piecewise",
    "differentiate", "differentiate_piecewise",
    "integrate_term", "definite_integrate",
    "is_piecewise",
    # declared rules (frontend `rules` / `apply` commands)
    "declared_ruleset", "apply_rule",
)


def back_substitute(eq, var, value):
    """Forward to `cas.math.judge.back_substitute` with the installed context."""
    return _back_substitute(get_runtime().math, eq, var, value)


def guard_report(guards, var, value, assumptions=None):
    """Forward to `cas.math.judge.guard_report` with the installed context.

    The trailing `assumptions` are the caller's scope assumptions; the math context
    is the facade's own business and never appears in the public signature.
    """
    return _guard_report(get_runtime().math, guards, var, value, assumptions)


def solve_linear(content, var):
    """Forward to `cas.math.tactics.solve_linear` with the installed context."""
    return _solve_linear(get_runtime().math, content, var)


def solve_piecewise(f, x, target):
    """Forward to `cas.math.tactics.solve_piecewise` with the installed context."""
    return _solve_piecewise(get_runtime().math, f, x, target)


def differentiate(t, x):
    """Forward to `cas.math.diff.differentiate` with the installed context."""
    return _differentiate(get_runtime().math, t, x)


def differentiate_piecewise(t, x):
    """Forward to `cas.math.diff.differentiate_piecewise` with the installed context."""
    return _differentiate_piecewise(get_runtime().math, t, x)


def integrate_term(f, x):
    """Forward to `cas.math.integrate.integrate_term` with the installed context."""
    return _integrate_term(get_runtime().math, f, x)


def definite_integrate(f, x, a, b):
    """Forward to `cas.math.integrate.definite_integrate` with the installed context."""
    return _definite_integrate(get_runtime().math, f, x, a, b)


def declared_ruleset():
    """Forward to `cas.math.rules.declared_ruleset` with the installed context."""
    return _declared_ruleset(get_runtime().math)
