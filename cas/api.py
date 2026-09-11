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
"""

from cas.errors import CadError, DiffError, IntegrateError, TacticsError
from cas.kernel.verdict import NO, YES
from cas.math.diff import differentiate, differentiate_piecewise
from cas.math.integrate import definite_integrate, integrate_term
from cas.math.judge import back_substitute, guard_report
from cas.math.piecewise import is_piecewise
from cas.math.qarith import fold
from cas.math.rules import apply_rule, declared_ruleset
from cas.math.tactics import solve_linear, solve_piecewise
from cas.runtime.dispatch import domain_normal_form

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
