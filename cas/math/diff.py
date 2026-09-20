"""Structural differentiation over any number-field coefficients and any
declared function domain.

Pure rule recursion, applied repeatedly:
· constants/variables: rational coefficients and named constants differentiate
  to 0, d(x)/dx = 1
· Plus/Times: linearity plus the Leibniz rule
· Power: power rule / exponential rule / general exp-log form
· functions: instantiate the declared derivative template (DB(0) lifted to the
  argument) and multiply by the chain factor

The declaration surface (derivative templates, declared roles, arity) arrives as
the explicit first argument, a `MathContext`; this module holds no handle that
assembly fills in behind its back, so it cannot read semantics it was never given.

Honest boundaries:
· a missing template raises DiffError with the declaration note
· a top-level Piecewise raises DiffError (branch-wise differentiation as a whole
  is unsafe at the breakpoints, see below); the cautious channel
  `differentiate_piecewise` provides branch-wise derivatives with breakpoints
  explicitly marked unverified
· multivariate functions and differentiation inside a binder raise DiffError
  (not implemented)
Results are folded. Term-level output can be cross-checked independently by the
domain-layer derivative (p_deriv / rf_deriv), which is what the workflow's Diff
verifier and the differentiation stress suite do. A piecewise value template
(such as the sign derivative of Abs) stays in the interned term through the chain
rule; when the source is outside the domain the workflow verifier honestly
returns UNKNOWN rather than certifying itself.
"""

from cas.syntax import term as T
from cas.syntax.term import Expr, Sym, Bound
from cas.errors import DiffError
from cas.math.domains.qarith import fold


def differentiate(ctx, t, x: Sym):
    """d(t)/dx: structural recursion plus rule application, then folding."""
    return fold(_diff(ctx, t, x))


def _has(t, x) -> bool:
    return x in T.free_vars(t)


def _diff(ctx, t, x):
    if T.is_num(t):
        return T.ZERO
    if isinstance(t, Sym):
        return T.ONE if t is x else T.ZERO
    if isinstance(t, T.Const):
        return T.ZERO                       # named constants (pi, e, gamma, ...)
    if isinstance(t, Bound):
        raise DiffError("differentiation inside a binder is not implemented")
    if not isinstance(t, Expr):
        raise DiffError(f"term cannot be differentiated: {t!r}")
    head = t.head.name
    if head == "Plus":
        return T.plus(*(_diff(ctx, a, x) for a in t.args))
    if head == "Times":
        # Leibniz: sum over i of a_1...a_{i-1} * da_i * a_{i+1}...a_n
        parts = []
        for i, a in enumerate(t.args):
            da = _diff(ctx, a, x)
            others = [t.args[j] for j in range(len(t.args)) if j != i]
            parts.append(T.times(*others, da))
        return T.plus(*parts)
    if head == "Power":
        b, e = t.args
        db, de = _diff(ctx, b, x), _diff(ctx, e, x)
        if not _has(e, x):
            # power rule: e * b^(e-1) * db (constant exponent, fractional or negative)
            return T.times(e, T.pw(b, T.plus(e, T.MONE)), db)
        # A variable-exponent power needs the logarithm, taken by declared role
        # rather than by hardcoding the Log name. When the role is undeclared
        # this refuses honestly instead of guessing a same-named function.
        log_head = ctx.role_head("logarithm")
        if log_head is None:
            raise DiffError("logarithm role is not declared: variable-exponent "
                            "power cannot be differentiated")
        lnb = T.call(log_head, b)
        if not _has(b, x):
            # exponential rule: b^e * ln(b) * de
            return T.times(t, lnb, de)
        # general case: b^e * (de * ln b + e * db / b)
        return T.times(t, T.plus(T.times(de, lnb),
                                 T.times(e, db, T.pw(b, T.MONE))))
    if head in ("Eq", "Ne", "Lt", "Le", "Gt", "Ge", "And", "Or", "Not"):
        raise DiffError("predicates cannot be differentiated")
    if head == "Piecewise":
        # Branch-wise differentiation is unsafe at breakpoints: derivatives on
        # the two sides need continuity and one-sided derivative checks, and
        # piecing the branch derivatives together is not the whole derivative
        # (for example x^2 for x <= 0 and x for x > 0 gives 0 branch-wise at 0
        # while the two one-sided derivatives differ). The cautious channel is
        # not built here, so this refuses honestly.
        raise DiffError("branch-wise differentiation of a piecewise function "
                        "needs continuity and one-sided derivative checks at "
                        "breakpoints, not implemented")
    # function application: look up the declared derivative template
    tpl, note = ctx.function_deriv(head)
    if tpl is None:
        raise DiffError(f"{head} has no derivative template"
                        + (f" ({note})" if note else ""))
    d = ctx.lookup_function(head)
    if d is not None and d.arity is not None and len(t.args) != d.arity:
        raise DiffError(f"{head} declares arity {d.arity}, got {len(t.args)} arguments")
    if len(t.args) != 1:
        raise DiffError(f"differentiation of the multivariate {head} is not implemented")
    arg = t.args[0]
    inner = T.lift(tpl, arg, 0)            # instantiate DB(0) with the argument
    return T.times(inner, _diff(ctx, arg, x))    # chain rule: template value times inner derivative


def differentiate_piecewise(ctx, t, x: Sym):
    """Cautious piecewise differentiation: differentiate each open cell and mark
    breakpoints as explicitly unverified.

    The derivative only holds on open cells (an open neighbourhood dominated by a
    single branch). Differentiability at a breakpoint needs continuity and
    one-sided derivative checks, which need a limit layer that is not built, so
    breakpoints are listed separately and branch-wise derivatives are never passed
    off as the derivative at a breakpoint.

    Returns (piecewise derivative, list of unverified breakpoint cells). A
    condition that is not a univariate polynomial partition propagates
    cad.CadError.
    """
    from cas.math.piecewise import branches, piecewise, fold_nested, domain_cells
    t = fold_nested(t)
    deriv = piecewise([(differentiate(ctx, v, x), c) for v, c in branches(t)])
    boundaries = [cell for cell, _v in domain_cells(t, x)
                  if cell.kind == "point"]
    return deriv, boundaries
