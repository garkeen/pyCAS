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

from __future__ import annotations

from typing import TYPE_CHECKING

from cas.errors import DiffError
from cas.math.domains.qarith import fold
from cas.syntax import term as T
from cas.syntax.term import Bound, Expr, Sym, Term
from cas.syntax.termpath import free_vars, instantiate_de_bruijn

if TYPE_CHECKING:
    from cas.math.cad import PointCell
    from cas.math.context import MathContext


def differentiate(ctx: MathContext, term: Term, variable: Sym) -> Term:
    """Differentiate one term and fold literal arithmetic."""
    return fold(_diff(ctx, term, variable))


def _has(term: Term, variable: Sym) -> bool:
    return variable in free_vars(term)


def _diff(ctx: MathContext, term: Term, variable: Sym) -> Term:
    if T.is_num(term):
        return T.ZERO
    if isinstance(term, Sym):
        return T.ONE if term is variable else T.ZERO
    if isinstance(term, T.Const):
        return T.ZERO
    if isinstance(term, Bound):
        raise DiffError("differentiation inside a binder is not implemented")
    if not isinstance(term, Expr):
        raise DiffError(f"term cannot be differentiated: {term!r}")
    head = term.head.name
    if head == "Plus":
        return T.plus(
            *(_diff(ctx, argument, variable) for argument in term.args)
        )
    if head == "Times":
        parts: list[Term] = []
        for index, argument in enumerate(term.args):
            derivative = _diff(ctx, argument, variable)
            others = [
                term.args[position]
                for position in range(len(term.args))
                if position != index
            ]
            parts.append(T.times(*others, derivative))
        return T.plus(*parts)
    if head == "Power":
        base, exponent = term.args
        base_derivative = _diff(ctx, base, variable)
        exponent_derivative = _diff(ctx, exponent, variable)
        if not _has(exponent, variable):
            return T.times(
                exponent,
                T.pw(base, T.plus(exponent, T.MONE)),
                base_derivative,
            )
        logarithm_head = ctx.role_head("logarithm")
        if logarithm_head is None:
            raise DiffError(
                "logarithm role is not declared: variable-exponent "
                "power cannot be differentiated"
            )
        logarithm = T.call(logarithm_head, base)
        if not _has(base, variable):
            return T.times(term, logarithm, exponent_derivative)
        return T.times(
            term,
            T.plus(
                T.times(exponent_derivative, logarithm),
                T.times(
                    exponent,
                    base_derivative,
                    T.pw(base, T.MONE),
                ),
            ),
        )
    if head in ("Eq", "Ne", "Lt", "Le", "Gt", "Ge", "And", "Or", "Not"):
        raise DiffError("predicates cannot be differentiated")
    if head == "Piecewise":
        raise DiffError(
            "branch-wise differentiation of a piecewise function needs "
            "continuity and one-sided derivative checks at breakpoints, "
            "not implemented"
        )
    template, note = ctx.function_deriv(head)
    if template is None:
        raise DiffError(
            f"{head} has no derivative template"
            + (f" ({note})" if note else "")
        )
    declaration = ctx.lookup_function(head)
    if (
        declaration is not None
        and declaration.arity is not None
        and len(term.args) != declaration.arity
    ):
        raise DiffError(
            f"{head} declares arity {declaration.arity}, got {len(term.args)} arguments"
        )
    if len(term.args) != 1:
        raise DiffError(
            f"differentiation of the multivariate {head} is not implemented"
        )
    argument = term.args[0]
    instantiated = instantiate_de_bruijn(template, argument)
    return T.times(instantiated, _diff(ctx, argument, variable))

def differentiate_piecewise(
    ctx: MathContext,
    term: Term,
    variable: Sym,
) -> tuple[Term, list[PointCell]]:
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
    from cas.math.piecewise import branches, domain_cells, fold_nested, piecewise

    flattened = fold_nested(term)
    derivative = piecewise(
        [(differentiate(ctx, value, variable), condition)
         for value, condition in branches(flattened)]
    )
    breakpoints = [
        cell
        for cell, _value in domain_cells(ctx, flattened, variable)
        if cell.kind == "point"
    ]
    return derivative, breakpoints
