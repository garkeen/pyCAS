"""Domain-condition extraction for the structural guard channel."""

from __future__ import annotations

from typing import TYPE_CHECKING

from cas.syntax import term as T
from cas.syntax.term import Int, Rat, Term

if TYPE_CHECKING:
    from cas.math.context import MathContext


def _guarded(condition: Term, guards: list[Term]) -> list[Term]:
    """Conditionalize a branch guard as ``not condition or guard``."""
    negated = T.mk(T.S("Not"), (condition,)) if condition is not T.TRUE else T.FALSE
    return [T.mk(T.S("Or"), (negated, guard)) for guard in guards]


def dom_condition(
    ctx: MathContext,
    term: Term,
    out: list[Term] | None = None,
) -> list[Term]:
    """Extract structural domain constraints without deciding their truth."""
    result = [] if out is None else out
    if isinstance(term, T.Expr):
        name = term.head.name
        if name == "Power":
            base, exponent = term.args
            if isinstance(exponent, Int) and exponent.v < 0:
                result.append(T.mk(T.S("Ne"), (base, T.ZERO)))
            elif isinstance(exponent, Rat):
                if exponent.f >= 0 and exponent.f.denominator % 2 == 0:
                    result.append(T.mk(T.S("Ge"), (base, T.ZERO)))
                elif exponent.f < 0:
                    if exponent.f.denominator % 2 == 0:
                        result.append(T.mk(T.S("Gt"), (base, T.ZERO)))
                    else:
                        result.append(T.mk(T.S("Ne"), (base, T.ZERO)))
        elif name == "Piecewise" and len(term.args) % 2 == 0:
            arguments = term.args
            for index in range(0, len(arguments), 2):
                value, condition = arguments[index], arguments[index + 1]
                body: list[Term] = []
                dom_condition(ctx, value, body)
                result.extend(_guarded(condition, body))
            return result
        else:
            condition_builder = ctx.lookup_domain_cond(name)
            if condition_builder is not None:
                result.extend(condition_builder(term))
        for argument in term.args:
            dom_condition(ctx, argument, result)
    elif isinstance(term, T.Bound):
        dom_condition(ctx, term.body, result)
    return result
