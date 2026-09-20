"""Domain-condition extraction: the structural channel of the guard system.

Constraints of Power are universal rules of the ring-level syntax (a nonzero
base for a negative integer power, a nonnegative base for a rational power with
an even denominator, ...) and live in the kernel. Constraints of function heads
are declared by the `domain` line of the declaration DSL (carried into the
runtime with the function declaration) and queried at run time, so semantics
belong to declarations and structure belongs to the kernel without mixing. The
declaration lookup arrives as the explicit first argument, a `MathContext`.

Domain conditions have exactly one registration channel: the declaration DSL.
There is no second injection point on the kernel side, because two channels
doing the same thing necessarily diverge and there is no way to tell which one
takes effect.
"""

from cas.syntax import term as T
from cas.syntax.term import S, Int, Rat


def _guarded(cond, guards):
    """Conditionalize a branch guard: `not cond or guard`. The branch is only
    active where cond holds, so its definedness obligation is only owed there."""
    neg = T.mk(S("Not"), (cond,)) if cond is not T.TRUE else T.FALSE
    return [T.mk(S("Or"), (neg, g)) for g in guards]


def dom_condition(ctx, t, out=None):
    """Recursively extract domain constraints, structurally, without deciding
    values.

    Power constraints are universal structural rules: a negative integer power
    a^-k gives a != 0; a rational power a^(p/q) with even q gives a >= 0; a
    negative rational power a^-e gives a > 0 when the denominator is even and
    a != 0 when it is odd. A Piecewise contributes each branch's body
    constraints, conditionalized as `not cond or constraint`; the disjunction
    across branches is handled by the decision layer. Every other function head
    goes through the declaration channel of the given context.
    """
    if out is None:
        out = []
    if isinstance(t, T.Expr):
        name = t.head.name
        if name == "Power":
            b, e = t.args
            if isinstance(e, Int) and e.v < 0:
                out.append(T.mk(S("Ne"), (b, T.ZERO)))
            elif isinstance(e, Rat):
                if e.f >= 0 and e.f.denominator % 2 == 0:
                    out.append(T.mk(S("Ge"), (b, T.ZERO)))
                elif e.f < 0:
                    if e.f.denominator % 2 == 0:
                        out.append(T.mk(S("Gt"), (b, T.ZERO)))
                    else:
                        out.append(T.mk(S("Ne"), (b, T.ZERO)))
        elif name == "Piecewise" and len(t.args) % 2 == 0:
            a = t.args
            for i in range(0, len(a), 2):
                v, c = a[i], a[i + 1]
                body = []
                dom_condition(ctx, v, body)     # the branch body's own constraints, nested included
                out.extend(_guarded(c, body))
            return out                          # conditions are propositions, not value guards
        else:
            fn = ctx.lookup_domain_cond(name)
            if fn is not None:
                out.extend(fn(t))
        for x in t.args:
            dom_condition(ctx, x, out)
    elif isinstance(t, T.Bound):
        dom_condition(ctx, t.body, out)
    return out
