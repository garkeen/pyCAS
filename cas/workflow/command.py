"""Commands: the shape of a frontend command.

A command is not a kernel primitive and does not form a functionally closed
ADT. It is a single pure-data record: the kind of claim is *declared* by
`checker_id`, and the kernel looks the checker up by id in the registry. A
command carries no verification logic, there are no functional subclasses, and
there is no per-type isinstance mapping table.

The named constructors below keep the old command names so the call surface is
unchanged; the `request` field replaces the former per-type request-head table.
"""

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class Command:
    """One command: claim kind plus payload. Pure data, no methods."""
    name: str                       # command name, recorded in Event.command
    checker_id: str                 # claim kind (a CheckerRegistry key)
    pred: int | None = None         # predecessor step number; None = no predecessor
    request: str = ""               # request head; empty means this step opens no task

    # --- payload: each command uses what it needs, the rest stay None/empty ---
    op: str = ""
    operand: object = None
    var: object = None
    rule: str = ""
    path: tuple = ()
    substitution: object = None
    solution: object = None
    condition: object = None
    negate: bool = False
    value: object = None
    constraint: object = None
    valuation: object = None
    antideriv: object = None
    bounds: object = None
    registers_assumption: bool = False   # Claim: register the proposition as an assumption
    # Branch merge: per-branch conditions, per-branch open guards, and the one
    # proposition each branch answered.
    conditions: tuple = ()
    guards: tuple = ()
    answers: tuple = ()


# ---------------------------------------------------------------------------
# Named constructors: old command names and call surface preserved
# ---------------------------------------------------------------------------

def Claim():
    """Assert into the ledger, with no predecessor. The proposition is
    registered as an assumption of the current scope.

    An assumption is a context entry, not a trusted conclusion; the workflow
    performs the registration and the checker only verifies.
    """
    return Command(name="Claim", checker_id="assumption.entry",
                   registers_assumption=True)


def BothSides(pred, op, operand):
    """Apply the same operation to both sides of an equation.

    Reversible (add/sub, mul/div by a nonzero element) means equivalent;
    irreversible (mul by 0) only implies, and information is lost.
    """
    return Command(name="BothSides", checker_id="both_sides.operate",
                   pred=pred, op=op, operand=operand)


def Rewrite(pred, rule="", path=(), substitution=None):
    """Rewrite: the predecessor's domain normal form (`rule=""`), or one
    instance of a declared rule at `(path, substitution)`.

    The instance data is supplied by the *proposer*; the checker verifies that
    one instance and neither searches paths nor re-runs rule search.
    """
    return Command(name="Rewrite",
                   checker_id="rule.instance" if rule else "equality.normalize",
                   pred=pred, request="Simplify", rule=rule, path=path,
                   substitution=substitution)


def Solve(pred, var, solution):
    """Input an equation, output a solution. `solution` is the certificate the
    solver hands over; the checker only performs back-substitution."""
    return Command(name="Solve", checker_id="solve.back_substitute",
                   pred=pred, request="Solve", var=var, solution=solution)


def Split(pred, condition, negate=False):
    """Split a conditional branch: one disjunctive step becomes two
    (`condition` and `not condition`)."""
    return Command(name="Split", checker_id="branch.split", pred=pred,
                   condition=condition, negate=negate)


def Subst(pred, var, value):
    """Substitution: replace a variable in the predecessor with a value, a
    purely syntactic operation."""
    return Command(name="Subst", checker_id="substitute", pred=pred,
                   request="Simplify", var=var, value=value)


def Diff(pred, var):
    """Differentiate the predecessor expression with respect to `var`.

    An equation is not valid input: differentiating both sides preserves no
    truth (from the point solution `x = 3` one would "derive" `1 = 0`).
    """
    return Command(name="Diff", checker_id="calculus.derivative", pred=pred,
                   request="Differentiate", var=var)


def Integrate(pred, var, antideriv, bounds=None):
    """Integration: find an antiderivative of the predecessor integrand with
    respect to `var`, or a definite integral when `bounds=(a, b)`.

    `antideriv` is the certificate; the checker is independent of the
    integrator and re-checks through the differentiation layer.
    """
    return Command(name="Integrate", checker_id="calculus.antiderivative",
                   pred=pred, request="Integrate", var=var,
                   antideriv=antideriv, bounds=bounds)


def ValuationCheck(constraint, valuation):
    """One valuation of a constraint system.

    The payload is a *certificate* handed over by the solver, not a conclusion;
    the checker re-checks each instance and its vanishing.
    """
    return Command(name="ValuationCheck", checker_id="constraint.satisfied",
                   constraint=constraint, valuation=valuation)
