"""Pure command records submitted to the workflow."""

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class Command:
    name: str
    checker_id: str
    premises: tuple = ()
    request: str = ""
    op: str = ""
    operand: object = None
    var: object = None
    rule: str = ""
    path: tuple = ()
    substitution: object = None
    solution: object = None
    condition: object = None
    source: object = None
    direction: str = ""
    target_step: object = None
    negate: bool = False
    value: object = None
    constraint: object = None
    valuation: object = None
    antideriv: object = None
    bounds: object = None
    registers_assumption: bool = False
    conditions: tuple = ()
    guards: tuple = ()
    answers: tuple = ()


def _refs(pred=None, premises=()):
    if premises:
        return tuple(premises)
    return () if pred is None else (pred,)


def Claim():
    return Command(name="Claim", checker_id="assumption.entry",
                   registers_assumption=True)


def BothSides(pred=None, op="", operand=None, premises=()):
    return Command(name="BothSides", checker_id="both_sides.operate",
                   premises=_refs(pred, premises), op=op, operand=operand)


def Rewrite(pred=None, rule="", path=(), substitution=None, premises=()):
    return Command(name="Rewrite",
                   checker_id="rule.instance" if rule else "equality.normalize",
                   premises=_refs(pred, premises), request="Simplify",
                   rule=rule, path=path, substitution=substitution)


def Solve(pred=None, var=None, solution=None, condition=None, premises=()):
    return Command(name="Solve", checker_id="solve.back_substitute",
                   premises=_refs(pred, premises), request="Solve",
                   var=var, solution=solution, condition=condition)


def Split(pred=None, condition=None, negate=False, premises=()):
    return Command(name="Split", checker_id="branch.split",
                   premises=_refs(pred, premises), condition=condition,
                   negate=negate)


def Subst(pred=None, var=None, value=None, premises=()):
    return Command(name="Subst", checker_id="substitute",
                   premises=_refs(pred, premises), request="Simplify",
                   var=var, value=value)


def Diff(pred=None, var=None, premises=()):
    return Command(name="Diff", checker_id="calculus.derivative",
                   premises=_refs(pred, premises), request="Differentiate",
                   var=var)


def Integrate(pred=None, var=None, antideriv=None, bounds=None, premises=()):
    return Command(name="Integrate", checker_id="calculus.antiderivative",
                   premises=_refs(pred, premises), request="Integrate",
                   var=var, antideriv=antideriv, bounds=bounds)


def Use(source=None, direction="", path=(), target=None, premises=()):
    return Command(name="Use", checker_id="congruence.lift",
                   premises=_refs(premises=premises), source=source,
                   direction=direction, path=tuple(path), target_step=target)


def Trans(pred=None, premises=(), value=None):
    return Command(name="Trans", checker_id="equality.trans",
                   premises=_refs(pred, premises), value=value)


def ValuationCheck(constraint, valuation):
    return Command(name="ValuationCheck", checker_id="constraint.satisfied",
                   constraint=constraint, valuation=valuation)
