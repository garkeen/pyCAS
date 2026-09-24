"""Typed workflow command envelopes and closed payload variants.

Commands are frontend/workflow input DTOs, not mathematical Steps. They
construct a `StepProposal` and its checker evidence; the kernel never dispatches
on a command class. Each command payload declares only the fields legal for that
operation, so an operation cannot be constructed with an unrelated field.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from typing import Mapping, TypeAlias

from cas.syntax.pattern import PatternSubstitution
from cas.syntax.term import Sym, Term
from cas.workflow.constraint import Constraint


class CommandName(StrEnum):
    CLAIM = "Claim"
    BOTH_SIDES = "BothSides"
    REWRITE = "Rewrite"
    SOLVE = "Solve"
    SPLIT = "Split"
    SUBST = "Subst"
    DIFF = "Diff"
    INTEGRATE = "Integrate"
    USE = "Use"
    TRANS = "Trans"
    VALUATION_CHECK = "ValuationCheck"
    MERGE_BRANCHES = "MergeBranches"


class Operation(StrEnum):
    ADD = "add"
    SUB = "sub"
    MUL = "mul"
    DIV = "div"


class Direction(StrEnum):
    RIGHT = "->"
    LEFT = "<-"


@dataclass(frozen=True, slots=True)
class TaskSpec:
    head: str
    argument: Term | None = None


@dataclass(frozen=True, slots=True)
class ClaimPayload:
    pass


@dataclass(frozen=True, slots=True)
class BothSidesPayload:
    op: Operation
    operand: Term


@dataclass(frozen=True, slots=True)
class RewritePayload:
    rule: str = ""
    path: tuple[int, ...] = ()
    substitution: PatternSubstitution | None = None


@dataclass(frozen=True, slots=True)
class SolvePayload:
    var: Sym
    solution: Term
    condition: Term | None = None


@dataclass(frozen=True, slots=True)
class SplitPayload:
    condition: Term
    negate: bool = False


@dataclass(frozen=True, slots=True)
class SubstPayload:
    var: Sym
    value: Term


@dataclass(frozen=True, slots=True)
class DiffPayload:
    var: Sym


@dataclass(frozen=True, slots=True)
class IntegratePayload:
    var: Sym
    antideriv: Term
    bounds: tuple[Term, Term] | None = None


@dataclass(frozen=True, slots=True)
class UsePayload:
    source: int
    direction: Direction
    path: tuple[int, ...]
    target: int


@dataclass(frozen=True, slots=True)
class TransPayload:
    value: tuple[Term, Term, Term]


@dataclass(frozen=True, slots=True)
class ValuationPayload:
    constraint: Constraint
    valuation: Mapping[Term, Term]


@dataclass(frozen=True, slots=True)
class MergePayload:
    conditions: tuple[Term, ...]
    guards: tuple[tuple[Term, ...], ...]
    answers: tuple[Term, ...]


CommandPayload: TypeAlias = (
    ClaimPayload
    | BothSidesPayload
    | RewritePayload
    | SolvePayload
    | SplitPayload
    | SubstPayload
    | DiffPayload
    | IntegratePayload
    | UsePayload
    | TransPayload
    | ValuationPayload
    | MergePayload
)


@dataclass(frozen=True, slots=True)
class Command:
    """A typed operation submitted to the workflow.

    `payload` is opaque to the kernel and is interpreted only by the checker
    selected by `checker_id`. The envelope contains no unrelated optional
    operation fields.
    """

    name: CommandName
    checker_id: str
    premises: tuple[int, ...]
    payload: CommandPayload
    task: TaskSpec | None = None
    registers_assumption: bool = False

    @property
    def request(self) -> str:
        """Compatibility read-only view of the task head, not a payload field."""
        return self.task.head if self.task is not None else ""

    @property
    def var(self) -> Term | None:
        """Compatibility read-only view of a task argument."""
        return self.task.argument if self.task is not None else None


def _refs(pred: int | None = None, premises: tuple[int, ...] = ()) -> tuple[int, ...]:
    if premises:
        return tuple(premises)
    return () if pred is None else (pred,)


def Claim() -> Command:
    return Command(
        name=CommandName.CLAIM,
        checker_id="assumption.entry",
        premises=(),
        payload=ClaimPayload(),
        registers_assumption=True,
    )


def BothSides(pred: int | None = None, op: str = "", operand: Term | None = None,
              premises: tuple[int, ...] = ()) -> Command:
    if operand is None:
        raise ValueError("both_sides requires an operand")
    return Command(
        name=CommandName.BOTH_SIDES,
        checker_id="both_sides.operate",
        premises=_refs(pred, premises),
        payload=BothSidesPayload(Operation(op), operand),
    )


def Rewrite(pred: int | None = None, rule: str = "",
            path: tuple[int, ...] = (),
            substitution: PatternSubstitution | None = None,
            premises: tuple[int, ...] = ()) -> Command:
    return Command(
        name=CommandName.REWRITE,
        checker_id="rule.instance" if rule else "equality.normalize",
        premises=_refs(pred, premises),
        payload=RewritePayload(rule, tuple(path), substitution),
        task=TaskSpec("Simplify"),
    )


def Solve(pred: int | None = None, var: Sym | None = None,
           solution: Term | None = None, condition: Term | None = None,
           premises: tuple[int, ...] = ()) -> Command:
    if var is None or solution is None:
        raise ValueError("solve requires a variable and a candidate")
    return Command(
        name=CommandName.SOLVE,
        checker_id="solve.back_substitute",
        premises=_refs(pred, premises),
        payload=SolvePayload(var, solution, condition),
        task=TaskSpec("Solve", var),
    )


def Split(pred: int | None = None, condition: Term | None = None,
          negate: bool = False, premises: tuple[int, ...] = ()) -> Command:
    if condition is None:
        raise ValueError("split requires a condition")
    return Command(
        name=CommandName.SPLIT,
        checker_id="branch.split",
        premises=_refs(pred, premises),
        payload=SplitPayload(condition, negate),
    )


def Subst(pred: int | None = None, var: Sym | None = None,
          value: Term | None = None, premises: tuple[int, ...] = ()) -> Command:
    if var is None or value is None:
        raise ValueError("substitution requires a variable and value")
    return Command(
        name=CommandName.SUBST,
        checker_id="substitute",
        premises=_refs(pred, premises),
        payload=SubstPayload(var, value),
        task=TaskSpec("Simplify", var),
    )


def Diff(pred: int | None = None, var: Sym | None = None,
         premises: tuple[int, ...] = ()) -> Command:
    if var is None:
        raise ValueError("differentiation requires a variable")
    return Command(
        name=CommandName.DIFF,
        checker_id="calculus.derivative",
        premises=_refs(pred, premises),
        payload=DiffPayload(var),
        task=TaskSpec("Differentiate", var),
    )


def Integrate(pred: int | None = None, var: Sym | None = None,
              antideriv: Term | None = None,
              bounds: tuple[Term, Term] | None = None,
              premises: tuple[int, ...] = ()) -> Command:
    if var is None or antideriv is None:
        raise ValueError("integration requires a variable and candidate")
    return Command(
        name=CommandName.INTEGRATE,
        checker_id="calculus.antiderivative",
        premises=_refs(pred, premises),
        payload=IntegratePayload(var, antideriv, bounds),
        task=TaskSpec("Integrate", var),
    )


def Use(source: int | None = None, direction: str = "",
         path: tuple[int, ...] = (), target: int | None = None,
         premises: tuple[int, ...] = ()) -> Command:
    if source is None or target is None:
        raise ValueError("use requires source and target steps")
    return Command(
        name=CommandName.USE,
        checker_id="congruence.lift",
        premises=_refs(premises=premises),
        payload=UsePayload(source, Direction(direction), tuple(path), target),
    )


def Trans(pred: int | None = None, premises: tuple[int, ...] = (),
          value: tuple[Term, Term, Term] | None = None) -> Command:
    if value is None:
        raise ValueError("trans requires a three-term certificate")
    return Command(
        name=CommandName.TRANS,
        checker_id="equality.trans",
        premises=_refs(pred, premises),
        payload=TransPayload(value),
    )


def ValuationCheck(constraint: Constraint, valuation: Mapping[Term, Term]) -> Command:
    return Command(
        name=CommandName.VALUATION_CHECK,
        checker_id="constraint.satisfied",
        premises=(),
        payload=ValuationPayload(constraint, valuation),
    )


def MergeBranches(conditions: tuple[Term, ...],
                  guards: tuple[tuple[Term, ...], ...],
                  answers: tuple[Term, ...]) -> Command:
    return Command(
        name=CommandName.MERGE_BRANCHES,
        checker_id="branch.merge",
        premises=(),
        payload=MergePayload(conditions, guards, answers),
    )
