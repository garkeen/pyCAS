"""Piecewise syntax container with ordered first-match evaluation.

``Piecewise(v1, c1, v2, c2, ...)`` is interned syntax, not a numeric domain.
The first branch whose condition is proved true supplies the value.  A TRUE
condition is the else branch and later branches are unreachable.  Operations
lift pointwise by Cartesian branch expansion; differentiation and integration
retain their separate breakpoint cautions.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeAlias, TypeGuard

from cas.errors import BudgetExceeded, PiecewiseError
from cas.kernel.scope import Assumptions
from cas.kernel.verdict import (
    YES,
    No,
    Reason,
    Refutation,
    RefutationChannel,
    Unknown,
    Verdict,
    refute,
    unknown,
)
from cas.math.cad import Cell, PointCell, resolve_partition
from cas.math.decide import decide
from cas.math.project import Projected, project
from cas.math.realroot import RootInterval
from cas.syntax import term as T
from cas.syntax.term import Expr, S, Sym, Term

if TYPE_CHECKING:
    from cas.math.context import MathContext

_HEAD = "Piecewise"
Branch: TypeAlias = tuple[Term, Term]
DomainCell: TypeAlias = tuple[Cell, Term]


@dataclass(frozen=True, slots=True)
class SelectedValue:
    """A uniquely selected branch value and discarded branch evidence."""

    value: Term
    refutations: tuple[Refutation, ...] = ()


@dataclass(frozen=True, slots=True)
class ResidualSelection:
    """An earlier undecided condition leaves a residual suffix."""

    residual: Term
    reason: Reason
    refutations: tuple[Refutation, ...] = ()


Selection: TypeAlias = SelectedValue | ResidualSelection


@dataclass(frozen=True, slots=True)
class OverlapCheck:
    """Order-independence verdict for one pair of branches."""

    first: int
    second: int
    verdict: Verdict


# ---------------------------------------------------------------------------
# Construction and decomposition
# ---------------------------------------------------------------------------


def is_piecewise(term: Term) -> TypeGuard[Expr]:
    return (
        isinstance(term, Expr)
        and term.head.name == _HEAD
        and len(term.args) % 2 == 0
    )


def piecewise(pairs: Iterable[Branch]) -> Term:
    """Build an interned Piecewise after syntax-only normalization."""
    kept: list[Branch] = []
    for value, condition in pairs:
        if condition is T.FALSE:
            continue
        kept.append((value, condition))
        if condition is T.TRUE:
            break
    if not kept:
        return T.SP("Undefined")
    if len(kept) == 1 and kept[0][1] is T.TRUE:
        return kept[0][0]
    flattened: list[Term] = []
    for value, condition in kept:
        flattened.extend((value, condition))
    return T.mk(S(_HEAD), tuple(flattened))


def branches(term: Term) -> list[Branch]:
    """Return value/condition branches, using TRUE for a non-piecewise term."""
    if not is_piecewise(term):
        return [(term, T.TRUE)]
    arguments = term.args
    return [
        (arguments[index], arguments[index + 1])
        for index in range(0, len(arguments), 2)
    ]


def conditions(term: Term) -> list[Term]:
    return [condition for _value, condition in branches(term)]


def project_pw(
    ctx: MathContext,
    term: Term,
) -> list[tuple[Term, Term, Projected | None]]:
    """Project each branch independently into the current projection ladder."""
    return [
        (value, condition, project(ctx, value))
        for value, condition in branches(term)
    ]


# ---------------------------------------------------------------------------
# Condition semantics
# ---------------------------------------------------------------------------


def select(
    ctx: MathContext,
    term: Term,
    assumptions: Assumptions,
) -> Selection:
    """Select by ordered first-match without guessing around Unknown."""
    survivors: list[Branch] = []
    refutations: list[Refutation] = []
    first_unknown: Reason | None = None
    for value, condition in branches(term):
        if condition is T.TRUE:
            if not survivors:
                return SelectedValue(value, tuple(refutations))
            survivors.append((value, condition))
            break
        verdict = decide(ctx, condition, assumptions)
        if verdict.is_no():
            if isinstance(verdict, No):
                refutations.append(verdict.evidence)
            continue
        if verdict.is_yes():
            if not survivors:
                return SelectedValue(value, tuple(refutations))
            survivors.append((value, condition))
            continue
        if not isinstance(verdict, Unknown):
            raise TypeError("decision pipeline returned an unsupported verdict")
        if first_unknown is None:
            first_unknown = verdict.reason
        survivors.append((value, condition))
    if not survivors:
        return SelectedValue(T.SP("Undefined"), tuple(refutations))
    return ResidualSelection(
        residual=piecewise(survivors),
        reason=Reason.FRAGMENT if first_unknown is None else first_unknown,
        refutations=tuple(refutations),
    )


def coverage(
    ctx: MathContext,
    term: Term,
    assumptions: Assumptions,
) -> Verdict:
    """Decide whether branch conditions cover the whole space."""
    branch_conditions = conditions(term)
    guarded = False
    causes: list[Refutation] = []
    for condition in branch_conditions:
        if condition is T.TRUE:
            return YES
        verdict = decide(ctx, condition, assumptions)
        if verdict.is_yes():
            return YES
        if verdict.is_no():
            if isinstance(verdict, No):
                causes.append(verdict.evidence)
            continue
        guarded = True
    if guarded:
        return unknown(Reason.GUARDED)
    claim = T.mk(S("Or"), tuple(branch_conditions))
    return refute(
        RefutationChannel.BRANCH,
        claim,
        detail="every branch condition was refuted, so coverage has a gap",
        causes=tuple(causes),
    )


def collapse(
    ctx: MathContext,
    term: Term,
    assumptions: Assumptions,
) -> Term | None:
    """Replace piecewise subterms by values selected in the assumption frame."""
    if is_piecewise(term):
        selection = select(ctx, term, assumptions)
        if isinstance(selection, ResidualSelection):
            return None
        return collapse(ctx, selection.value, assumptions)
    if not isinstance(term, Expr) or not term.args:
        return term
    arguments: list[Term] = []
    changed = False
    for argument in term.args:
        collapsed = collapse(ctx, argument, assumptions)
        if collapsed is None:
            return None
        changed = changed or collapsed is not argument
        arguments.append(collapsed)
    return T.mk(term.head, tuple(arguments)) if changed else term


def conflicts(
    ctx: MathContext,
    term: Term,
    assumptions: Assumptions,
) -> list[OverlapCheck]:
    """Lint branch pairs whose values differ on a satisfiable overlap."""
    from cas.math.decide import satisfiable

    branch_list = branches(term)
    output: list[OverlapCheck] = []
    for first_index, (first_value, first_condition) in enumerate(branch_list):
        for second_index in range(first_index + 1, len(branch_list)):
            second_value, second_condition = branch_list[second_index]
            overlap = (first_condition, second_condition)
            satisfiability = satisfiable(ctx, overlap, assumptions)
            if satisfiability.is_no():
                output.append(OverlapCheck(first_index, second_index, YES))
                continue
            output.append(
                OverlapCheck(
                    first_index,
                    second_index,
                    _agree(
                        ctx,
                        first_value,
                        second_value,
                        overlap,
                        assumptions,
                    ),
                )
            )
    return output


def _agree(
    ctx: MathContext,
    first: Term,
    second: Term,
    conditions: tuple[Term, ...],
    assumptions: Assumptions,
) -> Verdict:
    """Decide value agreement after extending the assumption frame."""
    if first is second:
        return YES
    extended = assumptions.extended(
        *(condition for condition in conditions if condition is not T.TRUE)
    )
    from cas.math.decide import equivalent

    return equivalent(ctx, first, second, extended)


# ---------------------------------------------------------------------------
# Per-branch operation lifting
# ---------------------------------------------------------------------------

LIFT_BRANCH_BUDGET = 1024


def _merge_runs(branch_list: Sequence[Branch]) -> list[Branch]:
    """Merge adjacent same-value branches under their disjunction."""
    output: list[Branch] = []
    for value, condition in branch_list:
        if output:
            previous_value, previous_condition = output[-1]
            if previous_value is value:
                output[-1] = (
                    previous_value,
                    T.or_(previous_condition, condition),
                )
                continue
        output.append((value, condition))
    return output


def lift(
    operation: Callable[..., Term],
    *terms: Term,
    budget: int = LIFT_BRANCH_BUDGET,
) -> Term:
    """Lift an operation over Piecewise arguments by Cartesian expansion."""
    if not any(is_piecewise(term) for term in terms):
        return operation(*terms)
    expansions = [_merge_runs(branches(term)) for term in terms]
    total = 1
    for expansion in expansions:
        total *= len(expansion)
    if total > budget:
        raise BudgetExceeded(
            total,
            f"piecewise lift would expand to {total} branches (budget {budget})",
        )
    combinations: list[list[Branch]] = [[]]
    for expansion in expansions:
        combinations = [
            combination + [branch]
            for combination in combinations
            for branch in expansion
        ]
    pairs: list[Branch] = []
    for combination in combinations:
        values = [value for value, _condition in combination]
        branch_conditions = [condition for _value, condition in combination]
        conjunction = _and_all(branch_conditions)
        if conjunction is T.FALSE:
            continue
        pairs.append((operation(*values), conjunction))
    return piecewise(pairs)


def _and_all(conditions: Sequence[Term]) -> Term:
    flattened: list[Term] = []
    for condition in conditions:
        if condition is T.FALSE:
            return T.FALSE
        if condition is T.TRUE:
            continue
        if isinstance(condition, Expr) and condition.head.name == "And":
            flattened.extend(condition.args)
        else:
            flattened.append(condition)
    if not flattened:
        return T.TRUE
    return T.and_(*flattened)


# ---------------------------------------------------------------------------
# Nested flattening and CAD domain extraction
# ---------------------------------------------------------------------------

_UNDEF = T.SP("Undefined")


def _conj(left: Term, right: Term) -> Term:
    if left is T.FALSE or right is T.FALSE:
        return T.FALSE
    if left is T.TRUE:
        return right
    if right is T.TRUE:
        return left
    return T.and_(left, right)


def fold_nested(term: Term) -> Term:
    """Flatten nested piecewise values into one layer."""
    if not is_piecewise(term):
        return term
    pairs: list[Branch] = []
    for value, condition in branches(term):
        if is_piecewise(condition):
            raise PiecewiseError(
                "a piecewise value is not allowed in condition position"
            )
        folded = fold_nested(value)
        if is_piecewise(folded):
            for inner_value, inner_condition in branches(folded):
                pairs.append((inner_value, _conj(inner_condition, condition)))
        else:
            pairs.append((folded, condition))
    return piecewise(pairs)


def domain_cells(
    ctx: MathContext,
    term: Term,
    variable: Sym,
) -> list[DomainCell]:
    """Resolve ordered-first-match values over the CAD cells in one variable."""
    flattened = fold_nested(term)
    branch_list = branches(flattened)
    branch_conditions = [condition for _value, condition in branch_list]
    output: list[DomainCell] = []
    for cell, labels in resolve_partition(ctx, branch_conditions, variable):
        value: Term = _UNDEF
        for (branch_value, _condition), holds in zip(branch_list, labels):
            if holds:
                value = branch_value
                break
        output.append((cell, value))
    return output


@dataclass(frozen=True, slots=True)
class Component:
    """One maximal connected component of a piecewise domain."""

    cells: tuple[DomainCell, ...]
    lo: RootInterval | None
    lo_closed: bool
    hi: RootInterval | None
    hi_closed: bool


def _mk_component(run: Sequence[DomainCell]) -> Component:
    first_cell = run[0][0]
    last_cell = run[-1][0]
    if isinstance(first_cell, PointCell):
        lower: RootInterval | None = first_cell.iso
        lower_closed = True
    else:
        lower = first_cell.lo
        lower_closed = False
    if isinstance(last_cell, PointCell):
        upper: RootInterval | None = last_cell.iso
        upper_closed = True
    else:
        upper = last_cell.hi
        upper_closed = False
    return Component(tuple(run), lower, lower_closed, upper, upper_closed)


def connected_components(domain: Sequence[DomainCell]) -> list[Component]:
    """Merge defined CAD cells into maximal connected components."""
    components: list[Component] = []
    run: list[DomainCell] = []
    for cell, value in domain:
        if value is _UNDEF:
            if run:
                components.append(_mk_component(run))
                run = []
        else:
            run.append((cell, value))
    if run:
        components.append(_mk_component(run))
    return components
