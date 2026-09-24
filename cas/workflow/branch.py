"""Conditional case-split storage and branch-condition utilities."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass, replace

from cas.kernel.ids import JudgmentId, ScopeId
from cas.syntax import term as T
from cas.syntax.term import Expr, Term


@dataclass(frozen=True, slots=True)
class BranchCase:
    condition: Term
    scope: ScopeId
    label: str = ""


@dataclass(frozen=True, slots=True)
class BranchGroup:
    id: int
    parent_lineage: ScopeId
    cases: tuple[BranchCase, ...]
    coverage: JudgmentId | None = None


def promote_guard(case_condition: Term, guard: Term) -> Expr:
    """Promote a branch-local guard to an implication in the parent scope."""
    return T.implies(case_condition, guard)


def complementary_pair(cases: Sequence[BranchCase]) -> tuple[int, int] | None:
    """Return indices of a syntactically complementary branch pair."""
    for first in range(len(cases)):
        first_condition = cases[first].condition
        for second in range(first + 1, len(cases)):
            second_condition = cases[second].condition
            if _is_negation(second_condition, first_condition) or _is_negation(
                first_condition, second_condition
            ):
                return first, second
    return None


def _is_negation(term: Term, other: Term) -> bool:
    return (
        isinstance(term, T.Expr)
        and isinstance(term.head, T.Sym)
        and term.head.name == "Not"
        and term.args[0] is other
    )


class BranchStore:
    """Append-only branch-group storage."""

    def __init__(self) -> None:
        self._groups: dict[int, BranchGroup] = {}
        self._next = 0

    def create(
        self,
        parent_lineage: ScopeId,
        cases: Sequence[BranchCase],
    ) -> BranchGroup:
        group_id = self._next
        self._next += 1
        group = BranchGroup(
            id=group_id,
            parent_lineage=parent_lineage,
            cases=tuple(cases),
        )
        self._groups[group_id] = group
        return group

    def get(self, group_id: int) -> BranchGroup:
        return self._groups[group_id]

    def set_coverage(self, group_id: int, judgment_id: JudgmentId) -> BranchGroup:
        group = replace(self._groups[group_id], coverage=judgment_id)
        self._groups[group_id] = group
        return group

    def all(self) -> tuple[BranchGroup, ...]:
        return tuple(self._groups[index] for index in range(self._next))

    def __len__(self) -> int:
        return self._next
