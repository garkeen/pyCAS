"""Branch: conditional case splits.

Each case uses its own child scope, and sibling branches cannot see each other:

    Gamma
    |- Gamma + [a != 0]
    |- Gamma + [a = 0]

Branch contexts cannot be merged directly. A merge must verify five things in
the parent scope:

    1. the branches cover the parent problem
    2. every branch answers the same task
    3. each branch result holds in its own scope
    4. no helper symbol escaped
    5. each branch's open conditions were promoted correctly

Point 5 is where branch merging most easily goes wrong: a guard `G_i` open in
branch `C_i` is promoted to the parent as

    C_i => G_i

not as a global, unconditional requirement `G_i`. That is what `promote_guard`
does.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.kernel.ids import JudgmentId, ScopeId
from cas.workflow.ids import TaskId


@dataclass(frozen=True, slots=True)
class BranchCase:
    condition: T.Term
    scope: ScopeId
    task: TaskId | None = None
    label: str = ""


@dataclass(frozen=True, slots=True)
class BranchGroup:
    id: int
    parent_scope: ScopeId
    cases: tuple
    coverage: JudgmentId | None = None


def promote_guard(case_condition, guard):
    """Promote a guard open inside a branch to the parent scope: `C_i => G_i`,
    not a global `G_i`."""
    return T.implies(case_condition, guard)


def complementary_pair(cases):
    """Whether the condition list contains a complementary pair (both `c` and
    `not c` as branch conditions).

    This is a syntactic test and does not guess semantics; returns (i, j) or
    None.
    """
    for i in range(len(cases)):
        ci = cases[i].condition
        for j in range(i + 1, len(cases)):
            cj = cases[j].condition
            if _is_neg(cj, ci) or _is_neg(ci, cj):
                return (i, j)
    return None


def _is_neg(a, b):
    return (isinstance(a, T.Expr) and isinstance(a.head, T.Sym)
            and a.head.name == "Not" and a.args[0] is b)


class BranchStore:
    """Branch group storage (append-only)."""

    def __init__(self):
        self._groups: dict[int, BranchGroup] = {}
        self._next = 0

    def create(self, parent_scope, cases) -> BranchGroup:
        gid = self._next
        self._next += 1
        g = BranchGroup(id=gid, parent_scope=parent_scope,
                        cases=tuple(cases))
        self._groups[gid] = g
        return g

    def get(self, gid) -> BranchGroup:
        return self._groups[gid]

    def set_coverage(self, gid, jid) -> BranchGroup:
        from dataclasses import replace
        g = replace(self._groups[gid], coverage=jid)
        self._groups[gid] = g
        return g

    def all(self):
        return tuple(self._groups[i] for i in range(self._next))

    def __len__(self):
        return self._next
