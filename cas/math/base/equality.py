"""Equality: domain normal form, identity decisions, and ledger closure."""

from __future__ import annotations

from collections.abc import Iterable
from typing import TYPE_CHECKING

from cas.kernel.scope import Assumptions
from cas.kernel.verdict import (
    YES,
    Reason,
    RefutationChannel,
    Verdict,
    contextualize,
    refute,
    unknown,
)
from cas.math.project import normalize as proj_normalize
from cas.math.project import project
from cas.syntax import term as T
from cas.syntax.term import S, SortKey, Term
from cas.syntax.termpath import free_vars, postorder

if TYPE_CHECKING:
    from cas.math.context import MathContext


def normal_form(ctx: MathContext, term: Term) -> Term:
    """Return the domain normal form of a term or equation."""
    if isinstance(term, T.Expr) and term.head.name == "Eq":
        left, right = term.args
        hit = project(ctx, T.plus(left, T.neg(right)))
        if hit is not None:
            return T.eq(proj_normalize(hit), T.ZERO)
        return term
    hit = project(ctx, term)
    if hit is not None:
        return proj_normalize(hit)
    return term


def is_closed(term: Term) -> bool:
    """Return whether a term has no free variables."""
    return not free_vars(term)


def identity_verdict(ctx: MathContext, left: Term, right: Term) -> Verdict:
    """Decide identity through the assembled mathematical pipeline."""
    from cas.math.decide import equivalent

    return equivalent(ctx, left, right)


_CLOSURE_TERM_BUDGET = 4000


def _representative_order(term: Term) -> tuple[int, int, SortKey]:
    """Order class members so the representative is a property of the term.

    A closed member comes first, then the smaller subtree, then the canonical
    order. Closed first is what makes the rewrite worth doing: the residual
    equation the closure hands to the exact and interval channels is decided
    when the frame pins a variable to a numeral, and stays undecided when the
    representative is the variable itself. The whole tuple is structural, so
    the choice does not depend on which object happened to be allocated first.
    """
    return (1 if free_vars(term) else 0, len(postorder(term)), term._key)


class _Union:
    """Union-find over terms keyed by structural hash.

    Equality is structural, so the key is the structural hash: a query term and
    the same term written inside a ledger fact are two objects but one element,
    and the closure has to treat them as one. The representative of a class is
    chosen by `_representative_order`, which reads the term's shape.
    """

    def __init__(self) -> None:
        self._up: dict[int, Term] = {}

    def add(self, term: Term) -> None:
        if term._sh not in self._up:
            self._up[term._sh] = term

    def find(self, term: Term) -> Term:
        self.add(term)
        path: list[Term] = []
        current = term
        while self._up[current._sh] is not current:
            path.append(current)
            current = self._up[current._sh]
        for item in path:
            self._up[item._sh] = current
        return current

    def union(self, left: Term, right: Term) -> bool:
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root == right_root:
            return False
        if _representative_order(right_root) < _representative_order(left_root):
            left_root, right_root = right_root, left_root
        self._up[right_root._sh] = left_root
        return True


def _congruence(union: _Union, terms: list[Term]) -> None:
    """Merge terms whose head and argument classes agree."""
    changed = True
    while changed:
        changed = False
        signatures: dict[tuple[int, tuple[int, ...]], Term] = {}
        for term in terms:
            if not isinstance(term, T.Expr):
                continue
            key = (
                term.head._h,
                tuple(union.find(argument)._h for argument in term.args),
            )
            previous = signatures.get(key)
            if previous is None:
                signatures[key] = term
            elif union.union(term, previous):
                changed = True


def _representative_rewrite(
    union: _Union,
    terms: list[Term],
    term: Term,
) -> Term:
    """Rewrite class members to their representatives at a fixed point."""
    universe: list[Term] = []
    seen: set[int] = set()
    stack: list[Term] = [*terms, term]
    while stack:
        current = stack.pop()
        if current._h in seen:
            continue
        seen.add(current._h)
        universe.append(current)
        representative = union.find(current)
        if representative is not current and representative._h not in seen:
            stack.append(representative)
        if isinstance(current, T.Expr):
            stack.extend(current.args)
    # The universe is keyed by the object's serial (`_h`), not by structure:
    # a node and the node it was rebuilt from are two objects that may be
    # structurally equal, and the fixed point below must be able to hold both
    # until they actually converge. Equality and hashing are structural, so
    # using them as keys here would let a rebuild overwrite the entry it is
    # about to read and would report convergence one pass early.
    values: dict[int, Term] = {current._h: current for current in universe}
    for _ in range(len(universe) + 2):
        changed = False
        for current in universe:
            representative = union.find(current)
            if representative is not current:
                rebuilt = values[representative._h]
            elif isinstance(current, T.Expr):
                arguments = tuple(values[argument._h] for argument in current.args)
                # `is`, not `==`: `values` holds the objects this pass produced,
                # and the point of the test is "did this node get a new object",
                # which is a question about the walk and not about structure.
                rebuilt = (
                    T.mk(current.head, arguments)
                    if any(
                        new is not old
                        for new, old in zip(arguments, current.args)
                    )
                    else current
                )
            else:
                rebuilt = current
            if rebuilt is not values[current._h]:
                values[current._h] = rebuilt
                changed = True
        if not changed:
            break
    return values[term._h]


def closure_decide(
    ctx: MathContext,
    left: Term,
    right: Term,
    assumptions: Assumptions | Iterable[Term],
) -> Verdict | None:
    """Decide an equation relative to an assumption frame."""
    facts = [
        fact
        for fact in assumptions
        if isinstance(fact, T.Expr) and fact.head.name == "Eq"
    ]
    if not facts:
        return None
    terms: list[Term] = []
    seen: set[int] = set()
    stack: list[Term] = [left, right, *facts]
    while stack:
        current = stack.pop()
        if current._h in seen:
            continue
        seen.add(current._h)
        terms.append(current)
        if isinstance(current, T.Expr):
            stack.extend(current.args)
    if len(terms) > _CLOSURE_TERM_BUDGET:
        return unknown(Reason.BUDGET)
    union = _Union()
    for fact in facts:
        union.union(fact.args[0], fact.args[1])
    _congruence(union, terms)
    if union.find(left) is union.find(right):
        return YES
    normal_left = _representative_rewrite(union, terms, left)
    normal_right = _representative_rewrite(union, terms, right)
    claim = T.mk(S("Eq"), (left, right))
    if normal_left is not left or normal_right is not right:
        verdict = identity_verdict(ctx, normal_left, normal_right)
        if verdict.is_yes():
            return YES
        if verdict.is_no() and is_closed(normal_left) and is_closed(normal_right):
            return contextualize(
                verdict,
                claim,
                "the representative terms have different identities",
            )
    left_root = union.find(left)
    right_root = union.find(right)
    for assumption in assumptions:
        if isinstance(assumption, T.Expr) and assumption.head.name == "Ne":
            first, second = assumption.args
            first_root = union.find(first)
            second_root = union.find(second)
            if first_root is second_root:
                continue
            if (
                first_root is left_root
                and second_root is right_root
            ) or (
                first_root is right_root
                and second_root is left_root
            ):
                return refute(
                    RefutationChannel.ASSUMPTION_FACT,
                    claim,
                    left,
                    right,
                    assumption,
                    detail="the assumption frame contains a matching Ne fact",
                )
    return None
