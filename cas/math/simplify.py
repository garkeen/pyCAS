"""Term rebuilding and declared automatic simplification."""

from __future__ import annotations

from cas.errors import BudgetExceeded
from cas.math.context import MathContext
from cas.math.rules import Applied, apply_rule
from cas.syntax import term as T
from cas.syntax.term import Expr, Term
from cas.syntax.termpath import all_paths, postorder, term_at

_MEMO: dict[int, Term] = {}
_MEMO_CAP = 1 << 16


def cost(term: Term) -> int:
    """Return the explicit-stack node count of a term."""
    return sum(1 for _term in postorder(term))


def rebuild(term: Term, budget: int = 100000) -> Term:
    """Re-intern a term bottom-up without applying mathematical rules."""
    hit = _MEMO.get(term._h)
    if hit is not None:
        return hit
    spent = budget

    def rebuild_node(root: Term) -> Term:
        nonlocal spent
        values: dict[Term, Term] = {}
        for current in reversed(postorder(root)):
            spent -= 1
            if spent < 0:
                raise BudgetExceeded()
            if current in values:
                continue
            if isinstance(current, Expr):
                arguments = tuple(values[argument] for argument in current.args)
                values[current] = T.mk(current.head, arguments)
            elif isinstance(current, T.Bound):
                values[current] = T.mk_bound_canon(
                    current.hint, values[current.body]
                )
            else:
                values[current] = current
        return values[root]

    previous = term
    while True:
        following = rebuild_node(previous)
        if following is previous:
            if len(_MEMO) >= _MEMO_CAP:
                _MEMO.clear()
            _MEMO[term._h] = previous
            return previous
        previous = following


def autosimplify(ctx: MathContext, term: Term, budget: int = 100000) -> Term:
    """Iterate declared guard-free automatic rules to a cost fixed point."""
    rules = ctx.rule_catalog
    automatic_ids = {
        rule.id for rule in rules.rules.values() if rule.auto and rule.guard is None
    }
    current = rebuild(term, budget)
    while True:
        base_cost = cost(current)
        following: Term | None = None
        for path in all_paths(current):
            subterm = term_at(current, path)
            candidates = [
                rule
                for rule in rules.candidates(subterm)
                if rule.id in automatic_ids
            ]
            for rule in sorted(candidates, key=lambda item: item.priority):
                result = apply_rule(rule, current, path, budget=budget)
                if isinstance(result, Applied) and cost(result.term) < base_cost:
                    following = result.term
                    break
            if following is not None:
                break
        if following is None:
            return current
        current = rebuild(following, budget)
