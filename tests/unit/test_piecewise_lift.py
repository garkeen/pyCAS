# -*- coding: utf-8 -*-
"""`lift` over Piecewise arguments: adjacent same-value branch merging and the
expansion budget.

Nails two defects. (a) The Cartesian expansion multiplied the branch count without
ever merging branches that carry the same value, so repeated operations on piecewise
values grew the container multiplicatively even when the argument itself had adjacent
branches with one value. (b) The expansion had no budget: a large product was built
in full (or would have been), instead of refusing honestly.

The merge is restricted to *adjacent* branches. Ordered first-match semantics makes
that restriction the only sound one: adjacent same-value branches yield their value
whether or not their conditions overlap, so one branch conditioned on the disjunction
is equivalent, while same-value branches separated by another branch cannot be merged
without deciding whether the intervening branch is reached first.
"""

import pytest

from cas.errors import BudgetExceeded
from cas.kernel.scope import Assumptions
from cas.syntax import term as T
from cas.syntax.term import S, N, mk
from cas.math.piecewise import (LIFT_BRANCH_BUDGET, branches, lift, piecewise,
                                select)

X = S("x")


def cond(op, k):
    return mk(S(op), (X, N(k)))


def at(a):
    """Assumption set for the concrete point x = a."""
    return Assumptions().extended(mk(S("Eq"), (X, N(a))))


# ---------------------------------------------------------------------------
# Adjacent same-value branches are merged
# ---------------------------------------------------------------------------

def test_adjacent_same_value_branches_merge_into_one():
    c1, c2 = cond("Gt", 0), cond("Lt", -3)
    p = piecewise([(N(1), c1), (N(1), c2), (N(2), T.TRUE)])
    assert len(branches(p)) == 3
    m = lift(T.plus, p, N(10))
    bs = branches(m)
    # the raw product of 3 branches with a single always-true branch would be 3
    assert len(bs) == 2
    # the two equal-value branches entered the product as one branch, with the
    # disjunction of their conditions
    assert bs[0][1] == T.or_(c1, c2) and bs[0][1] is T.or_(c1, c2)
    assert bs[0][0] is T.plus(N(1), N(10))
    assert bs[1][1] is T.TRUE


def test_merged_condition_is_the_disjunction_in_canonical_form():
    c1, c2 = cond("Le", 1), cond("Ge", 5)
    p = piecewise([(N(2), c1), (N(2), c2), (N(3), T.TRUE)])
    bs = branches(lift(T.times, p, N(10)))
    assert bs[0][1] == T.or_(c2, c1)          # same interned node, argument order canonical
    assert bs[0][0] is T.times(N(2), N(10))


def test_merge_composes_with_a_second_piecewise_argument():
    ca, cb = cond("Gt", 0), cond("Lt", -1)
    p = piecewise([(N(1), ca), (N(1), cb), (N(2), T.TRUE)])
    q = piecewise([(N(5), ca), (N(7), T.TRUE)])
    m = lift(T.plus, p, q)
    # merged p has 2 branches and q has 2, so the product is 4; without the merge the
    # same call would have produced 3 * 2 = 6
    assert len(branches(m)) == 4


# ---------------------------------------------------------------------------
# Non-adjacent same-value branches are not merged
# ---------------------------------------------------------------------------

def test_non_adjacent_same_value_branches_are_not_merged():
    # values 1, 2, 1: the equal values are separated by a different value
    p = piecewise([(N(1), cond("Gt", 0)), (N(2), cond("Lt", -3)), (N(1), T.TRUE)])
    assert len(branches(p)) == 3
    m = lift(T.plus, p, N(10))
    assert len(branches(m)) == 3            # count unchanged: no merge was legal


# ---------------------------------------------------------------------------
# Pointwise agreement: the merged form means the same function
# ---------------------------------------------------------------------------

def test_merged_lift_agrees_pointwise_with_the_selected_values():
    c1, c2 = cond("Gt", 0), cond("Lt", -3)
    p = piecewise([(N(1), c1), (N(1), c2), (N(2), T.TRUE)])
    q = piecewise([(N(5), c2), (N(7), T.TRUE)])
    m = lift(T.plus, p, q)
    for a in range(-7, 8):
        ctx = at(a)
        st_p, vp = select(p, ctx)
        st_q, vq = select(q, ctx)
        st_m, vm = select(m, ctx)
        assert (st_p, st_q, st_m) == ("value", "value", "value")
        assert T.plus(vp, vq) is vm


# ---------------------------------------------------------------------------
# The budget refuses honestly
# ---------------------------------------------------------------------------

def _two_by_two():
    # four distinct comparisons: no adjacent same-value pair in either argument, so the
    # product stays 2 * 2 with no merge to rely on
    p = piecewise([(N(1), cond("Gt", 0)), (N(2), cond("Lt", -1))])
    q = piecewise([(N(3), cond("Ge", 2)), (N(4), cond("Le", -4))])
    return p, q


def test_budget_refuses_when_the_product_exceeds_it():
    p, q = _two_by_two()
    with pytest.raises(BudgetExceeded) as ei:
        lift(T.plus, p, q, budget=3)
    assert ei.value.spent == 4                    # the product size, computed before expanding
    assert str(ei.value) == "piecewise lift would expand to 4 branches (budget 3)"


def test_a_larger_budget_lets_the_same_call_succeed():
    p, q = _two_by_two()
    m = lift(T.plus, p, q, budget=4)
    assert len(branches(m)) == 4


def test_default_budget_keeps_small_cases_working():
    p, q = _two_by_two()
    m = lift(T.plus, p, q)
    assert len(branches(m)) == 4
    assert LIFT_BRANCH_BUDGET >= 4


def test_budget_stops_a_product_that_merging_cannot_shrink():
    p, q = _two_by_two()
    for t in (p, q):                          # nothing to merge: every adjacency differs
        bs = branches(t)
        assert all(a[0] is not b[0] for a, b in zip(bs, bs[1:]))
    with pytest.raises(BudgetExceeded) as ei:
        lift(T.plus, p, q, budget=3)
    assert ei.value.spent == 4
    assert str(ei.value) == "piecewise lift would expand to 4 branches (budget 3)"


# ---------------------------------------------------------------------------
# Call compatibility
# ---------------------------------------------------------------------------

def test_lift_without_a_piecewise_argument_returns_the_operation():
    assert lift(T.plus, X, N(2)) is T.plus(X, N(2))
    assert lift(T.times, X, X) is T.times(X, X)


def test_lift_takes_its_budget_as_a_keyword():
    p, q = _two_by_two()
    assert len(branches(lift(T.plus, p, q, budget=4))) == 4
