# -*- coding: utf-8 -*-
"""Order comparisons are read over an ordered domain.
The declared constants are the value-domain evidence the decision layer has (it
receives assumptions, not scope declarations): a constant declared not real means
the ordered reading does not apply, so the predicate must stay undecided instead
of being answered by ordered-field rules (an even power is nonnegative, a sum of
nonnegative terms is nonnegative). The assumption channels (order-chain edges and
interval bounds) read the same evidence, so an assumption carrying such a constant
is not consumed as an order fact either. Equality is not affected, because equality
is available in every domain.
"""

from cas.runtime import bootstrap, get_runtime
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.math.decide import decide, negate

install(bootstrap())


def _ctx():
    return get_runtime().math


def _v(src, assumptions=None):
    return decide(_ctx(), parse(src), assumptions)


def _assume(*srcs):
    return Assumptions().extended(*[parse(s) for s in srcs])


def test_even_power_of_a_nonreal_constant_is_not_answered():
    """`i^2 >= 0` used to come out YES through the ordered-field power rule."""
    assert not _v("i^2 >= 0").is_yes()
    assert _v("i^2 >= 0").is_unknown()
    assert not _v("(-1)*i^2 >= 0").is_yes()
    assert not _v("i > 0").is_yes()


def test_ordered_rules_still_apply_to_real_operands():
    assert _v("x^2 >= 0").is_yes()
    assert _v("2 < 3").is_yes()
    assert _v("x^2 < 1").is_unknown()


def test_equality_is_decided_in_every_domain():
    assert _v("i == i").is_yes()
    assert _v("i*i == -1").is_yes()


def test_strong_negation_is_withheld_for_nonreal_operands():
    """`not (a > b)` is `a <= b` only where an order exists; equality negation
    needs no order and stays available."""
    from cas.syntax import term as T
    assert negate(_ctx(), parse("x > 0")) == parse("x <= 0")
    assert negate(_ctx(), parse("i > 0")) == T.not_(parse("i > 0"))
    assert negate(_ctx(), parse("i == 0")) == parse("i != 0")


def test_assumption_order_edges_with_a_nonreal_constant_are_not_consumed():
    """The query gate withholds order comparisons carrying a constant declared not
    real, but the order-chain channel builds its edges from assumptions: without
    the same gate, `x < i` and `i < 3` would chain to prove `x < 3` where the
    ordered reading does not apply."""
    assert _v("x < 3", _assume("x < i", "i < 3")).is_unknown()
    assert _v("x <= 3", _assume("x < i", "i < 3")).is_unknown()


def test_real_order_chain_still_answers():
    """The real-valued path is unchanged: the same chain without a non-real
    constant answers YES."""
    assert _v("x < 3", _assume("x < y", "y < 3")).is_yes()
    assert _v("x <= 3", _assume("x <= y", "y <= 3")).is_yes()


def test_interval_channel_ignores_assumptions_carrying_a_nonreal_constant():
    """The interval channel also builds bounds from assumptions (equality
    substitution included); a fact carrying a constant declared not real is not an
    ordered bound."""
    assert _v("x < 3", _assume("x == i", "i < 2")).is_unknown()
    assert _v("x < 3", _assume("x == y", "y == i", "i < 2")).is_unknown()
