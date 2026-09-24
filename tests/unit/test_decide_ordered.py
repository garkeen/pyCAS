"""Order comparisons require an ordered domain."""

from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.math.decide import decide, negate
from cas.runtime import Runtime


def _verdict(runtime: Runtime, source: str, assumptions=None):
    return decide(runtime.math, parse(runtime, source), assumptions)


def _assumptions(runtime: Runtime, *sources: str) -> Assumptions:
    return Assumptions().extended(*(parse(runtime, source) for source in sources))


def test_even_power_of_a_nonreal_constant_is_not_answered(runtime: Runtime) -> None:
    assert not _verdict(runtime, "i^2 >= 0").is_yes()
    assert _verdict(runtime, "i^2 >= 0").is_unknown()
    assert not _verdict(runtime, "(-1)*i^2 >= 0").is_yes()
    assert not _verdict(runtime, "i > 0").is_yes()


def test_ordered_rules_still_apply_to_real_operands(runtime: Runtime) -> None:
    assert _verdict(runtime, "x^2 >= 0").is_yes()
    assert _verdict(runtime, "2 < 3").is_yes()
    assert _verdict(runtime, "x^2 < 1").is_unknown()


def test_equality_is_decided_in_every_domain(runtime: Runtime) -> None:
    assert _verdict(runtime, "i == i").is_yes()
    assert _verdict(runtime, "i*i == -1").is_yes()


def test_strong_negation_is_withheld_for_nonreal_operands(runtime: Runtime) -> None:
    from cas.syntax import term as syntax

    assert negate(runtime.math, parse(runtime, "x > 0")) == parse(runtime, "x <= 0")
    assert negate(runtime.math, parse(runtime, "i > 0")) == syntax.not_(
        parse(runtime, "i > 0")
    )
    assert negate(runtime.math, parse(runtime, "i == 0")) == parse(runtime, "i != 0")


def test_assumption_order_edges_with_a_nonreal_constant_are_not_consumed(
    runtime: Runtime,
) -> None:
    frame = _assumptions(runtime, "x < i", "i < 3")
    assert _verdict(runtime, "x < 3", frame).is_unknown()
    assert _verdict(runtime, "x <= 3", frame).is_unknown()


def test_real_order_chain_still_answers(runtime: Runtime) -> None:
    frame = _assumptions(runtime, "x < y", "y < 3")
    assert _verdict(runtime, "x < 3", frame).is_yes()
    assert _verdict(runtime, "x <= 3", frame).is_yes()


def test_interval_channel_ignores_nonreal_assumptions(runtime: Runtime) -> None:
    frame = _assumptions(runtime, "x == i", "i < 2")
    assert _verdict(runtime, "x < 3", frame).is_unknown()
    chained = _assumptions(runtime, "x == y", "y == i", "i < 2")
    assert _verdict(runtime, "x < 3", chained).is_unknown()
