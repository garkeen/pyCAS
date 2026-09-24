"""Declaration-bound decision fallback."""

import pytest

import cas.math.decide as decide_module
from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.kernel.verdict import YES
from cas.runtime import Runtime


@pytest.fixture
def no_interval(monkeypatch):
    monkeypatch.setattr(
        decide_module,
        "_cmp_interval",
        lambda ctx, op, a, b, assumptions: None,
    )


def _decide(runtime: Runtime, source: str):
    return decide_module.decide(
        runtime.math,
        parse(runtime, source),
        Assumptions(),
    )


@pytest.mark.parametrize(
    "source,want_yes",
    [
        ("pi > 3", True),
        ("pi < 4", True),
        ("e > 2", True),
        ("e < 3", True),
        ("gamma < 1", True),
        ("pi > 0", True),
        ("sin(x) > 2", False),
    ],
)
def test_axiom_layer_acts_as_fallback(
    runtime: Runtime,
    no_interval,
    source: str,
    want_yes: bool,
) -> None:
    result = _decide(runtime, source)
    assert result.is_yes() is want_yes
    if not want_yes:
        assert result.evidence.proposition is not None
        assert result.evidence.witnesses


def test_interval_channel_decides_normally(runtime: Runtime) -> None:
    for source in ("pi > 3", "gamma < 1", "sin(x) > 2"):
        assert _decide(runtime, source).is_yes() or _decide(runtime, source).is_no()


def test_axiom_layer_agrees_with_interval_channel(runtime: Runtime) -> None:
    cases = ("pi > 3", "pi < 4", "e > 2", "e < 3", "gamma < 1", "sin(x) > 2")
    normal = [_decide(runtime, source).is_no() for source in cases]
    saved = decide_module._cmp_interval
    try:
        decide_module._cmp_interval = lambda ctx, op, a, b, assumptions: None
        with_axioms = [_decide(runtime, source).is_no() for source in cases]
    finally:
        decide_module._cmp_interval = saved
    assert normal == with_axioms


def test_axiom_layer_incomplete_returns_undecided(
    runtime: Runtime,
    monkeypatch,
) -> None:
    monkeypatch.setattr(
        decide_module,
        "_cmp_interval",
        lambda ctx, op, a, b, assumptions: None,
    )
    for source in ("x > 0", "sin(x) < -2", "pi + gamma > 4"):
        assert _decide(runtime, source).is_unknown()


def test_axiom_layer_consumes_runtime_declarations(
    runtime: Runtime,
    monkeypatch,
) -> None:
    declaration = runtime.const_by_name("gamma")
    assert declaration is not None and declaration.bounds is not None
    lower, upper = declaration.bounds
    monkeypatch.setattr(
        decide_module,
        "_cmp_interval",
        lambda ctx, op, a, b, assumptions: None,
    )
    assert _decide(runtime, f"gamma > {lower}") is YES
    assert _decide(runtime, f"gamma < {lower}").is_no()
    assert _decide(runtime, f"gamma > {upper}").is_no()
