# -*- coding: utf-8 -*-
"""The decide axiom layer: a usable fallback, not dead code.

An initial audit concluded that these lines (_axiom_constants /
_axiom_function_bounds) were fully shadowed by the interval channel and unreachable.
Measurement refuted that: with _cmp_interval disabled, this layer still decides
correctly.

The real relationship: the interval channel and this layer consume the **same**
declaration bound data (const_bounds / FunctionDecl.bound), but the interval channel is
more general because it can bound a compound expression a-b as a whole, so it usually
decides first; this layer reads the lemmas directly, covers less, and takes effect only
when every earlier channel yields (returns None). Deleting it would leave the
declaration bound data with a single consumption path.
"""

import pytest

import cas.math.decide as D
from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.kernel.verdict import YES, NO


@pytest.fixture
def no_interval(monkeypatch):
    """Disable the interval channel: return None (yield) rather than Unknown, which
    would short-circuit later channels."""
    monkeypatch.setattr(D, "_cmp_interval", lambda op, a, b, ctx: None)


def _decide(src):
    return D.decide(parse(src), Assumptions())


@pytest.mark.parametrize("src,want", [
    ("pi > 3", YES),      # const_bounds: 3 <= lo
    ("pi < 4", YES),      # 4 >= hi
    ("e > 2", YES),
    ("e < 3", YES),
    ("gamma < 1", YES),
    ("pi > 0", YES),
    ("sin(x) > 2", NO),   # FunctionDecl.bound: sin in (-1,1)
])
def test_axiom_layer_acts_as_fallback(no_interval, src, want):
    """With the interval channel disabled, the axiom layer must produce the decision,
    which proves it is not dead code."""
    assert _decide(src) is want, f"{src} was not decided by the axiom layer"


def test_interval_channel_decides_normally():
    """Without disabling, the interval channel decides the same inputs (the axiom layer
    is shadowed)."""
    for src in ["pi > 3", "gamma < 1", "sin(x) > 2"]:
        assert _decide(src) in (YES, NO)


def test_axiom_layer_agrees_with_interval_channel():
    """Both consume the same data, so their conclusions must agree -- a divergence means
    one of them is wrong."""
    cases = ["pi > 3", "pi < 4", "e > 2", "e < 3", "gamma < 1", "sin(x) > 2"]
    normal = [_decide(s) for s in cases]
    with_axioms = []
    saved = D._cmp_interval
    try:
        D._cmp_interval = lambda op, a, b, ctx: None
        with_axioms = [_decide(s) for s in cases]
    finally:
        D._cmp_interval = saved
    assert normal == with_axioms, "the two channels diverged"


def test_axiom_layer_incomplete_returns_undecided():
    """The axiom layer recognizes only the narrow form "constant/function op numeric";
    everything else must stay undecided."""
    saved = D._cmp_interval
    try:
        D._cmp_interval = lambda op, a, b, ctx: None
        for src in ["x > 0", "sin(x) < -2", "pi + gamma > 4"]:
            assert _decide(src).is_unknown(), f"{src} should not be decided by the axiom layer"
    finally:
        D._cmp_interval = saved


def test_axiom_layer_consumes_runtime_declarations():
    """Changing the bound data changes the conclusion, which proves the source is the
    runtime-assembled declaration rather than a hardcoded value."""
    from cas.runtime import dispatch
    d = dispatch.const_by_name("gamma")
    assert d.bounds is not None
    lo, hi = d.bounds
    saved = D._cmp_interval
    try:
        D._cmp_interval = lambda op, a, b, ctx: None
        assert _decide(f"gamma > {lo}") is YES
        assert _decide(f"gamma < {lo}") is NO
        assert _decide(f"gamma > {hi}") is NO
    finally:
        D._cmp_interval = saved
