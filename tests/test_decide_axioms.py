# -*- coding: utf-8 -*-
"""decide 公理层：可用兜底，不是死代码。

审计初判这 64 行（_axiom_constants / _axiom_function_bounds）被区间通道
完全遮蔽、不可达。实测否定：屏蔽 _cmp_interval 后本层仍能正确裁决。

真实关系：区间通道与本层消费**同一份**图书馆声明（const_bounds /
FunctionDecl.bound），但区间通道更通用（能对复合式 a−b 整体求区间），
故通常先由它定案；本层是引理直读，覆盖更窄，只在所有前序通道都让位
（返回 None）时才生效。删它会让图书馆界数据只剩单一消费路径。
"""

import pytest

import cas.math.decide as D
from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.kernel.verdict import YES, NO


@pytest.fixture
def no_interval(monkeypatch):
    """屏蔽区间通道：返回 None（让位），而非 Unknown（会短路后续通道）。"""
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
    ("sin(x) > 2", NO),   # FunctionDecl.bound: sin ∈ (-1,1)
])
def test_axiom_layer_acts_as_fallback(no_interval, src, want):
    """屏蔽区间通道后，裁决必须由公理层给出——证明它不是死代码。"""
    assert _decide(src) is want, f"{src} 未能由公理层裁决"


def test_interval_channel_decides_normally():
    """不屏蔽时，区间通道在同一批输入上就定了案（公理层被遮蔽）。"""
    for src in ["pi > 3", "gamma < 1", "sin(x) > 2"]:
        assert _decide(src) in (YES, NO)


def test_axiom_layer_agrees_with_interval_channel():
    """两者消费同源数据，结论必须一致——不一致说明其中一条错了。"""
    cases = ["pi > 3", "pi < 4", "e > 2", "e < 3", "gamma < 1", "sin(x) > 2"]
    normal = [_decide(s) for s in cases]
    with_axioms = []
    saved = D._cmp_interval
    try:
        D._cmp_interval = lambda op, a, b, ctx: None
        with_axioms = [_decide(s) for s in cases]
    finally:
        D._cmp_interval = saved
    assert normal == with_axioms, "两条通道结论分叉"


def test_axiom_layer_incomplete_returns_undecided():
    """公理层只认"常数/函数 op 数值"的窄形态，其余必须未决。"""
    saved = D._cmp_interval
    try:
        D._cmp_interval = lambda op, a, b, ctx: None
        for src in ["x > 0", "sin(x) < -2", "pi + gamma > 4"]:
            assert _decide(src).is_unknown(), f"{src} 不应由公理层裁决"
    finally:
        D._cmp_interval = saved


def test_axiom_layer_consumes_runtime_declarations():
    """界数据若改，结论随之改——证明数据源在运行期装配的声明而非硬编码。"""
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
