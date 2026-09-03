# -*- coding: utf-8 -*-
"""回代判官（cas/judge）：验证系统的原子，全系统唯一实现。

钉子：判官曾分散在 workflow._piecewise_aware_zero（私有）与 repl 的
内联副本，且两处通道顺序已分叉（repl 先试 eval_exact，workflow 只走
zero_of）。收敛后裁决权威只认 zero_of（域标准形）。
"""

import pytest

from cas import term as T
from cas.term import S
from cas.parser import parse
from cas.piecewise import piecewise
from cas.verdict import YES, NO
from cas.judge import (back_substitute, is_zero, guard_report,
                       verify_solution, has_piecewise, has_undef)


def Int(n):
    return T.Int(n)


def eq_of(src):
    return parse(src)


# ---------------------------------------------------------------------------
# 真解 / 伪解
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src,val,want", [
    ("2*x + 3 == 7", 2, True),        # 真解
    ("2*x + 3 == 7", 3, False),       # 伪解
    ("x^2 - 4 == 0", 2, True),
    ("x^2 - 4 == 0", 3, False),
    ("x/2 - 1 == 0", 2, True),
    ("x - x == 0", 5, True),
])
def test_回代判零(src, val, want):
    bs = back_substitute(eq_of(src), T.S("x"), Int(val))
    assert bs.zero is want


def test_伪解给出精确展示值():
    bs = back_substitute(eq_of("x^2 - 4 == 0"), T.S("x"), Int(3))
    assert bs.zero is False
    assert bs.exact == 5                      # 展示值，不参与裁决


def test_判零权威是域标准形而非环层求值():
    """eval_exact 只取展示值；裁决由 zero_of 出，覆盖严格更广。"""
    bs = back_substitute(eq_of("2*x + 3 == 7"), T.S("x"), Int(2))
    assert bs.zero is True
    assert bs.exact == 0                      # 两者都是精确算术，必须一致


# ---------------------------------------------------------------------------
# 分段：点塌缩后判零
# ---------------------------------------------------------------------------

def _分段方程():
    x = T.S("x")
    # f(x) = x-1 (x>0), x+1 (x<=0)  =>  f(x)=0 的解为 x=1 与 x=-1
    pw = piecewise([(T.plus(x, T.neg(Int(1))), parse("x > 0")),
                    (T.plus(x, Int(1)), parse("x <= 0"))])
    return T.mk(S("Eq"), (pw, T.ZERO)), x


@pytest.mark.parametrize("val,want", [(1, True), (-1, True),
                                      (2, False), (-3, False), (0, False)])
def test_分段方程逐点塌缩判零(val, want):
    eq, x = _分段方程()
    assert back_substitute(eq, x, Int(val)).zero is want


def test_含分段时走塌缩通道():
    eq, x = _分段方程()
    bs = back_substitute(eq, x, Int(1))
    assert has_piecewise(bs.diff) is True
    assert bs.exact is None                   # 环层求值管不了分段项


# ---------------------------------------------------------------------------
# 未决与定义域外
# ---------------------------------------------------------------------------

def test_判不动回未决不冒充通过():
    """含超越函数的项投影落空：None 是未决，不是"非解"。"""
    eq = T.mk(S("Eq"), (parse("sin(x)"), T.ZERO))
    bs = back_substitute(eq, T.S("x"), Int(0))
    assert bs.zero is None                      # 判不动
    assert verify_solution(eq, T.S("x"), Int(0)).is_unknown()


def test_非负解不能冒充通过():
    """verify_solution 的三个出口：NO / Unknown / YES。"""
    ok = verify_solution(eq_of("2*x + 3 == 7"), T.S("x"), Int(2))
    assert ok is YES
    bad = verify_solution(eq_of("2*x + 3 == 7"), T.S("x"), Int(3))
    assert bad is NO


# ---------------------------------------------------------------------------
# 守卫
# ---------------------------------------------------------------------------

def test_守卫失败与否证():
    eq = eq_of("2*x + 3 == 7")
    # 真解 x=2，但附加一条 x>5 的假守卫：判零过，守卫不过
    guards = [parse("x > 5")]
    v = verify_solution(eq, T.S("x"), Int(2), guards=guards)
    assert v is NO


def test_守卫报告逐条给出裁决():
    guards = [parse("x > 0"), parse("x < 10")]
    rep = guard_report(guards, T.S("x"), Int(2))
    assert len(rep) == 2
    assert all(c.verdict is YES for c in rep)
    assert all(c.subst is not None for c in rep)


# ---------------------------------------------------------------------------
# 实现唯一性
# ---------------------------------------------------------------------------

def test_判官只在judge一处实现():
    """workflow 不得再持有判零副本，repl 不得盗用私有函数。"""
    import cas.workflow as W
    import cas.judge as J
    for name in ("_piecewise_aware_zero", "_has_piecewise", "_has_undef"):
        assert not hasattr(W, name), f"workflow 仍持有判官副本: {name}"
    assert J.is_zero is not None


def test_repl不盗用workflow私有函数():
    import pathlib
    src = pathlib.Path("repl.py").read_text(encoding="utf-8")
    assert "_piecewise_aware_zero" not in src
