# -*- coding: utf-8 -*-
"""积分骨架压力台架（全部自证，无外部真值）。

  P32 不定积分往返  随机多项式：verify_antideriv（微分层独立复核）为真；
                    定积分值 == 逐项幂公式参照（与"原函数代入"两条独立通道）
  P33 可加性/FTC    ∫_a^b + ∫_b^c == ∫_a^c；∫_a^a == 0
  P34 分段定积分    有理分界逐段求和 == 分段参照；缺口/点洞诚实拒答
  P35 拒答边界      真分式/超越被积式、无理积分限 → IntegrateError

用法：python stress/stress_integrate.py [轮数] [种子]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.runtime import bootstrap
bootstrap()

import cas.syntax.term as T
from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.qarith import fold
from cas.math.integrate import (integrate_term, definite_integrate,
                           verify_antideriv)
from cas.errors import IntegrateError
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import _norm, to_term
from cas.math.piecewise import piecewise

X = S("x")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_poly(rng, maxdeg=4):
    """随机 ℚ 系数单变量多项式，返回 (Poly, {(e,):Fr})。"""
    deg = rng.randint(0, maxdeg)
    d = {}
    for e in range(deg + 1):
        c = Fr(rng.randint(-9, 9), rng.choice((1, 1, 2, 3)))
        if c != 0:
            d[(e,)] = d.get((e,), Fr(0)) + c
    d = {k: c for k, c in d.items() if c != 0}
    if not d:
        d = {(0,): Fr(1)}
    return _norm(Q_RING, (X,), d), d


def ref_definite(coefs, a, b):
    """逐项幂公式参照（独立于"原函数代入"通道）。"""
    total = Fr(0)
    for (e,), c in coefs.items():
        total += c * (b ** (e + 1) - a ** (e + 1)) / Fr(e + 1)
    return total


def _num(t):
    f = fold(t)
    if not T.is_num(f):
        return None
    return T.num_val(f)


# ---------------------------------------------------------------------------
# P32：不定积分往返 + 定积分独立通道
# ---------------------------------------------------------------------------

def prop_indefinite(rounds, rng):
    for i in range(rounds):
        p, coefs = rand_poly(rng)
        f = to_term(Q_RING, p)
        F = integrate_term(f, X)
        if verify_antideriv(F, f, X) is not True:
            fail("P32 原函数验证失败", i, to_str(f), to_str(F))
        a = Fr(rng.randint(-5, 5), 1)
        b = Fr(rng.randint(-5, 5), 1)
        if a > b:
            a, b = b, a
        got = _num(definite_integrate(f, X, T.N(a), T.N(b)))
        want = ref_definite(coefs, a, b)
        if got != want:
            fail("P32 定积分两通道不符", i, to_str(f), a, b, got, want)


# ---------------------------------------------------------------------------
# P33：可加性 / ∫_a^a == 0
# ---------------------------------------------------------------------------

def prop_additivity(rounds, rng):
    for i in range(rounds):
        p, _c = rand_poly(rng, maxdeg=3)
        f = to_term(Q_RING, p)
        a, b, c = sorted(Fr(rng.randint(-6, 6), 1) for _ in range(3))
        ab = _num(definite_integrate(f, X, T.N(a), T.N(b)))
        bc = _num(definite_integrate(f, X, T.N(b), T.N(c)))
        ac = _num(definite_integrate(f, X, T.N(a), T.N(c)))
        if ab + bc != ac:
            fail("P33 可加性破坏", i, to_str(f), a, b, c, ab, bc, ac)
        aa = _num(definite_integrate(f, X, T.N(a), T.N(a)))
        if aa != 0:
            fail("P33 ∫_a^a 非零", i, to_str(f), a, aa)


# ---------------------------------------------------------------------------
# P34：分段定积分
# ---------------------------------------------------------------------------

def prop_piecewise(rounds, rng):
    for i in range(rounds):
        r = rng.randint(-3, 3)
        p1, c1 = rand_poly(rng, maxdeg=3)
        p2, c2 = rand_poly(rng, maxdeg=3)
        pw = piecewise([(to_term(Q_RING, p1), parse(f"x < {r}")),
                        (to_term(Q_RING, p2), parse(f"x >= {r}"))])
        # 全在左区（a < b < r）
        a = Fr(r - rng.randint(3, 5), 1)
        b = Fr(r - rng.randint(1, 2), 1)
        got = _num(definite_integrate(pw, X, T.N(a), T.N(b)))
        if got != ref_definite(c1, a, b):
            fail("P34 左区不符", i, a, b, got, ref_definite(c1, a, b))
        # 跨分界点
        lo = Fr(r - rng.randint(1, 3), 1)
        hi = Fr(r + rng.randint(1, 3), 1)
        got2 = _num(definite_integrate(pw, X, T.N(lo), T.N(hi)))
        want2 = ref_definite(c1, lo, Fr(r)) + ref_definite(c2, Fr(r), hi)
        if got2 != want2:
            fail("P34 跨分界不符", i, lo, hi, got2, want2)
        # 缺口拒答：x<r 与 x>r+1，中间有缺口
        gap_pw = piecewise([(parse("1"), parse(f"x < {r}")),
                            (parse("1"), parse(f"x > {r + 1}"))])
        try:
            definite_integrate(gap_pw, X, T.N(Fr(r - 2)), T.N(Fr(r + 3)))
            fail("P34 缺口未拒答", i)
        except IntegrateError:
            pass


# ---------------------------------------------------------------------------
# P35：拒答边界
# ---------------------------------------------------------------------------

def prop_refusal(rounds, rng):
    for i in range(rounds):
        # 真分式
        try:
            integrate_term(parse("1/x"), X)
            fail("P35 真分式未拒", i)
        except IntegrateError:
            pass
        # 超越
        try:
            integrate_term(parse("exp(x)"), X)
            fail("P35 超越未拒", i)
        except IntegrateError:
            pass
        # 无理积分限（x^2-2 的根不是有理数项，用符号限触发）
        try:
            definite_integrate(parse("x^2"), X, parse("y"), T.N(1))
            fail("P35 非有理限未拒", i)
        except IntegrateError:
            pass


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== 积分骨架压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_indefinite(rounds, rng)
    print(f"P32 不定往返+两通道   {rounds} 轮通过")
    prop_additivity(rounds, rng)
    print(f"P33 可加性/∫_a^a      {rounds} 轮通过")
    prop_piecewise(rounds, rng)
    print(f"P34 分段定积分        {rounds} 轮通过")
    prop_refusal(rounds, rng)
    print(f"P35 拒答边界          {rounds} 轮通过")
    print("== 全部通过 ==")
