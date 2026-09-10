# -*- coding: utf-8 -*-
"""结式与无平方分解压力台架。

四条性质，全部自证、无需外部真值：
  P18 求值锚点   res(f, x−r) == f(r)（Horner 精确求值对照）
  P19 共根判据   res(f, g) = 0 ⟺ gcd(f, g) 非常数——两条独立算法交叉；
                 符号约定：res(f, g) = (−1)^(mn) res(g, f)
  P20 无平方往返 Π 因子ᵢ^重数ᵢ == monic(f)；各因子确无平方
                 （gcd(h, h') 常数）；Σ 重数·次数 == deg f

用法：python stress/stress_polytools.py [轮数] [种子]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.math.domains.q import Q_RING as R
from cas.math.domains.poly import (_norm, p_mul, p_pow, p_gcd_univar, p_deriv)
from cas.math.domains.polytools import resultant, squarefree, p_monic, p_deg
from cas.syntax.term import S

from cas.runtime import bootstrap
bootstrap()

X = S("x")
V = (X,)


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_poly(rng, maxdeg=5):
    d = {}
    for e in range(rng.randint(0, maxdeg)):
        c = Fr(rng.randint(-6, 6), rng.choice((1, 1, 2)))
        if c != 0:
            d[(e,)] = c
    if not d:
        d[(0,)] = Fr(rng.randint(1, 4))
    return _norm(R, V, d)


def nonzero(rng, maxdeg=5):
    while True:
        p = rand_poly(rng, maxdeg)
        if not p.is_zero() and p_deg(p) > 0:
            return p


def horner(p, r: Fr) -> Fr:
    acc = Fr(0)
    for e in range(p_deg(p), -1, -1):
        c = Fr(0)
        for k, cc in p.monos:
            if k[0] == e:
                c = cc
        acc = acc * r + c
    return acc


def poly_equal(a, b) -> bool:
    return a.monos == b.monos


# ---------------------------------------------------------------------------
# P18：求值锚点
# ---------------------------------------------------------------------------

def prop_eval_anchor(rounds, rng):
    for i in range(rounds):
        f = nonzero(rng)
        r = Fr(rng.randint(-4, 4), rng.choice((1, 2)))
        lin = _norm(R, V, {(1,): Fr(1), (0,): -r})
        got = resultant(R, lin, f)
        want = horner(f, r)
        if got != want:
            fail("P18 求值锚点", i, f"res={got} f(r)={want}")


# ---------------------------------------------------------------------------
# P19：共根判据 + 对称性
# ---------------------------------------------------------------------------

def prop_common_root(rounds, rng):
    for i in range(rounds):
        f, g = nonzero(rng), nonzero(rng)
        m, n = p_deg(f), p_deg(g)
        res = resultant(R, f, g)
        gcd_deg = p_deg(p_gcd_univar(R, f, g))
        if (res == 0) != (gcd_deg >= 1):
            fail("P19 共根判据", i, f"res={res} gcd_deg={gcd_deg}")
        res_swap = resultant(R, g, f)
        sign = -1 if (m * n) % 2 else 1
        if res != sign * res_swap:
            fail("P19 对称性", i, f"res={res} swap={res_swap}")
        # 构造共因子对：必判零
        c = nonzero(rng, 3)
        if resultant(R, p_mul(R, f, c), p_mul(R, g, c)) != 0:
            fail("P19 共因子未判零", i)


# ---------------------------------------------------------------------------
# P20：无平方往返
# ---------------------------------------------------------------------------

def prop_squarefree(rounds, rng):
    for i in range(rounds):
        f = nonzero(rng)
        f = p_monic(R, f)
        parts = squarefree(R, f)
        acc = _norm(R, V, {(0,): Fr(1)})
        total = 0
        for h, mult in parts:
            if p_deg(h) <= 0:
                fail("P20 常数因子", i)
            if p_deg(p_gcd_univar(R, h, p_deriv(R, h, 0))) > 0:
                fail("P20 因子含平方", i)
            acc = p_mul(R, acc, p_pow(R, h, mult))
            total += mult * p_deg(h)
        if not poly_equal(acc, f):
            fail("P20 往返不一致", i, f"deg f={p_deg(f)}")
        if total != p_deg(f):
            fail("P20 次数账目", i, f"Σ={total} deg={p_deg(f)}")


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== 结式/无平方压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_eval_anchor(rounds, rng)
    print(f"P18 求值锚点          {rounds} 轮通过")
    prop_common_root(rounds, rng)
    print(f"P19 共根判据/对称     {rounds} 轮通过")
    prop_squarefree(rounds, rng)
    print(f"P20 无平方往返        {rounds} 轮通过")
    print("== 全部通过 ==")
