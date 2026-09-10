# -*- coding: utf-8 -*-
"""微分层随机压力台架。

四条性质，全部自证、无需外部真值：
  P10 项域交叉   随机多项式/有理函数：项层 differentiate 与域层
                 p_deriv/rf_deriv（独立实现）在有理函数域判等
  P11 线性/莱布尼茨  d(a+b)=da+db，d(ab)=a·db+b·da（项层恒等式）
  P12 泰勒 h¹    f(x+h) 视为 h 的多项式，h¹ 系数 == f'(x)——
                 经系数提取的独立通道复核
  P13 验证器独立 工作流 Diff 步骤：正确导数过域交叉验证（open），
                 故意错误的导数被验证器否决（dead）

用法：python stress/stress_diff.py [轮数] [种子]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.runtime import new_workflow
from cas.syntax.term import S, N, mk, plus, times, pw, neg
from cas.syntax import term as T
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.qarith import fold
from cas.math.diff import differentiate
from cas.math.domains.poly import (p_mul, p_add, p_const, p_deriv, from_term,
                              to_term, _norm)
from cas.math.domains.ratfunc import (RatFunc, rf_deriv, rf_from_term,
                                 ratfunc_domain)
from cas.math.domains.q import Q_RING
from cas.workflow.workflow import Claim, Diff

from cas.runtime import bootstrap
bootstrap()

X, Y, H = S("x"), S("y"), S("h")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_coef(rng):
    n = rng.randint(-9, 9)
    d = rng.choice((1, 1, 1, 2, 3, 4))
    return Fr(n, d)


def rand_poly(rng):
    """随机双变量稀疏多项式。"""
    d = {}
    for _ in range(rng.randint(1, 6)):
        k = (rng.randint(0, 4), rng.randint(0, 4))
        c = rand_coef(rng)
        if c != 0:
            d[k] = d.get(k, Fr(0)) + c
    return _norm(Q_RING, (X, Y), {k: v for k, v in d.items() if v != 0})


def rand_nonzero_poly(rng):
    while True:
        p = rand_poly(rng)
        if not p.is_zero():
            return p


def rf_equal_terms(a, b):
    """两项在 ℚ(x, y) 判等（交叉相乘，独立于项层折叠）。"""
    rfd = ratfunc_domain(X, Y)
    return rfd.equal(a, b) is True


# ---------------------------------------------------------------------------
# P10：项层微分 × 域层导数 交叉验证
# ---------------------------------------------------------------------------

def prop_cross(rounds, rng):
    for i in range(rounds):
        if rng.random() < 0.5:
            p = rand_poly(rng)
            t = to_term(Q_RING, p)
            for var, idx in ((X, 0), (Y, 1)):
                got = differentiate(t, var)
                want = to_term(Q_RING, p_deriv(Q_RING, p, idx))
                if not rf_equal_terms(got, want):
                    fail("P10 多项式交叉", i, f"t={to_str(t)} d/d{var.name}",
                         f"got={to_str(got)}", f"want={to_str(want)}")
        else:
            a, b = rand_poly(rng), rand_nonzero_poly(rng)
            rf = RatFunc(a, b)
            ta, tb = to_term(Q_RING, a), to_term(Q_RING, b)
            t = times(ta, pw(tb, N(-1)))
            for var, idx in ((X, 0), (Y, 1)):
                got = differentiate(t, var)
                d = rf_deriv(Q_RING, rf, idx)
                want = times(to_term(Q_RING, d.num),
                             pw(to_term(Q_RING, d.den), N(-1)))
                if not rf_equal_terms(got, want):
                    fail("P10 有理函数交叉", i,
                         f"t={to_str(t)} d/d{var.name}",
                         f"got={to_str(got)}", f"want={to_str(want)}")


# ---------------------------------------------------------------------------
# P11：线性 + 莱布尼茨（项层恒等式）
# ---------------------------------------------------------------------------

def prop_leibniz(rounds, rng):
    for i in range(rounds):
        a = to_term(Q_RING, rand_poly(rng))
        b = to_term(Q_RING, rand_nonzero_poly(rng))
        da, db = differentiate(a, X), differentiate(b, X)
        # d(a+b) = da + db
        if not rf_equal_terms(differentiate(plus(a, b), X), plus(da, db)):
            fail("P11 线性", i, to_str(a), to_str(b))
        # d(ab) = a·db + b·da
        want = plus(times(a, db), times(b, da))
        if not rf_equal_terms(differentiate(times(a, b), X), want):
            fail("P11 莱布尼茨", i, to_str(a), to_str(b))
        # d(a/b) = (da·b − a·db)/b²
        q = times(a, pw(b, N(-1)))
        want_q = times(plus(times(da, b), neg(times(a, db))),
                       pw(b, N(-2)))
        if not rf_equal_terms(differentiate(q, X), want_q):
            fail("P11 商规则", i, to_str(q))


# ---------------------------------------------------------------------------
# P12：泰勒 h¹ 系数 == 导数（独立通道：系数提取）
# ---------------------------------------------------------------------------

def prop_taylor(rounds, rng):
    for i in range(rounds):
        p = rand_poly(rng)
        t = to_term(Q_RING, p)
        th = T.subst(t, {X: plus(X, H)})      # f(x+h, y)
        ph = from_term(Q_RING, th, (H, X, Y))
        if ph is None:
            fail("P12 展开落域失败", i, to_str(th))
        coefs = {}
        for k, c in ph.monos:
            coefs.setdefault(k[0], {})[(k[1], k[2])] = c
        lin = _norm(Q_RING, (X, Y), coefs.get(1, {}))
        got = differentiate(t, X)
        want = to_term(Q_RING, lin)
        if not rf_equal_terms(got, want):
            fail("P12 泰勒 h¹", i, f"t={to_str(t)}",
                 f"got={to_str(got)}", f"want={to_str(want)}")


# ---------------------------------------------------------------------------
# P13：工作流验证器独立性（正确过、错误死）
# ---------------------------------------------------------------------------

def prop_workflow(rounds, rng):
    for i in range(rounds):
        p = rand_poly(rng)
        t = to_term(Q_RING, p)
        good = differentiate(t, X)
        wf = new_workflow()
        s0 = wf.add(t, Claim())
        s1 = wf.add(good, Diff(pred=s0.id, var=X))
        if s1.status != "open":
            fail("P13 正确导数被否决", i, to_str(t), to_str(good))
        bad = plus(good, N(1))
        s2 = wf.add(bad, Diff(pred=s0.id, var=X))
        if s2.status != "dead":
            fail("P13 错误导数未死", i, to_str(t), to_str(bad))


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260827
    print(f"== 微分压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_cross(rounds, rng)
    print(f"P10 项域交叉          {rounds} 轮通过")
    prop_leibniz(rounds, rng)
    print(f"P11 线性/莱布尼茨/商  {rounds} 轮通过")
    prop_taylor(min(rounds, 500), rng)
    print(f"P12 泰勒 h¹           {min(rounds,500)} 轮通过")
    prop_workflow(min(rounds, 300), rng)
    print(f"P13 验证器独立        {min(rounds,300)} 轮通过")
    print("== 全部通过 ==")
