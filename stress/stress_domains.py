"""域层随机压力台架（cas_v3_arch.md 九 验收方法论）。

五条性质，全部自证：
  P5 多项式往返    random Poly -> to_term -> from_term == 原 monos
  P6 构造等价      同多项式不同构造顺序 -> equal YES
  P7 不等否定      p vs p+常数 -> equal NO
  P8 有理函数交叉  a/b vs (a*c)/(b*c) -> equal YES；a/b vs (a+1)/b -> NO
  P9 GCD 整除      gcd(a,b) 整除 a 与 b（单变量域上精确除法验证）

用法：python stress/stress_domains.py [轮数] [种子]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.term import S, N, mk, plus, times, pw
from cas.parser import parse
from cas.pprint import to_str
from cas.domains.poly import (Poly, p_add, p_mul, p_neg, p_pow, p_scale,
                              p_const, p_zero, p_gcd_univar,
                              p_divmod_field, from_term, to_term,
                              _norm)
from cas.domains.ratfunc import rf_from_term, rf_equal, RatFunc
from cas.domains.q import Q_RING
from cas.domains import poly_domain, ratfunc_domain

X, Y = S("x"), S("y")


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_coef(rng):
    n = rng.randint(-9, 9)
    d = rng.choice((1, 1, 1, 2, 3, 4, 5))
    return Fr(n, d)


def rand_poly_uni(rng, n_terms=None):
    """随机单变量 Poly（变量 X）。"""
    if n_terms is None:
        n_terms = rng.randint(1, 5)
    d = {}
    exps = rng.sample(range(0, 8), min(n_terms, 8))
    for e in exps:
        c = rand_coef(rng)
        if c != 0:
            d[(e,)] = c
    return _norm(Q_RING, (X,), d)


def rand_poly_bi(rng):
    """随机双变量 Poly（变量 X, Y）。"""
    d = {}
    for _ in range(rng.randint(1, 6)):
        ex = rng.randint(0, 4)
        ey = rng.randint(0, 4)
        c = rand_coef(rng)
        if c != 0:
            d[(ex, ey)] = d.get((ex, ey), Fr(0)) + c
    return _norm(Q_RING, (X, Y), {k: v for k, v in d.items() if v != 0})


# ---------------------------------------------------------------------------
# P5：Poly 往返一致性
# ---------------------------------------------------------------------------

def prop_poly_roundtrip(rounds, rng):
    for i in range(rounds):
        p = rand_poly_bi(rng) if rng.random() < 0.5 else rand_poly_uni(rng)
        t = to_term(Q_RING, p)
        p2 = from_term(Q_RING, t, p.vars)
        if p2 is None:
            fail("P5 from_term 返回 None", i, p)
        if p.monos != p2.monos:
            fail("P5 往返不一致", i, f"orig={p.monos}", f"rt={p2.monos}")


# ---------------------------------------------------------------------------
# P6/P7：判等完备性
# ---------------------------------------------------------------------------

def prop_equal(rounds, rng):
    """P6 因式 vs 展开判等；P7 不等否定。"""
    P = poly_domain(X)
    for i in range(rounds):
        a = rand_poly_uni(rng)
        b = rand_poly_uni(rng)
        # t1 = a*b（未展开乘积形式），t2 = p_mul 后的展开形式
        t1 = times(to_term(Q_RING, a), to_term(Q_RING, b))
        t2 = to_term(Q_RING, p_mul(Q_RING, a, b))
        r = P.equal(t1, t2)
        if r is not True:
            fail("P6 因式 vs 展开失败", i, to_str(t1), to_str(t2))
        # 不等否定：p vs p + 常数
        p = a if not a.is_zero() else p_const(Q_RING, (X,), Fr(1))
        q = p_add(Q_RING, p, p_const(Q_RING, p.vars, Fr(rng.randint(1, 9))))
        r = P.equal(to_term(Q_RING, p), to_term(Q_RING, q))
        if r is not False:
            fail("P7 不等否定失败", i, to_str(to_term(Q_RING, p)),
                 to_str(to_term(Q_RING, q)))


# ---------------------------------------------------------------------------
# P8：有理函数交叉相乘判等
# ---------------------------------------------------------------------------

def prop_ratfunc(rounds, rng):
    RF = ratfunc_domain(X)
    for i in range(rounds):
        a = rand_poly_uni(rng)
        b = rand_poly_uni(rng)
        if b.is_zero():
            continue
        c = rand_poly_uni(rng)
        if c.is_zero():
            continue
        # a/b == (a*c)/(b*c) via cross-mult
        ra = RatFunc(a, b)
        rb = RatFunc(p_mul(Q_RING, a, c), p_mul(Q_RING, b, c))
        if not rf_equal(Q_RING, ra, rb):
            fail("P8 交叉等价失败", i)
        # a/b != (a+1)/b
        a2 = p_add(Q_RING, a, p_const(Q_RING, (X,), Fr(1)))
        rb2 = RatFunc(a2, b)
        if rf_equal(Q_RING, ra, rb2):
            fail("P8 不等失败", i)


# ---------------------------------------------------------------------------
# P9：GCD 整除性
# ---------------------------------------------------------------------------

def prop_gcd(rounds, rng):
    for i in range(rounds):
        a = rand_poly_uni(rng)
        b = rand_poly_uni(rng)
        if a.is_zero() and b.is_zero():
            continue
        g = p_gcd_univar(Q_RING, a, b)
        if g.is_zero():
            continue
        # g 整除 a：a = g*q + 0
        q, r = p_divmod_field(Q_RING, a, g, 0)
        if not r.is_zero():
            fail("P9 gcd 不整除 a", i,
                 f"a={to_term(Q_RING,a)}",
                 f"g={to_term(Q_RING,g)}",
                 f"r={to_term(Q_RING,r)}")
        q, r = p_divmod_field(Q_RING, b, g, 0)
        if not r.is_zero():
            fail("P9 gcd 不整除 b", i,
                 f"b={to_term(Q_RING,b)}",
                 f"g={to_term(Q_RING,g)}",
                 f"r={to_term(Q_RING,r)}")



if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 42
    print(f"== 域层压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_poly_roundtrip(rounds, rng)
    print(f"P5 多项式往返       {rounds} 轮通过")
    prop_equal(rounds, rng)
    print(f"P6/P7 判等完备      {rounds} 轮通过")
    prop_ratfunc(min(rounds, 1000), rng)
    print(f"P8  有理函数交叉    {min(rounds,1000)} 轮通过")
    prop_gcd(min(rounds, 500), rng)
    print(f"P9  GCD 整除        {min(rounds,500)} 轮通过")
    print("== 全部通过 ==")
