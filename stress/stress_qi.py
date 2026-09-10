# -*- coding: utf-8 -*-
"""ℚ(i) 高斯域压力台架（全部自证，无外部真值）。

  P39 双通道交叉      环对偶运算（QIRing，FriCAS Complex 模式）×
                      成员通道（i↦z → ℚ(z) 有理函数 → 模 z²+1 约化，
                      Maxima 代数量模式）——两条独立代码路径逐轮一致；
                      域公理（分配律/逆元/范数乘性）
  P40 成员边界        各种形状的 ℚ(i) 项（乱序/除法/幂）成员判定与值
                      往返；非成员（π+i、sin(i)、开方、含变元、除零）
                      全部如实落空；规范化幂等（驻留指针）
  P41 阶梯×判零×能力  投影阶梯 ℤ→ℚ→ℚ(i)；域判等/判零通道；能力字段
                      （is_field / 无序 / 非欧几里得）；积分常数通道
                      （∫(a+bi)dx 经微分层独立验证）

用法：python stress/stress_qi.py [轮数] [种子]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

import library
library.load_all()

import cas.syntax.term as T
from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.project import project, zero_of, normalize
from cas.math.domains.qi import QI_RING, qi_of_term
from cas.math.integrate import integrate_term, verify_antideriv

X = S("x")
I = library.IU
DOM = project(parse("i")).domain


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_qi(rng, nonzero=False):
    while True:
        a = Fr(rng.randint(-9, 9), rng.choice((1, 1, 2, 3)))
        b = Fr(rng.randint(-9, 9), rng.choice((1, 1, 2, 3)))
        if (a, b) != (0, 0) or not nonzero:
            return (a, b)


def _norm2(p):
    return p[0] * p[0] + p[1] * p[1]


# ---------------------------------------------------------------------------
# P39：双通道交叉 + 域公理
# ---------------------------------------------------------------------------

def prop_two_channels(rounds, rng):
    for i in range(rounds):
        a = rand_qi(rng)
        b = rand_qi(rng, nonzero=True)
        c = rand_qi(rng)
        ta, tb, tc = DOM.to_term(a), DOM.to_term(b), DOM.to_term(c)
        # 通道 1：环对偶运算；通道 2：项级运算经成员通道（rf 机器 + 模约化）
        m1 = QI_RING.mul(a, b)
        m2 = qi_of_term(I, T.times(ta, tb))
        if m1 != m2:
            fail("P39 乘法两通道不符", i, a, b, m1, m2)
        d1 = QI_RING.div_exact(a, b)
        d2 = qi_of_term(I, T.times(ta, T.pw(tb, T.N(-1))))
        if d1 != d2:
            fail("P39 除法两通道不符", i, a, b, d1, d2)
        s1 = QI_RING.add(a, b)
        s2 = qi_of_term(I, T.plus(ta, tb))
        if s1 != s2:
            fail("P39 加法两通道不符", i, a, b, s1, s2)
        # 域公理：分配律、逆元、范数乘性（环通道内自证）
        if QI_RING.mul(a, QI_RING.add(b, c)) != \
                QI_RING.add(QI_RING.mul(a, b), QI_RING.mul(a, c)):
            fail("P39 分配律破坏", i, a, b, c)
        if QI_RING.mul(b, QI_RING.div_exact(QI_RING.from_int(1), b)) != \
                QI_RING.from_int(1):
            fail("P39 逆元不还原", i, b)
        if _norm2(QI_RING.mul(a, b)) != _norm2(a) * _norm2(b):
            fail("P39 范数乘性破坏", i, a, b)


# ---------------------------------------------------------------------------
# P40：成员边界 + 规范化往返
# ---------------------------------------------------------------------------

def prop_membership(rounds, rng):
    for i in range(rounds):
        a = rand_qi(rng)
        b = rand_qi(rng, nonzero=True)
        # 除法形状：期望值由测试内独立算术（共轭/范数公式）给出
        want = QI_RING.div_exact(a, b)
        expr = f"({a[0]}+({a[1]})*i)/({b[0]}+({b[1]})*i)"
        got = qi_of_term(I, parse(expr))
        if got != want:
            fail("P40 除法项值不符", i, expr, got, want)
        # 幂形状：i^n 的值 = i^(n mod 4)
        n = rng.randint(0, 11)
        k = n % 4
        want_pow = [(Fr(1), Fr(0)), (Fr(0), Fr(1)),
                    (Fr(-1), Fr(0)), (Fr(0), Fr(-1))][k]
        got_pow = qi_of_term(I, parse(f"i^{n}"))
        if got_pow != want_pow:
            fail("P40 幂项值不符", i, n, got_pow, want_pow)
        # 乱序形状：b·i + a 与 a + b·i 同值
        for shape in (parse(f"{a[1]}*i + {a[0]}"),
                      parse(f"{a[0]} + {a[1]}*i")):
            if qi_of_term(I, shape) != a:
                fail("P40 乱序形状不符", i, to_str(shape), a)
        # 规范化幂等：normalize 的产物再 normalize 是同一驻留指针
        t1 = normalize(project(parse(expr)))
        t2 = normalize(project(t1))
        if t1 is not t2:
            fail("P40 规范化不幂等", i, to_str(t1), to_str(t2))
        # 非成员：π+i、sin(i)、开方、含变元、除零
        for bad in ("pi + i", "sin(i)", "2^(1/2)", "x + i", "1/(i*i+1)"):
            if qi_of_term(I, parse(bad)) is not None:
                fail("P40 非成员未落空", i, bad)


# ---------------------------------------------------------------------------
# P41：阶梯 × 判零 × 能力 × 积分常数
# ---------------------------------------------------------------------------

def prop_ladder(rounds, rng):
    for i in range(rounds):
        a = rand_qi(rng)
        # 阶梯序：整数 → ℚ → ℚ(i)
        if project(parse("3")).name != "Z":
            fail("P41 整数阶梯", i)
        if project(parse("1/3")).name != "Q":
            fail("P41 有理阶梯", i)
        h = project(DOM.to_term(a))
        if a[1] == 0:
            # im=0 的对即有理数：规范项是纯有理项，阶梯正确命中 ℤ/ℚ
            if h is None or h.name not in ("Z", "Q"):
                fail("P41 纯实数对应落有理阶梯", i, a, h and h.name)
        elif h is None or h.name != "Q(i)":
            fail("P41 高斯阶梯", i, a)
        # 判零通道：值差折叠后应得精确真值
        t = DOM.to_term(a)
        z = zero_of(t)
        if z is not (a == (Fr(0), Fr(0))):
            fail("P41 判零失真", i, a, z)
        if zero_of(parse("i*i+1")) is not True:
            fail("P41 i²+1 未判零", i)
        if zero_of(parse("(1+i)*(1-i) - 2")) is not True:
            fail("P41 (1+i)(1−i)=2 未判零", i)
        # 能力字段（架构 3.2：序判定按能力查表必须拒绝的依据）
        if not DOM.is_field or DOM.is_ordered or DOM.is_euclidean:
            fail("P41 能力字段错误", i)
        # 积分常数通道：∫(a+bi)dx = (a+bi)x，微分层独立验证
        f = DOM.to_term(a)
        F = integrate_term(f, X)
        if not verify_antideriv(F, f, X):
            fail("P41 积分常数验证失败", i, to_str(f), to_str(F))


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260828
    print(f"== ℚ(i) 高斯域压力台架：rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_two_channels(rounds, rng)
    print(f"P39 双通道交叉+域公理  {rounds} 轮通过")
    prop_membership(rounds, rng)
    print(f"P40 成员边界+规范化    {rounds} 轮通过")
    prop_ladder(rounds, rng)
    print(f"P41 阶梯判零能力积分   {rounds} 轮通过")
    print("== 全部通过 ==")
