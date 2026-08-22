"""M5.2.5：ℚ(i) Gaussian rational 常数域。

覆盖：域算术精确性 / Poly-RatFunc-ugcd-squarefree 系数无关性 /
极点分析 RDE 在 ℚ(i)[x] 上完备判定（可积给解、不可积给证明）。
"""

import unittest
from fractions import Fraction as Fr

from cas.term import S, N
from cas.poly import Poly
from cas.errors import PolyError
from cas.gaussian import Ga

x = S("x")


class TestGaussianArithmetic(unittest.TestCase):
    def test_basic_ops(self):
        i = Ga.imag()
        self.assertEqual(i * i, Ga(-1))
        self.assertEqual((Ga(1, 2) + Ga(3, -1)), Ga(4, 1))
        self.assertEqual((Ga(1, 2) - Ga(1, 2)), Ga(0))
        # (1+i)/(1-i) = i
        self.assertEqual(Ga(1, 1) / Ga(1, -1), Ga(0, 1))
        # 逆与幂
        self.assertEqual(Ga(1, 1) ** -1, Ga(Fr(1, 2), Fr(-1, 2)))
        self.assertEqual(Ga(0, 1) ** 4, Ga(1))
        self.assertEqual(Ga(2) * Fr(1, 2), Ga(1))

    def test_zero_equiv_exact(self):
        # 零等价精确：(1+i)^2 - 2i == 0（非数值近似）
        z = Ga(1, 1) ** 2 - Ga(0, 2)
        self.assertTrue(z.is_zero())
        self.assertEqual(z, 0)

    def test_div_by_zero(self):
        with self.assertRaises(PolyError):
            Ga(1) / Ga(0)

    def test_embed_fr(self):
        self.assertEqual(Ga.promote(Fr(3, 4)), Ga(Fr(3, 4)))
        self.assertTrue(Ga(Fr(1, 2)).is_real())


class TestPolyOverGaussian(unittest.TestCase):
    def test_poly_arith(self):
        i = Ga.imag()
        px = lambda c: Poly.const((x,), c)
        # (x - i)(x + i) = x^2 + 1
        a = Poly.mono((x,), x, 1) + px(i)
        b = Poly.mono((x,), x, 1) - px(i)
        prod = a * b
        want = Poly.mono((x,), x, 2) + px(Ga(1))
        self.assertEqual(prod, want)

    def test_ugcd_over_ga(self):
        from cas.poly import ugcd

        px = lambda c: Poly.const((x,), c)
        i = Ga.imag()
        # gcd(x^2+1, x-i) = x-i（monic 规范后）
        f = Poly.mono((x,), x, 2) + px(Ga(1))
        g = Poly.mono((x,), x, 1) - px(i)
        d = ugcd(f, g)
        self.assertEqual(d.degree(x), 1)
        self.assertEqual(d.lc(x), Ga(1))

    def test_squarefree_decomp_over_ga(self):
        from cas.factor import squarefree_decomp

        px = lambda c: Poly.const((x,), c)
        i = Ga.imag()
        # (x-i)^2 (x+i)：无平方分解 [(x+i,1),(x-i,2)] 类形态
        f = (Poly.mono((x,), x, 1) - px(i)) ** 2 * \
            (Poly.mono((x,), x, 1) + px(i))
        parts = squarefree_decomp(f)
        total = Poly.one((x,))
        for fac, e in parts:
            total = total * fac ** e
        self.assertEqual(total, f)

    def test_ratfunc_deriv(self):
        from cas.ratfunc import RatFunc

        i = Ga.imag()
        num = Poly.const((x,), i)
        den = Poly.mono((x,), x, 1)
        rf = RatFunc(num, den)
        d = rf.deriv(x)
        # d(i/x)/dx = -i/x^2
        want = RatFunc(Poly.const((x,), -i), Poly.mono((x,), x, 2))
        self.assertEqual(d.p, want.p)
        self.assertEqual(d.q, want.q)


class TestRdeOverGaussian(unittest.TestCase):
    """极点分析 RDE y' + λy = g 在 ℚ(i)[x] 上：可积给解、不可积给证明。"""

    def _rf(self, num_coefs, den_coefs=(Ga(1),)):
        """系数 list -> RatFunc over (x,)，Ga 元素。"""
        def build(cs):
            p = Poly.zero((x,))
            for e, c in enumerate(cs):
                if isinstance(c, Ga) and c.is_zero():
                    continue
                p = p + Poly.mono((x,), x, e) * Poly.const((x,), c)
            return p if not p.is_zero() else Poly.zero((x,))
        from cas.ratfunc import RatFunc
        return RatFunc(build(num_coefs), build(list(den_coefs)))

    def _solve(self, lam, rhs):
        from cas.risch import _rde_base_rde
        from cas.risch import DiffExt

        de = DiffExt(x)
        return _rde_base_rde(lam, rhs, de)

    def test_solve_const_imag(self):
        i = Ga.imag()
        # y' + i*y = 1 => y = 1/i = -i
        y, st = self._solve(self._rf([i]), self._rf([Ga(1)]))
        self.assertEqual(st, 'ok')
        self.assertEqual(y.const_val(), Ga(0, -1))

    def test_solve_linear_rhs(self):
        i = Ga.imag()
        # y' + 2i*y = x => y = x/(2i) + 1/( (2i)^2 ) = -i x/2 - 1/4
        y, st = self._solve(self._rf([Ga(0, 2)]), self._rf([Ga(0), Ga(1)]))
        self.assertEqual(st, 'ok')
        got = y.to_term()
        # 数值交叉核对由导数关系保证——这里直接验证系数结构：
        # y = a x + b, a = 1/(2i) = -i/2, b = -a/(2i) = -1/4
        self.assertEqual(y.p.degree(x), 1)
        ca = y.p.monos.get((1,))
        cb = y.p.monos.get((0,), Ga(0))
        self.assertEqual(ca, Ga(0, Fr(-1, 2)))
        self.assertEqual(cb * Ga(0, 2) + ca, Ga(0))

    def test_nonelementary_proved(self):
        i = Ga.imag()
        # y' + i*y = 1/x 无有理解（Ei(ix) 成分）——机器证明
        y, st = self._solve(self._rf([i]), self._rf([Ga(1)], [Ga(0), Ga(1)]))
        self.assertIsNone(y)
        self.assertEqual(st, 'proved')

    def test_nonpoly_lambda_undecided(self):
        # λ 有理（非常数分子分母）：当前理论 undecided（诚实边界）
        lam = self._rf([Ga(1)], [Ga(0), Ga(1)])       # 1/x
        y, st = self._solve(lam, self._rf([Ga(1)]))
        self.assertIsNone(y)
        self.assertEqual(st, 'undecided')


if __name__ == "__main__":
    unittest.main()
