"""N3 域内完全幂判定类级验收（M78.4）。

数学锚（范数预筛保证 'no' 钉的必然性）：
  y^k = x ⟹ N(x) = N(y)^k 为有理数 k 次幂。
  N(θ)=−m(0)（二次）；N(a+bθ)=a²−b²·v（θ²=v）；
  三次二项 T³−v：N(a+bθ+cθ²) = a³+v b³+v² c³ − 3vabc。
"""

import unittest
from fractions import Fraction as Fr

from cas.algfield import AlgField, AlgElem
from cas.denest import perfect_power
from cas.parser import parse
from cas.pprint import to_str


def _qf(v):
    """ℚ(√v)：T² − v。"""
    return AlgField([Fr(-v), Fr(0), Fr(1)], Fr(1))


def _cf(v):
    """ℚ(∛v)：T³ − v。"""
    return AlgField([Fr(-v), Fr(0), Fr(0), Fr(1)], Fr(1))


class TestQuadraticPerfectPower(unittest.TestCase):
    def setUp(self):
        self.f2 = _qf(2)
        self.g = self.f2.gen()

    def test_sqrt_denest_yes(self):
        # (1+√2)² = 3+2√2 —— 会话验收钉例 4 的域内核心
        x = AlgElem(self.f2, [Fr(3), Fr(2)])
        v, y = perfect_power(x, 2)
        self.assertEqual(v, 'yes')
        self.assertEqual((y ** 2).cs, x.cs)
        # 根代表元符号任意（±(1+√2) 同为精确根）
        self.assertEqual(sorted(abs(c) for c in y.cs), [Fr(1), Fr(1)])

    def test_not_square_proved_no(self):
        # θ=√2：若 y²=θ 则 N(θ)=−2=N(y)²≥0 矛盾 ⟹ proved no
        v, y = perfect_power(self.g, 2)
        self.assertEqual(v, 'no')

    def test_norm_obstruction_no(self):
        # 5+3√2：N=25−18=7 非平方 ⟹ proved no
        x = AlgElem(self.f2, [Fr(5), Fr(3)])
        v, _ = perfect_power(x, 2)
        self.assertEqual(v, 'no')

    def test_cube_yes(self):
        # (1+√2)³ = 7+5√2
        x = AlgElem(self.f2, [Fr(7), Fr(5)])
        v, y = perfect_power(x, 3)
        self.assertEqual(v, 'yes')
        self.assertEqual((y ** 3).cs, x.cs)
        self.assertEqual(sorted(abs(c) for c in y.cs), [Fr(1), Fr(1)])

    def test_rational_perfect_power_in_field(self):
        # 4 是 ℚ(√2) 内平方（平凡坐标）
        v, y = perfect_power(AlgElem(self.f2, [Fr(4)]), 2)
        self.assertEqual(v, 'yes')
        self.assertEqual(y.cs[0] ** 2, Fr(4))

    def test_fourth_power_composite_k(self):
        # (1+√2)^4 = (3+2√2)² = 17+12√2；k=4 复合指数
        x = AlgElem(self.f2, [Fr(17), Fr(12)])
        v, y = perfect_power(x, 4)
        self.assertEqual(v, 'yes')
        self.assertEqual((y ** 4).cs, x.cs)   # k=4 精确回验

    @staticmethod
    def _sq(cs):
        a, b = cs
        return [a * a + 2 * b * b, 2 * a * b]


def _sq(cs):
    a, b = list(cs) + [Fr(0)] * (2 - len(cs))
    return [a * a + 2 * b * b, 2 * a * b]


class TestCubicPerfectPower(unittest.TestCase):
    def setUp(self):
        self.f8 = _cf(2)
        self.th = self.f8.gen()

    def test_binomial_expansion_yes(self):
        # (1+θ)³ = 1+3θ+3θ²+θ³ = 3+3θ+3θ² （θ³=2）
        x = AlgElem(self.f8, [Fr(3), Fr(3), Fr(3)])
        v, y = perfect_power(x, 3)
        self.assertEqual(v, 'yes')
        self.assertEqual((y ** 3).cs, x.cs)   # 精确回验

    def test_norm_squares_no(self):
        # 2+θ：N=8+2=10 非平方 ⟹ proved no（平方情形）
        x = AlgElem(self.f8, [Fr(2), Fr(1)])
        v, _ = perfect_power(x, 2)
        self.assertEqual(v, 'no')


class TestHonestBounds(unittest.TestCase):
    def test_unknown_on_bad_input(self):
        f2 = _qf(2)
        v, _ = perfect_power("not-an-elem", 2)
        self.assertEqual(v, 'unknown')
        v, _ = perfect_power(f2.gen(), 1)
        self.assertEqual(v, 'unknown')
        v, _ = perfect_power(f2.gen(), 99)
        self.assertEqual(v, 'unknown')


class TestTermGate(unittest.TestCase):
    """N3 项级闸门接线（kernelreg.try_collapse，构造期生效）。"""

    def test_nested_collapse_principal(self):
        self.assertEqual(to_str(parse('sqrt(3+2*sqrt(2))')),
                         '2^(1/2) + 1')

    def test_honest_no_and_multi_leaf(self):
        # Q(sqrt3) 内非完全幂：不坍缩
        self.assertIn('3^(1/2)', to_str(parse('sqrt(3+2*sqrt(3))')))

    def test_cross_quad_collapse(self):
        # 跨域二次坍缩（rsimp p₂c）：√(5+2√6)=√2+√3（y∉ℚ(√6)）
        self.assertEqual(to_str(parse('sqrt(5+2*sqrt(6))')),
                         '2^(1/2) + 3^(1/2)')
        self.assertEqual(to_str(parse('sqrt(7+4*sqrt(3))')),
                         '3^(1/2) + 2')


if __name__ == "__main__":
    unittest.main(verbosity=2)
