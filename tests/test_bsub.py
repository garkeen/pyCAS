"""反向换元验收：主支逆解新限 + 三角符号窗口脱根号。"""

import unittest

from cas import term as T
from cas.bsub import _pi_coef
from cas.session import Session
from cas.term import S


x = S("x")


class TestBsub(unittest.TestCase):
    def test_sqrt_quarter_circle(self):
        # 经典：∫₀¹ √(1−x²) dx = π/4（x = sin t，√(cos²t) 经窗口脱壳）
        s = Session()
        out = s.handle(":bsub x=sin(t) sqrt(1-x^2) x 0 1")
        self.assertIn("1/4*π", out)
        self.assertIn("VERIFIED", out)
        self.assertIn("backward substitution x=sin(t)", out)

    def test_atan_substitution(self):
        # ∫₀¹ 1/(1+x²) dx = π/4（x = tan t；新限 atan(0)/atan(1) 折叠）
        s = Session()
        out = s.handle(":bsub x=tan(t) 1/(1+x^2) x 0 1")
        self.assertIn("1/4*π", out)
        self.assertIn("VERIFIED", out)

    def test_out_of_domain_bounds_honest(self):
        # sin(t) = 2 无实数解：诚实拒答（不求复数支）
        s = Session()
        out = s.handle(":bsub x=sin(t) sqrt(1-x^2) x 0 2")
        self.assertNotIn("VERIFIED", out)

    def test_unknown_inverse_honest(self):
        # h 无 spec.inv 覆盖：界方程解不出 -> 拒答
        s = Session()
        out = s.handle(":bsub x=t^3+t x x 0 1")
        self.assertNotIn("VERIFIED", out)


class TestPiCoef(unittest.TestCase):
    def test_forms(self):
        from fractions import Fraction as Fr

        self.assertEqual(_pi_coef(T.ZERO), Fr(0))
        self.assertEqual(_pi_coef(T.PI), Fr(1))
        self.assertEqual(_pi_coef(T.div(T.PI, T.N(2))), Fr(1, 2))
        self.assertEqual(_pi_coef(T.neg(T.PI)), Fr(-1))
        self.assertIsNone(_pi_coef(T.S("q")))
        self.assertIsNone(_pi_coef(T.ONE))


if __name__ == "__main__":
    unittest.main(verbosity=2)
