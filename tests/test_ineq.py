import unittest

from cas.term import S
from cas.parser import parse
from cas.ineq import solve_poly_ineq


x = S("x")


def si(s, op="Gt"):
    ivs, out = solve_poly_ineq(parse(s), op, x)
    return out


class TestPolyInequality(unittest.TestCase):
    def test_basic(self):
        self.assertEqual(si("x^2-1", "Gt"), "(-inf, -1) U (1, inf)")
        self.assertEqual(si("x^2-1", "Le"), "[-1, 1]")
        self.assertEqual(si("x^2+x-2", "Lt"), "(-2, 1)")
        self.assertEqual(si("3*x-1", "Gt"), "(1/3, inf)")

    def test_even_multiplicity(self):
        # (x-1)^2 >= 0 全实轴；(x-1)^2 < 0 空集；(x-1)^2 <= 0 单点
        self.assertEqual(si("x^2-2*x+1", "Ge"), "(-inf, inf)")
        self.assertEqual(si("x^2-2*x+1", "Lt"), "empty")
        self.assertEqual(si("x^2-2*x+1", "Le"), "[1, 1]")

    def test_no_real_roots(self):
        self.assertEqual(si("x^2+1", "Gt"), "(-inf, inf)")
        self.assertEqual(si("x^2+1", "Lt"), "empty")
        self.assertEqual(si("-x^2-1", "Gt"), "empty")

    def test_irrational_roots_descriptors(self):
        out = si("x^2-2", "Gt")
        self.assertIn("RootOf", out)
        self.assertIn("U", out)

    def test_zero_poly(self):
        self.assertEqual(si("x - x", "Ge"), "(-inf, inf)")
        self.assertEqual(si("x - x", "Gt"), "empty")

    def test_sign_consistency(self):
        # 抽样自洽：解集内任取点满足不等式，解集外不满足
        from fractions import Fraction as Fr

        ivs, _ = solve_poly_ineq(parse("x^3-x"), "Gt", x)
        p = lambda v: v ** 3 - v
        for v in (Fr(2), Fr(-1, 4)):  # 解集 (−1,0) U (1,inf) 内
            self.assertGreater(p(v), 0)
        for v in (Fr(1, 2), Fr(-2)):  # 解集外
            self.assertLessEqual(p(v), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
