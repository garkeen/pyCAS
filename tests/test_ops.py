import unittest

from cas.term import S
from cas.parser import parse
from cas.pprint import to_str
from cas import ops
from cas.errors import PolyError


x, y = S("x"), S("y")


class TestTogetherCancel(unittest.TestCase):
    def test_together(self):
        t = parse("1/x + 1/y")
        r = ops.together(t)
        self.assertEqual(to_str(r), "(x + y)/(x*y)")

    def test_cancel_common_factor(self):
        # (x^2-1)/(x-1) -> x+1（单变量约分）
        t = parse("(x^2-1)/(x-1)")
        self.assertEqual(to_str(ops.cancel(t)), "x + 1")

    def test_num_den(self):
        t = parse("1/x + 2")
        self.assertEqual(to_str(ops.numerator(t)), "2*x + 1")
        self.assertEqual(to_str(ops.denominator(t)), "x")

    def test_polynomial_denominator_one(self):
        self.assertEqual(to_str(ops.denominator(parse("x^2 + 1"))), "1")


class TestCollectCoefficient(unittest.TestCase):
    def test_collect(self):
        t = parse("(x+y)^2 + 3*x")
        r = ops.collect(t, x)
        # 规范序（按 sort_key）；x 的各幂次系数已分离
        self.assertEqual(to_str(r), "x^2 + y^2 + x*(2*y + 3)")

    def test_coefficient(self):
        t = parse("(x+y)^3")
        self.assertEqual(to_str(ops.coefficient(t, x, 2)), "3*y")
        self.assertEqual(to_str(ops.coefficient(t, x, 0)), "y^3")
        self.assertEqual(to_str(ops.coefficient(t, x, 3)), "1")

    def test_coefficient_list(self):
        t = parse("x^2 + 2*x + 3")
        self.assertEqual([to_str(c) for c in ops.coefficient_list(t, x)], ["3", "2", "1"])

    def test_non_polynomial_raises(self):
        with self.assertRaises(PolyError):
            ops.coefficient(parse("sin(x)"), x, 1)

    def test_collect_non_polynomial_falls_back(self):
        t = parse("sin(x) + sin(x)")
        self.assertEqual(to_str(ops.collect(t, x)), "2*sin(x)")


if __name__ == "__main__":
    unittest.main(verbosity=2)
