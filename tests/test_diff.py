import unittest

from cas.term import S, N, plus, times, sin, cos
from cas.simplify import simplify
from cas.diff import d, verify


x = S("x")


class TestDiff(unittest.TestCase):
    def test_basic(self):
        self.assertIs(d(plus(x, sin(x)), x), plus(N(1), cos(x)))

    def test_product(self):
        e = times(x, sin(x))
        self.assertIs(simplify(d(e, x)), plus(sin(x), times(x, cos(x))))

    def test_verify(self):
        F = plus(times(x, sin(x)), cos(x))
        self.assertEqual(verify(F, x, times(x, cos(x))), "VERIFIED")


if __name__ == "__main__":
    unittest.main(verbosity=2)
