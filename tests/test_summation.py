import unittest

from cas.parser import parse
from cas.pprint import to_str
from cas import summation as sm
from cas.term import S


class TestBernoulli(unittest.TestCase):
    def test_values(self):
        from fractions import Fraction as Fr
        self.assertEqual(sm._bernoulli_plus(0), Fr(1))
        self.assertEqual(sm._bernoulli_plus(1), Fr(1, 2))
        self.assertEqual(sm._bernoulli_plus(2), Fr(1, 6))
        self.assertEqual(sm._bernoulli_plus(4), Fr(-1, 30))
        self.assertEqual(sm._bernoulli_plus(6), Fr(1, 42))


class TestPowSum(unittest.TestCase):
    def test_formulas(self):
        x = S("x")
        cases = {
            0: "x",
            1: "1/2*x + 1/2*x^2",
            2: "1/6*x + 1/2*x^2 + 1/3*x^3",
            3: "1/4*x^2 + 1/2*x^3 + 1/4*x^4",
        }
        for p, expected in cases.items():
            self.assertEqual(to_str(sm.pow_sum(x, p)), expected, f"Σk^{p}")


class TestIndefSum(unittest.TestCase):
    def check(self, expr_str):
        k = S("k")
        t = parse(expr_str)
        r = sm.indef_sum(t, k)
        self.assertIsNotNone(r, f"Σ({expr_str}) should be summable")
        self.assertTrue(sm.verify_indef(r, t, k), f"Σ({expr_str}) diff verify failed")

    def test_polynomial(self):
        for s in ["1", "k", "k^2", "k^3", "k^4", "2*k^2 + 3*k + 1",
                  "a*k^2 + b*k", "k^5 - 2*k^3 + k"]:
            self.check(s)

    def test_unsupported(self):
        k = S("k")
        for s in ["1/k", "sin(k)", "exp(k)", "log(k+1)"]:
            self.assertIsNone(sm.indef_sum(parse(s), k), f"Σ({s}) should be unsupported")


class TestFiniteSum(unittest.TestCase):
    def check_num(self, expr, lo, hi, expected):
        k = S("k")
        r = sm.finite_sum(parse(expr), k, parse(str(lo)), parse(str(hi)))
        self.assertIsNotNone(r)
        self.assertIs(r, parse(str(expected)), f"Σ_{lo}^{hi} {expr}")

    def test_numeric(self):
        self.check_num("k", 1, 10, 55)
        self.check_num("k^2", 1, 10, 385)
        self.check_num("k^3", 1, 5, 225)
        self.check_num("1", 1, 100, 100)
        self.check_num("k", 5, 10, 45)
        self.check_num("2*k + 1", 1, 4, 24)

    def test_symbolic(self):
        k = S("k")
        r = sm.finite_sum(parse("k"), k, parse("1"), parse("n"))
        self.assertEqual(to_str(r), "1/2*n + 1/2*n^2")
        r = sm.finite_sum(parse("k^2"), k, parse("1"), parse("n"))
        self.assertEqual(to_str(r), "1/6*n + 1/2*n^2 + 1/3*n^3")

    def test_unsupported(self):
        k = S("k")
        self.assertIsNone(sm.finite_sum(parse("1/k"), k, parse("1"), parse("10")))


class TestGosper(unittest.TestCase):
    def check(self, expr_str, expected=None):
        k = S("k")
        t = parse(expr_str)
        r = sm.indef_sum(t, k)
        self.assertIsNotNone(r, f"Σ({expr_str}) should be summable")
        self.assertTrue(sm.verify_indef(r, t, k), f"Σ({expr_str}) diff verify failed")
        if expected is not None:
            self.assertEqual(to_str(r), expected, f"Σ({expr_str})")

    def test_rational_summable(self):
        self.check("1/(k*(k+1))", "-1/(k + 1)")
        self.check("(2*k+1)/(k^2*(k+1)^2)")

    def test_full_gosper(self):
        """完整 normal form（z 有理函数，c≠1 的情况）"""
        self.check("1/(k*(k+2))")        # 简化版做不了，完整版能做
        self.check("1/((2*k+1)*(2*k+3))")  # 裂项

    def test_unsupported(self):
        k = S("k")
        for s in ["1/k", "1/(2*k+1)", "k/(k+1)", "1/k^2", "1/(k^2+1)"]:
            self.assertIsNone(sm.indef_sum(parse(s), k), f"Σ({s}) should be unsupported")

    def test_finite_gosper(self):
        k = S("k")
        r = sm.finite_sum(parse("1/(k*(k+1))"), k, parse("1"), parse("10"))
        self.assertIs(r, parse("10/11"))
        r = sm.finite_sum(parse("1/(k*(k+1))"), k, parse("1"), parse("n"))
        self.assertEqual(to_str(r), "-1/(n + 1) + 1")
        # 完整 normal form 的定界求和
        r = sm.finite_sum(parse("1/(k*(k+2))"), k, parse("1"), parse("10"))
        self.assertEqual(to_str(r), "175/264")

    def test_session_gosper(self):
        from cas.session import Session
        s = Session()
        out = s.handle(":sum 1/(k*(k+1)) k")
        self.assertIn("VERIFIED", out)
        out = s.handle(":sum 1/(k*(k+1)) k 1 10")
        self.assertIn("10/11", out)


class TestSessionSum(unittest.TestCase):
    def test_sum_command(self):
        from cas.session import Session
        s = Session()
        out = s.handle(":sum k^2 k 1 10")
        self.assertIn("385", out)
        self.assertIn("VERIFIED", out)

    def test_sum_indef(self):
        from cas.session import Session
        s = Session()
        out = s.handle(":sum k^3 k")
        self.assertIn("VERIFIED", out)

    def test_sum_noun_value(self):
        from cas.session import Session
        s = Session()
        s.current = s._parse_in("sum(x^2, x)")
        out = s.handle(":value")
        self.assertIn("1/3*x^3", out)

    def test_sum_unsupported(self):
        from cas.session import Session
        s = Session()
        out = s.handle(":sum 1/k k")
        self.assertIn("unsupported", out)


if __name__ == "__main__":
    unittest.main()
