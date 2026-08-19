import unittest

from cas.term import S
from cas.parser import parse
from cas.pprint import to_str


x = S("x")


class TestSolve(unittest.TestCase):
    def setUp(self):
        from cas.solve import solve, check_solution

        self.solve = solve
        self.check = check_solution

    def sols(self, expr, var="x"):
        r = self.solve(parse(expr), S(var))
        return r

    def test_linear(self):
        r = self.sols("2*x - 4")
        self.assertEqual(r.status, "ok")
        self.assertEqual(to_str(r.solutions[0]), "2")
        r = self.sols("x + 2 = 5")
        self.assertEqual(to_str(r.solutions[0]), "3")
        r = self.sols("x/2 = 3")
        self.assertEqual(to_str(r.solutions[0]), "6")

    def test_linear_param(self):
        r = self.sols("a*x - b")
        self.assertEqual(r.status, "ok")
        self.assertEqual(len(r.provisos), 1)
        self.assertEqual(to_str(r.provisos[0]), "a != 0")
        self.assertEqual(to_str(r.solutions[0]), "b/a")

    def test_linear_degenerate(self):
        r = self.sols("0*x - 1")
        self.assertEqual(r.status, "contradiction")
        r = self.sols("x - x")
        self.assertEqual(r.status, "identity")

    def test_quadratic(self):
        r = self.sols("x^2 - 5*x + 6")
        self.assertEqual([to_str(v) for v in r.solutions], ["2", "3"])
        r = self.sols("x^2 + 2*x + 1")
        self.assertEqual([to_str(v) for v in r.solutions], ["-1"])

    def test_quadratic_surds(self):
        r = self.sols("x^2 - 2")
        self.assertEqual([to_str(v) for v in r.solutions], ["2^(1/2)", "-2^(1/2)"])
        for v in r.solutions:
            self.assertEqual(self.check(parse("x^2 - 2"), v, x), "VERIFIED")

    def test_quadratic_complex_roots(self):
        # 复数域：x^2+1 = 0 的根为 ±i（纯符号）
        r = self.sols("x^2 + 1")
        self.assertEqual(r.status, "ok")
        self.assertEqual([to_str(v) for v in r.solutions], ["i", "-i"])
        for v in r.solutions:
            self.assertEqual(self.check(parse("x^2 + 1"), v, x), "VERIFIED")
        r2 = self.sols("x^2 - 2*x + 5")
        self.assertEqual([to_str(v) for v in r2.solutions], ["2*i + 1", "-2*i + 1"])

    def test_cubic_rational_roots(self):
        r = self.sols("x^3 - x")
        self.assertEqual([to_str(v) for v in r.solutions], ["-1", "0", "1"])
        r = self.sols("x^3 - 6*x^2 + 11*x - 6")
        self.assertEqual([to_str(v) for v in r.solutions], ["1", "2", "3"])
        for v in r.solutions:
            self.assertEqual(self.check(parse("x^3 - 6*x^2 + 11*x - 6"), v, x), "VERIFIED")

    def test_unsupported(self):
        # 超越与多项式混合：无逆函数结构，诚实拒答
        r = self.sols("sin(x) + x - 2")
        self.assertEqual(r.status, "unsupported")

    def test_inverse_principal(self):
        # 主支逆解（spec.inv 声明驱动；特殊点折叠自动）
        r = self.sols("sin(x) - 1")
        self.assertEqual(to_str(r.solutions[0]), "1/2*π")
        self.assertIn("principal", r.note)
        r2 = self.sols("exp(x) - 2")
        self.assertEqual(to_str(r2.solutions[0]), "log(2)")
        r3 = self.sols("log(x) - 1")
        self.assertEqual(to_str(r3.solutions[0]), "exp(1)")
        r4 = self.sols("cos(x)")
        self.assertEqual(to_str(r4.solutions[0]), "1/2*π")
        r5 = self.sols("sin(x) - 1/2")
        self.assertEqual(to_str(r5.solutions[0]), "arcsin(1/2)")

    def test_param_lowdeg(self):
        # 系数域首付款：参数化二次方程通用求根公式
        r = self.sols("a*x^2 + b*x + c")
        self.assertEqual(r.status, "ok")
        self.assertEqual(len(r.solutions), 2)
        self.assertEqual([to_str(g) for g in r.provisos], ["a != 0"])
        # 根含判别式根式
        self.assertIn("b^2", to_str(r.solutions[0]).replace(" ", "") + to_str(r.solutions[1]).replace(" ", ""))
        # 退化到线性
        r2 = self.sols("a*x + b")
        self.assertEqual(to_str(r2.solutions[0]), "-b/a")
        # 带参数的三次：诚实 unsupported
        r3 = self.sols("a*x^3 + x")
        self.assertEqual(r3.status, "unsupported")

    def test_check_unverified(self):
        r = self.sols("x^2 - 5*x + 6")
        e = self.check(parse("x^2 - 5*x + 6"), S("a"), x)
        self.assertEqual(e, "UNVERIFIED")

    def test_session_solve(self):
        from cas.session import Session

        s = Session()
        out = s.solve("x^2 - 5*x + 6 = 0", "x")
        self.assertIn("2", out)
        self.assertIn("3", out)

    def test_auto_channel(self):
        from cas.session import Session

        s = Session()
        s.feed("exp(log(x)) + 2*exp(log(x))")
        s.auto()
        self.assertEqual(to_str(s.current), "3*x")
        s2 = Session()
        s2.feed("log(x*y) + exp(log(x))")
        s2.auto()
        self.assertIn("log(x*y)", to_str(s2.current))


if __name__ == "__main__":
    unittest.main(verbosity=2)
