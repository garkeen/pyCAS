import unittest

from cas.term import S
from cas.parser import parse
from cas.pprint import to_str
from cas.poly import Poly, mgcd, div_exact
from cas.errors import PolyError
from cas import ops
from cas.ratfunc import RatFunc


x, y = S("x"), S("y")


def P(s):
    return Poly.from_term(parse(s), (x, y))


class TestMgcd(unittest.TestCase):
    def test_basic(self):
        self.assertEqual(to_str(mgcd(P("(x+y)*(x-y)"), P("(x+y)^2")).to_term()), "x + y")
        self.assertEqual(to_str(mgcd(P("x^2*y + x*y^2"), P("x^2 - y^2")).to_term()), "x + y")

    def test_content_gcd(self):
        # 多项式 content gcd：(y+1) 同时整除两式
        g = mgcd(P("(y+1)*x + (y+1)"), P("(y+1)*x + 2*(y+1)"))
        self.assertEqual(to_str(g.to_term()), "y + 1")

    def test_coprime(self):
        g = mgcd(P("(x+1)*(y+1)"), P("(x+1)*(y+2)"))
        self.assertEqual(to_str(g.to_term()), "x + 1")

    def test_univariate_fallback(self):
        g = mgcd(Poly.from_term(parse("x^2-1"), (x,)), Poly.from_term(parse("x^2+2*x+1"), (x,)))
        self.assertEqual(to_str(g.to_term()), "x + 1")


class TestDivExact(unittest.TestCase):
    def test_exact(self):
        f = P("(x+y)*(x^2+1)*(y-1)")
        d = P("(x+y)*(y-1)")
        self.assertEqual(to_str(div_exact(f, d).to_term()), "x^2 + 1")

    def test_not_exact_raises(self):
        with self.assertRaises(PolyError):
            div_exact(P("x^2 + y"), P("x + y"))


class TestMultivariateCancel(unittest.TestCase):
    def test_cancel(self):
        self.assertEqual(to_str(ops.cancel(parse("(x^2-y^2)/(x-y)"))), "x + y")
        self.assertEqual(
            to_str(ops.together(parse("(x^2-y^2)/(x-y) + 1"))), "x + y + 1"
        )

    def test_ratfunc_multivariate(self):
        rf = RatFunc.from_term(parse("(x^2-y^2)/(x-y)"), (x, y))
        self.assertEqual(to_str(rf.to_term()), "x + y")

    def test_parameter_style(self):
        # 参数 a：(a*x)/(a) 约分为 x（a 视为变量之一）
        a = S("a")
        rf = RatFunc.from_term(parse("(a*x)/(a)"), (x, a))
        self.assertEqual(to_str(rf.to_term()), "x")


if __name__ == "__main__":
    unittest.main(verbosity=2)
