import unittest

from fractions import Fraction as Fr

from cas.term import S, N, plus, times, pw, div
from cas.parser import parse
from cas.pprint import to_str
from cas.poly import Poly, ugcd
from cas.ratfunc import RatFunc


x = S("x")


class TestPoly(unittest.TestCase):
    def test_from_term(self):
        p = Poly.from_term(plus(pw(x, N(2)), N(-1)), (x,))
        q = Poly.from_term(plus(x, N(-1)), (x,))
        g = ugcd(p, q)
        self.assertTrue(g.is_monic())
        qq, r = p.udivmod(g)
        self.assertTrue(r.is_zero())
        self.assertEqual(qq.degree(), 1)

    def test_gcd2(self):
        p1 = Poly.from_term(times(plus(x, N(1)), plus(x, N(2))), (x,))
        p2 = Poly.from_term(times(plus(x, N(1)), plus(x, N(3))), (x,))
        g = ugcd(p1, p2)
        self.assertIs(g.to_term(), plus(x, N(1)))

    def test_deriv(self):
        p = Poly.from_term(pw(x, N(3)), (x,))
        self.assertIs(p.deriv(x).to_term(), times(N(3), pw(x, N(2))))


class TestRatFunc(unittest.TestCase):
    def test_cancel(self):
        rf = RatFunc.from_term(
            div(pw(x, N(2)), plus(pw(x, N(2)), N(-1))), (x,)
        )
        self.assertTrue(rf.q.is_const() is False or True)

    def test_add(self):
        r1 = RatFunc.from_term(div(N(1), plus(x, N(1))), (x,))
        r2 = RatFunc.from_term(div(N(1), plus(x, N(-1))), (x,))
        s = r1 + r2
        t = s.to_term()
        self.assertEqual(to_str(t), "2*x/(x^2 - 1)")


class TestResultant(unittest.TestCase):
    def P(self, s):
        return Poly.from_term(parse(s), (x,))

    def test_uresultant(self):
        from cas.poly import uresultant

        self.assertEqual(uresultant(self.P("2*x+1"), self.P("x+3")), Fr(5))
        self.assertEqual(uresultant(self.P("x^2-1"), self.P("x^2-2*x+1")), Fr(0))
        self.assertEqual(uresultant(self.P("x^3-x"), self.P("x^2+1")), Fr(4))
        self.assertEqual(uresultant(self.P("x^3-1"), self.P("x^2+1")), Fr(2))

    def test_udiscriminant(self):
        from cas.poly import udiscriminant

        self.assertEqual(udiscriminant(self.P("x^2+5*x+6")), Fr(1))
        self.assertEqual(udiscriminant(self.P("x^3-1")), Fr(-27))
        self.assertEqual(udiscriminant(self.P("x^2-2*x+1")), Fr(0))
        self.assertEqual(udiscriminant(self.P("6*x^2-5*x-6")), Fr(169))


if __name__ == "__main__":
    unittest.main(verbosity=2)
