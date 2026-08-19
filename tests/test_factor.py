import unittest

from fractions import Fraction as Fr

from cas.term import S
from cas.parser import parse
from cas.poly import Poly


x = S("x")


class TestFactor(unittest.TestCase):
    def P(self, s):
        return Poly.from_term(parse(s), (x,))

    def check(self, s):
        from cas.factor import factor

        c, facs = factor(self.P(s))
        prod = Poly.one((x,)).scalar(c)
        for g, m in facs:
            prod = prod * g ** m
        self.assertTrue((prod - self.P(s)).is_zero(), s)
        for g, m in facs:
            self.assertGreater(m, 0)
            self.assertGreater(g.degree(x), 0)

    def test_cases(self):
        cases = [
            "x^2-1", "x^2-2*x+1", "x^3-1", "x^3-8", "x^4-1", "x^4+4",
            "x^4+x^3+x^2+x+1", "x^2+1", "2*x^2+4*x+2", "x^6-1",
            "x^4-5*x^2+4", "x^4+2*x^2+1", "6*x^2-5*x-6", "x^5-1",
            "x^2-3", "x^3+3*x^2+3*x+1", "x^4+x^2+1", "x^8-1",
            "x^3-2*x^2-x+2", "x^5+x^4+x^3+x^2+x", "3*x^2+5*x+2",
            "x^2+4*x+4", "2*x^2-8", "x^4-16", "4*x^2-9",
            "x^3+2*x^2-x-2", "x^5-32", "x^4-8*x^2+16", "9*x^2-1",
            "x^3+6*x^2+11*x+6", "2*x^3-3*x^2-3*x+2", "x^7-1",
            "x^2+x+1", "x^3-2", "x^4+3*x^2+2", "8*x^3+1",
        ]
        for s in cases:
            self.check(s)

    def test_known_factors(self):
        from cas.factor import factor

        c, facs = factor(self.P("x^4-5*x^2+4"))
        self.assertEqual(c, Fr(1))
        self.assertEqual(set(str(g) for g, m in facs), {"x - 2", "x - 1", "x + 1", "x + 2"})

        c, facs = factor(self.P("6*x^2-5*x-6"))
        self.assertEqual(set(str(g) for g, m in facs), {"2*x - 3", "3*x + 2"})

        c, facs = factor(self.P("2*x^2+4*x+2"))
        self.assertEqual(c, Fr(2))
        self.assertEqual([str(g) for g, m in facs], ["x + 1"])
        self.assertEqual([m for g, m in facs], [2])

    def test_irreducible(self):
        from cas.factor import factor

        for s in ("x^2+1", "x^2-3", "x^4+x^3+x^2+x+1", "x^3-2"):
            c, facs = factor(self.P(s))
            self.assertEqual(len(facs), 1, s)
            self.assertEqual(c, Fr(1), s)

    def test_negative_lc(self):
        from cas.factor import factor

        c, facs = factor(self.P("-x^2+1"))
        self.assertEqual(set(str(g) for g, m in facs), {"x - 1", "x + 1"})
        prod = Poly.one((x,)).scalar(c)
        for g, m in facs:
            prod = prod * g ** m
        self.assertTrue((prod - self.P("-x^2+1")).is_zero())


class TestApart(unittest.TestCase):
    def P(self, s):
        return Poly.from_term(parse(s), (x,))

    def check(self, num, den):
        from cas.apart import apart

        f = self.P(num)
        g = self.P(den)
        q, terms = apart(f, g)
        tot = q * g
        for nn, dd, k in terms:
            tot = tot + nn * g.udivmod(dd ** k)[0]
        self.assertTrue((tot - f).is_zero(), f"{num}/{den}")

    def test_cases(self):
        for num, den in [
            ("1", "x^2-1"),
            ("x", "x^2-1"),
            ("x+1", "x^2-2*x+1"),
            ("x+1", "x^2"),
            ("x^3", "x^2-1"),
            ("1", "x^3-1"),
            ("1", "x^4-1"),
            ("x^2+1", "x^3-x"),
            ("1", "x^3-6*x^2+11*x-6"),
            ("x^2", "x^4-5*x^2+4"),
            ("x+2", "x^2+x+1"),
            ("1", "x^2+2*x+2"),
            ("3*x+5", "x^2+3*x+2"),
            ("1", "(x-1)^2*(x+1)"),
            ("x^3+1", "x^3-8"),
            ("2", "x^3-3*x^2+3*x-1"),
            ("1", "x^5-1"),
            ("1", "x^3-2"),
        ]:
            self.check(num, den)

    def test_content_sign(self):
        for num, den in [
            ("2", "2*x"),
            ("2", "-x^2+1"),
            ("-2", "x^2-1"),
            ("1", "-x+1"),
            ("1", "2*x+2"),
            ("3*x", "2*x^2-2"),
            ("1", "6*x^2-5*x-6"),
            ("-1", "x^3-1"),
        ]:
            self.check(num, den)

    def test_known_apart(self):
        from cas.apart import apart

        q, terms = apart(self.P("1"), self.P("x^2-1"))
        self.assertTrue(q.is_zero())
        pairs = set((str(nn), str(dd), k) for nn, dd, k in terms)
        self.assertEqual(pairs, {("1/2", "x - 1", 1), ("-1/2", "x + 1", 1)})

        q, terms = apart(self.P("x+1"), self.P("x^2-2*x+1"))
        pairs = set((str(nn), str(dd), k) for nn, dd, k in terms)
        self.assertEqual(pairs, {("1", "x - 1", 1), ("2", "x - 1", 2)})


if __name__ == "__main__":
    unittest.main(verbosity=2)
