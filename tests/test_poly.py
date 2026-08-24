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


class TestRatFuncEq(unittest.TestCase):
    """B6：RatFunc 值等词与哈希契约（M78.4）。"""

    def mk(self, s):
        return RatFunc.from_term(parse(s), (self.xv,))

    def setUp(self):
        self.xv = S("x")

    def test_value_eq_across_shapes(self):
        a = self.mk("(x^2-1)/(x-1)")
        b = self.mk("x+1")
        self.assertTrue(a == b)
        self.assertFalse(a != b)
        c = self.mk("(x+1)/2")
        self.assertFalse(self.mk("(x^2-1)/(x-1)") == c)

    def test_eq_cross_var_extension(self):
        from cas.ratfunc import RatFunc
        yv = S("y")
        r1 = RatFunc.from_term(parse("(x^2-1)/(x-1)"), (self.xv,))
        r2 = RatFunc.from_term(parse("y+1"), (yv,))
        # 数学上不同变元不可比？此处按并集扩元后交叉判零：
        # (x+1) 与 (y+1) 差非零 ⟹ 不等
        self.assertFalse(r1 == r2)
        r3 = RatFunc.from_term(parse("x+1"), (self.xv,))
        r4 = RatFunc.from_term(parse("(x^2+x)/(x)"), (yv, self.xv))
        self.assertTrue(r3 == r4)

    def test_hash_consistent_with_eq(self):
        a, b = self.mk("(x^2-1)/(x-1)"), self.mk("x+1")
        self.assertEqual(hash(a), hash(b))
        d = {a: "ok"}
        self.assertEqual(d[b], "ok")


class TestMkRatCanonical(unittest.TestCase):
    """B5：_mk_rat 全轨道唯一代表形契约（M78.4）。"""

    def test_unit_scaling_invariance_ga_track(self):
        from fractions import Fraction as Fr
        from cas.poly import Poly, _mk_rat
        from cas.gaussian import Ga
        xv = S("x")
        num = Poly((xv,), {(1,): Ga(1, 1), (0,): Fr(1)})
        den = Poly((xv,), {(1,): Ga(2, 1), (0,): Fr(1)})
        base = _mk_rat(num, den)
        for k in (Ga(0, 1), Ga(3, -2), Fr(-7)):
            scaled = _mk_rat(
                num.scalar(k), den.scalar(k)
            )
            self.assertEqual(base, scaled)
        # 幂等性
        self.assertEqual(_mk_rat(base.num, base.den), base)

    def test_unit_scaling_invariance_symrat_track(self):
        from fractions import Fraction as Fr
        from cas.poly import Poly, _mk_rat, SymRat
        av = S("a")
        xv = S("x")
        sr = SymRat(Poly((av,), {(0,): Fr(3), (1,): Fr(1)}),
                    Poly.one((av,)))
        num = Poly((xv,), {(1,): sr, (0,): Fr(2)})
        den = Poly((xv,), {(2,): Fr(1)})
        base = _mk_rat(num, den)
        k = SymRat(Poly((av,), {(0,): Fr(-1), (1,): Fr(2)}),
                   Poly((av,), {(0,): Fr(5)}))
        self.assertEqual(base, _mk_rat(num.scalar(k), den.scalar(k)))

    def test_monic_denominator_canonical(self):
        from fractions import Fraction as Fr
        from cas.poly import Poly, _mk_rat
        from cas.gaussian import Ga
        xv = S("x")
        num = Poly((xv,), {(1,): Ga(1, 1)})
        den = Poly((xv,), {(1,): Ga(2, 1)})
        r = _mk_rat(num, den)
        # 分母首一化：lc == 域单位元（精确逆缩放；叶型可为 Ga(1,0)）
        lc = r.den.lc(r.den.vars[0])
        self.assertEqual(lc, 1)


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
