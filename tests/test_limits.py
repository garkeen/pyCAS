import unittest

from cas.parser import parse
from cas.pprint import to_str
from cas.term import S, N
from cas.limits import limit


x = S("x")


def L(s, a=0, side=None):
    return limit(parse(s), x, N(a), side=side)


class TestLimits(unittest.TestCase):
    """极限引擎：代入/消去/首阶分析/洛必达兜底，三值诚实。"""

    def test_continuity(self):
        self.assertIs(L("x^2 + 1"), N(1))
        self.assertEqual(to_str(L("x^2 + 1", 2)), "5")

    def test_classic(self):
        self.assertEqual(to_str(L("sin(x)/x")), "1")
        self.assertEqual(to_str(L("(1-cos(x))/x^2")), "1/2")
        self.assertEqual(to_str(L("(exp(x)-1)/x")), "1")
        self.assertEqual(to_str(L("log(1+x)/x")), "1")
        self.assertEqual(to_str(L("(sin(x)-x)/x^3")), "-1/6")
        self.assertEqual(to_str(L("atan(x)/x")), "1")
        self.assertEqual(to_str(L("tan(x)/x")), "1")
        self.assertEqual(to_str(L("(1-exp(x))/x")), "-1")

    def test_cancel(self):
        self.assertEqual(to_str(L("(x^2-1)/(x-1)", 1)), "2")

    def test_poles_one_sided(self):
        import cas.term as T

        self.assertIs(L("1/x", 0, "+"), T.INFINITY)
        self.assertEqual(to_str(L("1/x", 0, "-")), "-Infinity")
        # 双侧不存在：左右不一致 -> 诚实 UNKNOWN
        self.assertIsNone(L("1/x"))
        self.assertIs(L("1/x^2"), T.INFINITY)

    def test_pi_points(self):
        # π 类常数点走代入通道（mk 折叠 cos(π)）
        import cas.term as T
        from cas.term import PI

        self.assertIs(limit(parse("cos(x)"), x, PI), T.MONE)
        self.assertEqual(to_str(limit(parse("sin(x)^2"), x, PI)), "0")

    def test_zero_limit(self):
        import cas.term as T

        self.assertIs(L("x*sin(1/x)"), T.ZERO)

    def test_honest_unknown(self):
        # 振荡无极限：诚实拒答
        self.assertIsNone(L("sin(1/x)"))


class TestSeries(unittest.TestCase):
    """Taylor 级数引擎：系数表 + 环算术 + 单项式复合，本性奇点拒答。"""

    def test_tables(self):
        from fractions import Fraction as Fr
        from cas.series import series

        k0, cs = series(parse("sin(x)"), x, Fr(0), 5)
        self.assertEqual((k0, cs[1], cs[3]), (0, Fr(1), Fr(-1, 6)))
        k0, cs = series(parse("exp(x)"), x, Fr(0), 4)
        self.assertEqual(cs[2], Fr(1, 2))

    def test_composition(self):
        from fractions import Fraction as Fr
        from cas.series import series

        k0, cs = series(parse("sin(x^2)"), x, Fr(0), 6)
        self.assertEqual(cs[2], Fr(1))
        k0, cs = series(parse("exp(-x)"), x, Fr(0), 4)
        self.assertEqual(cs[1], Fr(-1))

    def test_poles(self):
        from fractions import Fraction as Fr
        from cas.series import series, leading_term

        k0, cs = series(parse("1/x^2"), x, Fr(0), 4)
        self.assertEqual((k0, cs[0]), (-2, Fr(1)))
        self.assertEqual(leading_term(parse("(sin(x)-x)/x^3"), x, Fr(0))[:2], (0, Fr(-1, 6)))

    def test_essential_honest(self):
        from fractions import Fraction as Fr
        from cas.series import series, SeriesError

        with self.assertRaises(SeriesError):
            series(parse("exp(1/x)"), x, Fr(0))


if __name__ == "__main__":
    unittest.main(verbosity=2)
