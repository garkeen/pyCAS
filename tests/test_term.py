import unittest

from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N, plus, times, pw, sin, cos, log, lt, mk_bound, subst
from cas.parser import parse


x, y = S("x"), S("y")


class TestTerm(unittest.TestCase):
    def test_interning(self):
        self.assertIs(plus(x, N(1)), plus(x, N(1)))
        self.assertIs(plus(x, N(1)), plus(N(1), x))
        self.assertIsNot(plus(x, N(1)), plus(x, N(2)))

    def test_fold(self):
        self.assertIs(plus(N(1), N(2)), N(3))
        self.assertIs(times(N(2), N(3), x), times(N(6), x))
        self.assertIs(times(N(0), x), T.ZERO)
        self.assertIs(pw(N(2), N(-2)), N(Fr(1, 4)))
        self.assertIs(pw(T.ZERO, N(-1)), T.UND)
        self.assertIs(pw(T.ZERO, T.ZERO), T.UND)
        self.assertIs(T.UND, plus(T.UND, x))

    def test_alpha(self):
        self.assertIs(mk_bound("x", sin(x)), mk_bound("t", sin(S("t"))))
        self.assertIsNot(mk_bound("x", plus(x, y)), mk_bound("y", plus(x, y)))

    def test_capture_avoidance(self):
        b = mk_bound("x", plus(x, y))
        r = subst(b, {y: x})
        self.assertIs(r.body.args[0], x)
        self.assertIsInstance(r.body.args[1], T.DB)

    def test_paths(self):
        t = plus(x, times(y, x))
        self.assertIs(T.term_at(t, (1, 1)), y)
        self.assertIs(T.replace_at(t, (1, 1), N(5)), plus(x, times(x, N(5))))


class TestParser(unittest.TestCase):
    def test_parse(self):
        e = parse("x^2 + 2*x + 1")
        self.assertIs(e, plus(pw(x, N(2)), times(N(2), x), N(1)))
        e2 = parse("sin(x)*cos(x)+cos(x)*sin(x)")
        self.assertIs(e2, times(N(2), sin(x), cos(x)))
        e3 = parse("log(x*y)")
        self.assertIs(e3, log(times(x, y)))
        e4 = parse("x < 3")
        self.assertIs(e4, lt(x, N(3)))
        e5 = parse("2.5")
        self.assertIs(e5, N(Fr(5, 2)))

    def test_quote(self):
        e = parse("'x+1")
        self.assertIs(e.head, S("Quote"))


class TestCtorNormalization(unittest.TestCase):
    """地基回归：构造即规范化 / 解析结合性。"""

    def test_power_right_assoc(self):
        from cas.pprint import to_str

        self.assertEqual(to_str(parse("2^3^2")), "512")
        self.assertEqual(to_str(parse("-2^2")), "-4")
        self.assertEqual(to_str(parse("-x^2^2")), "-x^4")
        self.assertIs(parse("x^(y^z)"), parse("x^y^z"))

    def test_ctor_ring_normalization(self):
        # 构造即规范化：等项 = 同指针
        self.assertIs(parse("x*x"), pw(x, N(2)))
        self.assertIs(parse("x/x"), T.ONE)
        self.assertIs(parse("x/x^2"), pw(x, N(-1)))
        self.assertIs(parse("x^2*x^3"), pw(x, N(5)))
        self.assertIs(parse("2*x+3*x"), times(N(5), x))
        self.assertIs(parse("x+1-x"), N(1))
        # 非整数指数不合并（分支切割安全）
        self.assertIsNot(parse("x^a*x^b"), parse("x^(a+b)"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
