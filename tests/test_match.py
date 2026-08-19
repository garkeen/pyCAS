import unittest

from cas import term as T
from cas.term import S, N, plus, times, pw
from cas.match import matches


x, y = S("x"), S("y")


class TestMatch(unittest.TestCase):
    def test_repeated(self):
        self.assertEqual(len(list(matches(plus(T.PV("a"), T.PV("a")), plus(x, y)))), 0)
        m = list(matches(plus(T.PV("a"), T.PV("a")), plus(x, x)))
        self.assertEqual(len(m), 1)
        self.assertIs(m[0]["a"], x)

    def test_ac(self):
        m = list(matches(times(N(2), T.PV("u")), times(x, N(2))))
        self.assertEqual(len(m), 1)
        self.assertIs(m[0]["u"], x)

    def test_seq(self):
        m = list(matches(plus(T.PV("a"), T.PS("r")), plus(x, y, N(1))))
        self.assertTrue(any(s["r"] == (y, N(1)) or s["r"] == (N(1), y) for s in m))

    def test_nested(self):
        m = list(matches(pw(T.PV("u"), N(2)), pw(plus(x, N(1)), N(2))))
        self.assertIs(m[0]["u"], plus(x, N(1)))


class TestOneIdentity(unittest.TestCase):
    """OneIdentity：带单位元的 AC 头模式可匹配裸项（mathics 属性同款）。"""

    def test_plus_bare(self):
        ms = list(matches(plus(T.PV("a"), T.PV("b")), x))
        got = {(m["a"], m["b"]) for m in ms}
        self.assertEqual(got, {(T.ZERO, x), (x, T.ZERO)})

    def test_times_bare(self):
        ms = list(matches(times(T.PV("a"), T.PV("b")), x))
        got = {(m["a"], m["b"]) for m in ms}
        self.assertEqual(got, {(T.ONE, x), (x, T.ONE)})

    def test_typed_hole_respected(self):
        # ?a::num 只能吸收数值单位元，绑定唯一
        ms = list(matches(plus(T.PV("a", "num"), T.PV("b")), x))
        self.assertEqual(len(ms), 1)
        self.assertIs(ms[0]["a"], T.ZERO)
        self.assertIs(ms[0]["b"], x)

    def test_nonhole_not_absorbed(self):
        # 非洞子模式不吸收单位元：2*?u 不匹配裸 x
        self.assertEqual(list(matches(times(N(2), T.PV("u")), x)), [])

    def test_seq_empty(self):
        ms = list(matches(plus(T.PV("a"), T.PS("r")), x))
        self.assertTrue(any(m["a"] is x and m["r"] == () for m in ms))
        self.assertTrue(any(m["a"] is T.ZERO and m["r"] == (x,) for m in ms))


if __name__ == "__main__":
    unittest.main(verbosity=2)
