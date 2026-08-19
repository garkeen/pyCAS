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


if __name__ == "__main__":
    unittest.main(verbosity=2)
