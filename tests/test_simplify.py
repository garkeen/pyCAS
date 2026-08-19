import unittest

from cas import term as T
from cas.term import S, N, plus, times, pw
from cas.simplify import simplify


x = S("x")


class TestSimplify(unittest.TestCase):
    def test_collect(self):
        e = plus(times(N(2), x), times(N(3), x))
        self.assertIs(simplify(e), times(N(5), x))
        e2 = plus(times(N(2), x), times(N(-2), x))
        self.assertIs(simplify(e2), T.ZERO)

    def test_power(self):
        self.assertIs(simplify(times(x, x)), pw(x, N(2)))
        self.assertIs(simplify(pw(x, N(1))), x)
        self.assertIs(simplify(pw(pw(x, N(2)), N(3))), pw(x, N(6)))


class TestExplicitStack(unittest.TestCase):
    """显式工作栈：深表达式不触及 Python 递归上限。"""

    def _deep(self, depth):
        from cas.term import sin as _sin

        e = x
        for _ in range(depth):
            e = _sin(e)
        return e

    def test_deep_simplify(self):
        e = self._deep(3000)
        # 远超 Python 默认递归深度，旧递归实现必 RecursionError
        self.assertIs(simplify(e, budget=100000), e)

    def test_deep_subst(self):
        from cas.term import subst, S as _S

        e = self._deep(3000)
        r = subst(e, {_S("x"): _S("y")})
        # 沿链下行 3000 层，内层应为 y
        inner = r
        for _ in range(3000):
            inner = inner.args[0]
        self.assertIs(inner, _S("y"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
