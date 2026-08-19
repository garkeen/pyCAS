import unittest

from cas import term as T
from cas.term import S, N, plus, times, pw, neg
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify


x = S("x")
i = T.IU


class TestComplexArithmetic(unittest.TestCase):
    def test_i_powers_fold(self):
        self.assertIs(parse("i^2"), T.MONE)
        self.assertIs(parse("i^3"), neg(i))
        self.assertIs(parse("i^4"), T.ONE)
        self.assertIs(parse("i^-1"), neg(i))

    def test_complex_product(self):
        # (1+i)(1-i) = 2：纯常数乘积构造器自动展开折叠
        e = parse("(1+i)*(1-i)")
        self.assertIs(e, N(2))
        # 含符号的乘积不自动展开（展开是 expand 的职责），expand 后归零
        from cas.simplify import expand

        e2 = expand(parse("(x+i)*(x-i)"))
        self.assertIs(e2, plus(pw(x, N(2)), N(1)))

    def test_conjugate(self):
        self.assertIs(parse("conjugate(2)"), N(2))
        self.assertIs(parse("conjugate(i)"), neg(i))
        # 双重共轭消去
        self.assertIs(parse("conjugate(conjugate(x))"), x)
        # 分配：conj(x + i) = conj(x) - i
        e = parse("conjugate(x + i)")
        self.assertIs(e, plus(T.mk(S("Conjugate"), (x,)), neg(i)))


class TestComplexSolve(unittest.TestCase):
    def test_quadratic_complex(self):
        from cas.solve import solve

        r = solve(parse("x^2 + 1"), x)
        self.assertEqual(r.status, "ok")
        self.assertEqual([to_str(v) for v in r.solutions], ["i", "-i"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
