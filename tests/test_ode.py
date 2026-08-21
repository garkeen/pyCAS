"""ODE 基础层验收：分类命名 + 微分回验三态诚实。"""

import unittest

from cas.ode import dsolve
from cas.parser import parse
from cas.pprint import to_str
from cas.term import S


x, y = S("x"), S("y")


def solve_eq(s):
    eq = parse(s)
    from cas import term as T

    f = T.plus(eq.args[0], T.neg(eq.args[1]))
    return dsolve(f, y, x)


class TestOdeClassification(unittest.TestCase):
    def test_direct(self):
        r = solve_eq("D(y,x) = 2*x")
        self.assertEqual(r.kind, "direct")
        self.assertEqual(r.status, "VERIFIED")
        self.assertEqual(to_str(r.sol), "C1 + x^2")

    def test_direct_trig(self):
        r = solve_eq("D(y,x) = cos(x)")
        self.assertEqual((r.kind, r.status), ("direct", "VERIFIED"))
        self.assertEqual(to_str(r.sol), "C1 + sin(x)")

    def test_linear1_constant(self):
        r = solve_eq("D(y,x) = y")
        self.assertEqual((r.kind, r.status), ("linear1", "VERIFIED"))
        self.assertEqual(to_str(r.sol), "C1*exp(x)")

    def test_linear1_forcing(self):
        r = solve_eq("D(y,x) + y = exp(x)")
        self.assertEqual(r.kind, "linear1")
        self.assertEqual(r.status, "VERIFIED")
        self.assertEqual(to_str(r.sol), "exp(-x)*(C1 + 1/2*exp(2*x))")

    def test_separable_power(self):
        r = solve_eq("D(y,x) = y^2")
        self.assertEqual((r.kind, r.status), ("separable", "VERIFIED"))
        self.assertEqual(to_str(r.sol), "(-(C1 + x))^-1")

    def test_separable_mixed(self):
        r = solve_eq("D(y,x) = x^2*y^3")
        self.assertEqual(r.kind, "separable")
        # 负分数幂显式：符号验证经采样（分支根式环层判不了零）
        self.assertIn(r.status, ("VERIFIED", "PROBABLE"))

    def test_constcoef2_complex(self):
        r = solve_eq("D(D(y,x),x) + y = 0")
        self.assertEqual((r.kind, r.status), ("constcoef2", "VERIFIED"))
        self.assertEqual(to_str(r.sol), "C1*cos(x) + C2*sin(x)")

    def test_constcoef2_distinct(self):
        r = solve_eq("D(D(y,x),x) - 3*D(y,x) + 2*y = 0")
        self.assertEqual((r.kind, r.status), ("constcoef2", "VERIFIED"))
        self.assertEqual(to_str(r.sol), "C1*exp(2*x) + C2*exp(x)")

    def test_constcoef2_repeated(self):
        r = solve_eq("D(D(y,x),x) - 2*D(y,x) + y = 0")
        self.assertEqual((r.kind, r.status), ("constcoef2", "VERIFIED"))
        self.assertEqual(to_str(r.sol), "exp(x)*(C1 + C2*x)")

    def test_unsupported_honest(self):
        # 非线性二阶 / 非多项式系数：诚实拒答
        r = solve_eq("D(D(y,x),x) + y^2 = 0")
        self.assertIsNone(r.sol)
        self.assertEqual(r.kind, "unsupported")


class TestOdeCommand(unittest.TestCase):
    def test_session_command(self):
        from cas.session import Session

        s = Session()
        out = s.handle("!dsolve D(D(y,x),x) + y = 0 y x")
        self.assertIn("C1*cos(x) + C2*sin(x)", out)
        self.assertIn("[VERIFIED, kind: constcoef2]", out)
        # 题型入账（可解释步骤）
        self.assertTrue(any(st.rule_id.startswith("kernel:dsolve") for st in s.log))


if __name__ == "__main__":
    unittest.main(verbosity=2)
