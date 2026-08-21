import unittest

from cas.parser import parse
from cas.pprint import to_str
from cas.term import S
from cas.integrate import defint, integrate


x = S("x")


def D(expr, lo, hi):
    return defint(parse(expr), x, parse(lo), parse(hi))


class TestDefint(unittest.TestCase):
    """定积分：Newton-Leibniz + 奇点拆分 + 端点极限 + 数值交叉核对。"""

    def test_basic(self):
        v, st, _ = D("x^2", "0", "1")
        self.assertEqual((to_str(v), st), ("1/3", "VERIFIED"))
        v, st, _ = D("x", "0", "2")
        self.assertEqual(to_str(v), "2")
        v, st, _ = D("1/x^2", "1", "2")
        self.assertEqual(to_str(v), "1/2")

    def test_trig_pi_bounds(self):
        v, st, _ = D("sin(x)", "0", "pi")
        self.assertEqual((to_str(v), st), ("2", "VERIFIED"))
        v, st, _ = D("cos(x)", "0", "pi/2")
        self.assertEqual(to_str(v), "1")

    def test_atan_real_form(self):
        # 负判别式二次因子走实形式（atan），不再出 RootOf；atan(1) 特殊点折叠为 π/4
        v, st, _ = D("1/(1+x^2)", "0", "1")
        self.assertEqual((to_str(v), st), ("1/4*π", "VERIFIED"))
        F, ok, _, _prov = integrate(parse("1/(x^2+1)"), x)
        self.assertEqual(to_str(F), "atan(x)")

    def test_reversed_bounds(self):
        v, st, _ = D("x", "3", "1")
        self.assertEqual((to_str(v), st), ("-4", "VERIFIED"))

    def test_divergence(self):
        v, st, note = D("1/x^2", "-1", "1")
        self.assertIsNone(v)
        self.assertEqual(st, "DIVERGES")

    def test_interior_singularity_honest(self):
        # 1/(x-1) 在 (0,2) 内奇异：端点极限不可判 -> 诚实 UNKNOWN（不给错值）
        v, st, _ = D("1/(x-1)", "0", "2")
        self.assertIsNone(v)
        self.assertIn(st, ("UNKNOWN", "DIVERGES"))

    def test_log_integrand(self):
        v, st, _ = D("(2*x+1)/(x^2+x+1)", "0", "1")
        self.assertEqual((to_str(v), st), ("log(3)", "VERIFIED"))

    def test_empty_interval(self):
        import cas.term as T

        v, st, _ = D("x^2", "1", "1")
        self.assertIs(v, T.ZERO)
        self.assertEqual(st, "VERIFIED")


class TestDefintSession(unittest.TestCase):
    def test_kernel_commands(self):
        from cas.session import Session

        s = Session()
        out = s.solver["defint"].fn(s, "sin(x) x 0 pi")
        self.assertIn("2", out)
        self.assertIn("VERIFIED", out)
        out = s.solver["limit"].fn(s, "sin(x)/x x 0")
        self.assertEqual(out, "1   [PROBABLE, numeric probe]")
        self.assertEqual(s.solver["limit"].fn(s, "sin(1/x) x 0"), "UNKNOWN")
        # 算法步入账
        self.assertTrue(any(st.rule_id.startswith("kernel:defint") for st in s.log))


class TestDefintSymmetryAndBoundaries(unittest.TestCase):
    """对称性预检 + 无原函数边界 + spec anti 补全（Log/Atan）。"""

    def test_no_antiderivative_honest_refusal(self):
        # exp(-x^2) 无初等原函数：Risch 证明性拒答（M5.1b 起带 proved 标记）
        from cas.session import Session

        s = Session()
        out = s.handle("!defint exp(-x^2) x 0 1")
        self.assertIn("unsupported", out)
        self.assertIn("proved", out)

    def test_log_anti_and_improper_endpoint(self):
        # Log anti 表项（分部积分标准结果）+ 端点瑕点单侧极限
        from cas.session import Session

        s = Session()
        self.assertIn("[VERIFIED, method: spec antiderivative table]",
                      s.handle("!integrate ln(x)"))
        out = s.handle("!defint ln(x) x 0 1")
        self.assertIn("-1", out)
        self.assertIn("VERIFIED", out)

    def test_odd_symmetry(self):
        v, st, note = D("x^5", "-3", "3")
        self.assertIs(v, parse("0"))
        self.assertEqual((st, note), ("VERIFIED", "odd about interval midpoint (reflection)"))

    def test_even_symmetry(self):
        v, st, note = D("cos(x)^2", "-1", "1")
        self.assertEqual(st, "VERIFIED")
        self.assertTrue(note.startswith("even about interval midpoint"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
