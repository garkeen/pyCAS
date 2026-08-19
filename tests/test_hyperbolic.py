import math
import unittest

from cas import term as T
from cas.term import S, sinh, cosh, tanh
from cas.parser import parse
from cas.pprint import to_str
from cas.diff import d


x = S("x")


class TestHyperbolic(unittest.TestCase):
    """双曲函数域：FunctionSpec 红利验收——注册即得全部能力，核心代码零改动。"""

    def test_special_folding(self):
        self.assertIs(parse("sinh(0)"), T.ZERO)
        self.assertIs(parse("cosh(0)"), T.ONE)
        self.assertIs(parse("tanh(0)"), T.ZERO)

    def test_deriv_via_spec(self):
        self.assertIs(d(sinh(x), x), cosh(x))
        self.assertIs(d(cosh(x), x), sinh(x))
        self.assertEqual(to_str(d(tanh(x), x)), "-tanh(x)^2 + 1")
        self.assertEqual(to_str(d(parse("sinh(x^2)"), x)), "2*x*cosh(x^2)")

    def test_parity_rules_generated(self):
        from cas.session import Session

        s = Session()
        for rid in ("sinh_neg", "cosh_neg", "tanh_neg"):
            self.assertIn(rid, s.rules.rules)
            self.assertEqual(s.rules.rules[rid].origin, "spec")
        s.feed("sinh(-x) + cosh(-x)")
        s.auto()
        self.assertEqual(to_str(s.current), "cosh(x) - sinh(x)")

    def test_identities(self):
        from cas.session import Session

        s = Session()
        s.feed("cosh(x)^2 - sinh(x)^2")
        self.assertIs(s.apply("cosh2_sinh2"), T.ONE)
        s2 = Session()
        s2.feed("sinh(x)")
        self.assertEqual(to_str(s2.apply("sinh_def")), "1/2*(exp(x) - exp(-x))")

    def test_numeric_layer(self):
        from cas.evalnum import eval_approx

        self.assertAlmostEqual(eval_approx(parse("sinh(1)"), {}), math.sinh(1))
        self.assertAlmostEqual(eval_approx(parse("cosh(1) + tanh(1)"), {}), math.cosh(1) + math.tanh(1))


if __name__ == "__main__":
    unittest.main(verbosity=2)
