import unittest

from fractions import Fraction as Fr

from cas.term import S
from cas.parser import parse
from cas.decide import equivalent, T3
from cas.evalnum import eval_exact, eval_approx, sample_agrees, EvalNumError


x, y = S("x"), S("y")


class TestEvalExact(unittest.TestCase):
    def test_ring(self):
        e = parse("x^2 + 3*x*y - 2")
        env = {x: Fr(1, 2), y: Fr(3, 4)}
        self.assertEqual(eval_exact(e, env), Fr(1, 4) + Fr(9, 8) - 2)

    def test_rejects_transcendental(self):
        with self.assertRaises(EvalNumError):
            eval_exact(parse("sin(x)"), {x: Fr(1)})
        with self.assertRaises(EvalNumError):
            eval_exact(parse("pi"), {})

    def test_unbound(self):
        with self.assertRaises(EvalNumError):
            eval_exact(parse("x + 1"), {})


class TestEvalApprox(unittest.TestCase):
    def test_transcendental(self):
        self.assertAlmostEqual(eval_approx(parse("sin(pi/2)"), {}), 1.0)
        self.assertAlmostEqual(eval_approx(parse("exp(0) + log(1)"), {}), 1.0)
        self.assertAlmostEqual(eval_approx(parse("abs(-3)"), {}), 3.0)

    def test_env(self):
        self.assertAlmostEqual(eval_approx(parse("x^2 + y"), {x: 2.0, y: Fr(1)}), 5.0)


class TestSampling(unittest.TestCase):
    def test_agrees(self):
        self.assertIs(sample_agrees(parse("x + x"), parse("2*x"), [x]), True)

    def test_disagreement_is_unknown_not_no(self):
        # 采样永不否证：不一致 -> 未知（None），否证必须走符号通道
        self.assertIsNone(sample_agrees(parse("x"), parse("x + 1"), [x]))

    def test_equivalent_probable(self):
        # log(x)+log(y) vs log(x*y)：符号通道需守卫无法判定，数值采样支持 -> PROBABLE
        r = equivalent(parse("log(x) + log(y)"), parse("log(x*y)"))
        self.assertIs(r, T3.PROBABLE)

    def test_equivalent_trig_yes(self):
        # 三角层决策过程：多角度基归零（符号 YES，非采样）
        self.assertIs(equivalent(parse("sin(x)^2 + cos(x)^2"), parse("1")), T3.YES)


if __name__ == "__main__":
    unittest.main(verbosity=2)
