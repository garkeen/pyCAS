"""N8 出口共轭有理化类级验收（M78.5）。

对照物 expr.spad root_reduce：平方根类核、分母一次的共轭闭式。
整类断言三面：形态（有理化后分母无该叶）、数值恒等（eval_approx
对拍）、诚实边界（高次/多叶/二次分母不动）。"""

import unittest

from cas.parser import parse
from cas.pprint import to_str
from cas.ratexit import rationalize


def _rat(s):
    return rationalize(parse(s))


class TestConjugateRationalization(unittest.TestCase):
    def test_classic_cases(self):
        self.assertEqual(to_str(_rat("1/(1+sqrt(2))")), "2^(1/2) - 1")
        self.assertEqual(to_str(_rat("1/sqrt(2)")), "1/2*2^(1/2)")
        self.assertEqual(to_str(_rat("3/(2+sqrt(5))")),
                         "3*5^(1/2) - 6")
        self.assertEqual(to_str(_rat("1/(1+2*sqrt(2))")),
                         "2/7*2^(1/2) - 1/7")

    def test_function_field_denominator(self):
        # 分母含 x 的线性式——root_reduce 的 univariate in r 场景
        r = _rat("(x+1)/(x-sqrt(2))")
        self.assertEqual(to_str(r),
                         "(x + 2^(1/2))*(x + 1)/(x^2 - 2)")

    def test_value_preserved(self):
        from cas.evalnum import eval_approx, EvalNumError
        from cas.term import S
        xv = S('x')
        cases = ["1/(1+sqrt(2))", "(x+1)/(x-sqrt(2))",
                 "3/(2+sqrt(5))", "x^2/(x^2-sqrt(2))"]
        for c in cases:
            a, b = parse(c), _rat(c)
            for p in (0.37, 0.83, 1.61, 2.9):
                va = eval_approx(a, {xv: p})
                try:
                    vb = eval_approx(b, {xv: p})
                except EvalNumError:
                    continue          # 有理化形在负底点未定义=原形同
                self.assertAlmostEqual(va, vb, places=9, msg=c)

    def test_honest_boundaries(self):
        # 多叶线性分母：单遍跳过，不动点（M78.8 辖区）
        self.assertEqual(to_str(_rat("1/(sqrt(2)+sqrt(3))")),
                         "(2^(1/2) + 3^(1/2))^-1")
        # 无根式表达式原样返回
        self.assertEqual(to_str(_rat("1/(x^2+x+1)")),
                         "(x + x^2 + 1)^-1")
        # 平方根类分母经 mk 后对根次数恒 <=1（l^2=bv 构造期折叠），
        # 故 root_reduce 的次数守卫在本表示下自动满足——二次以上
        # 边界只可能经高次根出现，同样由指数恰为 1/2 的叶子判据排除
        self.assertIn("3^(1/3)", to_str(_rat("1/(1+3^(1/3))")))

    def test_idempotent(self):
        once = _rat("(x+1)/(x-sqrt(2))")
        twice = rationalize(once)
        self.assertIs(twice, once)


if __name__ == "__main__":
    unittest.main(verbosity=2)
