"""N1 根式规范化类级验收（M78.4）。

原则：有理底 × 指数全类 sweep + 数值预言机对拍 + 规范形幂等钉；
分支破裂负例（偶指标负底）与符号底不干涉钉。
"""

import unittest
from fractions import Fraction as Fr

from cas.term import S, N
import cas.term as T
from cas.parser import parse
from cas.pprint import to_str
from cas.evalnum import eval_approx


class TestSplitRadicalSweep(unittest.TestCase):
    """正有理底 × 约简指数：折叠后数值恒等。"""

    BASES = [Fr(2), Fr(8), Fr(12), Fr(9, 4), Fr(1, 8), Fr(72),
             Fr(5), Fr(97), Fr(1000000), Fr(3, 5)]
    EXPS = [(1, 2), (3, 2), (1, 3), (2, 3), (5, 6), (7, 3), (1, 6)]

    def test_value_preserved(self):
        for b in self.BASES:
            for p, q in self.EXPS:
                t = T.pw(N(b), N(Fr(p, q)))
                got = eval_approx(t, {})
                want = float(b) ** (p / q)
                tol = max(1e-8, abs(want) * 1e-9)
                self.assertAlmostEqual(got, want, delta=tol,
                                       msg=f"{b}^({p}/{q}) -> {to_str(t)}")

    def test_idempotent_canonical_form(self):
        # 规范形不动点：输出再构造不变
        for b in self.BASES:
            for p, q in self.EXPS:
                t1 = to_str(T.pw(N(b), N(Fr(p, q))))
                self.assertEqual(to_str(parse(t1)), t1)


class TestRadicalCanonicalPins(unittest.TestCase):
    """[m,c,r] 记录形与同次合并的精确形态钉。"""

    def test_content_sqfree_extraction(self):
        self.assertEqual(to_str(parse("sqrt(8)")), to_str(parse("2*sqrt(2)")))
        self.assertEqual(to_str(parse("sqrt(18)")), to_str(parse("3*sqrt(2)")))
        self.assertEqual(to_str(parse("16^(1/3)")), to_str(parse("2*2^(1/3)")))
        self.assertEqual(to_str(parse("(9/4)^(1/2)")), to_str(parse("3/2")))

    def test_same_index_merge(self):
        self.assertEqual(to_str(parse("sqrt(2)*sqrt(3)")),
                         to_str(parse("sqrt(6)")))
        self.assertEqual(to_str(parse("sqrt(8)*sqrt(2)")), "4")
        self.assertEqual(to_str(parse("sqrt(12)/sqrt(3)")), "2")
        # 三因子同次
        self.assertEqual(to_str(parse("sqrt(2)*sqrt(3)*sqrt(6)")), "6")

    def test_index_reduction(self):
        # 2^{5/6} 规范为 32^{1/6}（残余重数整体携带，指标归约不动点）
        self.assertEqual(to_str(parse("2^(5/6)")), to_str(parse("32^(1/6)")))

    def test_negative_odd_index(self):
        self.assertEqual(to_str(parse("(-8)^(1/3)")), "-2")

    def test_branch_break_honest_pins(self):
        # 偶指标负底：非实数，诚实不折叠（一般复底不合并）
        self.assertEqual(to_str(parse("(-4)^(1/2)")),
                         to_str(parse("sqrt(-4)")))
        self.assertEqual(to_str(parse("sqrt(-2)*sqrt(-3)")),
                         to_str(parse("sqrt(-3)*sqrt(-2)")))

    def test_symbolic_untouched(self):
        # 符号底不合并不拆分（分支安全边界）
        self.assertEqual(to_str(parse("sqrt(x)*sqrt(y)")),
                         to_str(parse("x^(1/2)*y^(1/2)")))
        self.assertEqual(to_str(parse("sqrt(x+y)")),
                         to_str(parse("(x+y)^(1/2)")))

    def test_session_class_example_pin(self):
        # 会话验收钉（例 5 族）：√a·√b 合并类全覆盖的代表形态
        self.assertEqual(to_str(parse("sqrt(2)*sqrt(6)-sqrt(3)*2")), "0")


if __name__ == "__main__":
    unittest.main(verbosity=2)
