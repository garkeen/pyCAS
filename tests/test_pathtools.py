"""子项操作通道测试（path 寻址：只操作指定子项，其余不动）。

对齐架构 §6：path 是表达式树的唯一寻址方案。value/auto/simplify/integrate
的整体版本与子项版本（*_at）共享同一套语义，子项版本将结果就地装回。
"""
import unittest

from cas.session import Session
from cas import term as T
from cas.pprint import to_str


class PathToolsTest(unittest.TestCase):
    def setUp(self):
        self.s = Session()

    def test_value_at_only_evaluates_target_subterm(self):
        s = self.s
        s.feed("integrate(exp(x), x) + integrate(sin(x), x)")
        out = s.value_at((0,))
        self.assertIn("exp(x)", out)
        self.assertIn("sin(x)", out)          # 第二个保持名词
        self.assertNotIn("cos", out)          # 未对第二个求值
        # 结构断言：第一个积分已算，第二个仍是惰性名词
        p = T.term_at(s.current, (1,))
        self.assertEqual(p.head.name, "Integrate")

    def test_auto_at_rewrites_only_subterm(self):
        s = self.s
        s.feed("exp(log(a)) + b")
        out = s.auto_at((1,))
        self.assertEqual(to_str(s.current), "a + b")

    def test_integrate_at_integrates_subterm(self):
        s = self.s
        s.feed("x^2 + x")
        out = s.integrate_at((1,))
        self.assertIn("1/3", out)
        self.assertIn("VERIFIED", out)
        self.assertEqual(to_str(s.current), "x + 1/3*x^3")

    def test_integrate_at_evaluates_inert_integral(self):
        s = self.s
        s.feed("integrate(exp(x), x) + integrate(sin(x), x)")
        out = s.integrate_at((0,))
        self.assertIn("exp(x)", out)
        self.assertIn("VERIFIED", out)
        # 第二个积分保持名词
        self.assertEqual(T.term_at(s.current, (1,)).head.name, "Integrate")

    def test_simplify_at_no_effect_is_honest(self):
        s = self.s
        s.feed("abs(x)^2 + y")
        before = s.current
        out = s.simplify_at((0,))
        self.assertIn("no simplification", out)
        self.assertIs(s.current, before)      # 无效果：状态不变

    def test_eval_inert_matches_value_semantics(self):
        from cas.session import _eval_inert
        from cas.parser import parse
        t = parse("integrate(exp(x), x) + integrate(sin(x), x)")
        r, changed = _eval_inert(t, 100000)
        self.assertTrue(changed)
        # 全树求值：两个惰性积分都被实算（value_at 的"只算第一个"靠限定子树实现）
        self.assertEqual(to_str(r), "exp(x) - cos(x)")

    def test_operations_are_recorded_in_step_log(self):
        s = self.s
        s.feed("integrate(exp(x), x) + integrate(sin(x), x)")
        s.value_at((0,))
        last = s.log[-1]
        self.assertEqual(last.rule_id, "scheme:value_at")
        self.assertEqual(last.path, (0,))


if __name__ == "__main__":
    unittest.main()