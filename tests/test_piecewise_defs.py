import unittest

from cas import term as T
from cas.term import S
from cas.parser import parse
from cas.pprint import to_str
from cas.diff import d


x = S("x")


class TestPiecewise(unittest.TestCase):
    """Piecewise 一等头：mk 归一、打印、逐分支微分、abs 分段定理。"""

    def test_parse_and_print(self):
        t = parse("piecewise(x, x >= 0, -x, x < 0)")
        self.assertEqual(to_str(t), "piecewise(x if x >= 0, -x if x < 0)")

    def test_prune_false_and_true_cutoff(self):
        t = parse("piecewise(1, false, 2, true, 3, x > 1)")
        # false 剪除、true 截断尾部后仅剩单 true 分支 -> 塌缩为值本身
        self.assertIs(t, T.N(2))
        self.assertIs(parse("piecewise(1, false)"), T.UND)

    def test_pattern_stays_noun(self):
        from cas.loader import parse_rules

        r = parse_rules("rule pw = piecewise(?v, ?c) -> ?v")[0]
        self.assertIsInstance(r.pattern, T.Expr)
        self.assertEqual(r.pattern.head.name, "Piecewise")

    def test_diff_distributes(self):
        t = parse("piecewise(x^2, x >= 0, -x^2, x < 0)")
        self.assertEqual(to_str(d(t, x)), "piecewise(2*x if x >= 0, -2*x if x < 0)")

    def test_abs_def_rule(self):
        from cas.session import Session

        s = Session()
        s.feed("abs(x - 1)")
        r = s.apply("abs_def")
        self.assertEqual(to_str(r), "piecewise(x - 1 if x - 1 >= 0, -(x - 1) if true)")


class TestDefinitions(unittest.TestCase):
    """用户定义（交互式标配）：f(x) := 体 / a := 体，feed 宏展开。"""

    def S(self):
        from cas.session import Session

        return Session()

    def test_function_definition(self):
        s = self.S()
        self.assertIn("defined", s.define("f(x)", "x^2 + 1"))
        s.feed("f(2)")
        self.assertIs(s.current, T.N(5))
        s.feed("f(y)")
        self.assertEqual(to_str(s.current), "y^2 + 1")

    def test_variable_and_nested(self):
        s = self.S()
        s.assign("a", "3")
        s.assign("b", "a + 1")
        s.feed("a*x + b")
        self.assertEqual(to_str(s.current), "3*x + 4")

    def test_variable_bare_evaluation(self):
        # feed 交互输入：变量定义裸引用即求值（Mathematica 语义）
        s = self.S()
        s.assign("a", "3")
        s.feed("a")
        self.assertIs(s.current, T.N(3))

    def test_kernel_inputs_expand(self):
        s = self.S()
        s.define("g(x)", "x^2 - 1")
        self.assertIn("x = -1, 1", s.solve("g(x)", "x"))

    def test_arity_mismatch_stays(self):
        s = self.S()
        s.define("f(x)", "x^2")
        s.feed("f(1, 2)")
        self.assertEqual(to_str(s.current), "f(1, 2)")

    def test_reserved_rejected(self):
        from cas.errors import ParseError

        s = self.S()
        with self.assertRaises(ParseError):
            s.define("sin(x)", "x")
        with self.assertRaises(ParseError):
            s.assign("plus", "1")

    def test_recursive_cycle_caught(self):
        from cas.errors import BudgetExceeded

        s = self.S()
        s.assign("c", "c + 1")
        with self.assertRaises(BudgetExceeded):
            s.feed("c + c")

    def test_bare_symbol_not_expanded(self):
        # 裸符号作主语（如积分变量）优先于宏语义
        s = self.S()
        s.define("g(x)", "x^2")
        s.feed("g")
        self.assertEqual(to_str(s.current), "g")
        self.assertIn("1/2*g^2", s.integrate("g"))   # g 被当积分变量，不展开定义

    def test_undef(self):
        s = self.S()
        s.assign("a", "3")
        self.assertIn("undefined", s.undef("a"))
        s.feed("a")
        self.assertIs(s.current, S("a"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
