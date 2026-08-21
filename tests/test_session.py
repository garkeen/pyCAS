import unittest

from cas.term import S, plus, neg, sin, log
from cas.parser import parse
from cas.pprint import to_str


x, y = S("x"), S("y")


class TestSessionFlow(unittest.TestCase):
    def test_suggest_apply_undo(self):
        from cas.session import Session

        s = Session()
        s.feed("x + sin(-x)")
        sug = s.suggest()
        self.assertIn("sin_neg", [r[0] for r in sug])
        res = s.apply("sin_neg", (1,))
        self.assertIs(res, plus(x, neg(sin(x))))
        s.undo()
        self.assertIs(s.current, plus(x, sin(neg(x))))

    def test_obligation_flow(self):
        from cas.session import Session

        s = Session()
        s.feed("log(x*y)")
        out = s.apply("log_prod")
        self.assertIn("obligation", out)
        self.assertEqual(len(s.obligations), 1)
        s.assume("x>0")
        out2 = s.answer(s.obligations[0].oid if s.obligations else 1, "y>0")
        self.assertIs(s.current, plus(log(x), log(y)))

    def test_contradiction_lock(self):
        from cas.session import Session

        s = Session()
        s.assume("a>0")
        r = s.assume("a<0")
        self.assertIn("CONTRADICTION", r)
        self.assertIsNotNone(s.locked)

    def test_lock_blocks_further_work(self):
        from cas.session import Session

        s = Session()
        s.assume("a>0")
        s.assume("a<0")
        self.assertIsNotNone(s.locked)
        with self.assertRaises(ValueError):
            s.feed("a+1")

    def test_kernel_registry(self):
        from cas.session import Session

        s = Session()
        self.assertIn("solve", s.solver)
        self.assertIn("!integrate", s.commands())
        # 含空格表达式 + 末尾变量名（rsplit 不切碎表达式）
        out = s.solver["solve"].fn(s, "x^2 - 5*x + 6 = 0 x")
        self.assertIn("2", out)
        self.assertIn("3", out)
        # 无变量时末尾数字不被误当变量
        self.assertEqual(s.solver["solve"].fn(s, "2*x - 4"), "x = 2   [VERIFIED]")
        self.assertEqual(s.solver["factor"].fn(s, ""), "usage: !factor <expr>")


class TestExplainableSteps(unittest.TestCase):
    """可解释步骤：规则步逐条推导，算法步只报算法名+验证态（verify 背书即解释）。"""

    def test_kernel_step_logged(self):
        from cas.session import Session

        s = Session()
        out = s.integrate("1/(x^2-1)")
        self.assertIn("VERIFIED", out)
        self.assertIn("Hermite", out)   # 策略通道报所用方法
        algo = [st for st in s.log if st.rule_id.startswith("kernel:")]
        self.assertEqual(len(algo), 1)
        self.assertIn("[algorithm]", s.steps()[-1])

    def test_rule_step_explained(self):
        from cas.session import Session

        s = Session()
        s.feed("x + sin(-x)")
        s.apply("sin_neg")
        ln = s.steps()[-1]
        self.assertIn("[rule sin_neg]", ln)
        self.assertIn("x + sin(-x)", ln)
        self.assertIn("x - sin(x)", ln)

    def test_replay_skips_kernel_steps(self):
        from cas.session import Session

        s = Session()
        s.feed("1/(x^2-1)")
        s.integrate("1/(x^2-1)")
        r = s.replay()
        # 算法步直接恢复输出，不卡死
        self.assertIn("log", to_str(r))


class TestHistoryReuse(unittest.TestCase):
    """% 历史复用（Mathematica %/%% 同款最小版）。"""

    def test_percent_latest(self):
        from cas.session import Session

        s = Session()
        s.feed("x + 1")
        self.assertEqual(to_str(parse(s.expand_history("% * 2"))), "2*(x + 1)")

    def test_percent_n_parenthesized(self):
        from cas.session import Session

        s = Session()
        s.feed("1/(x^2-1)")
        s.integrate(s.expand_history("%1"))   # REPL 层负责 % 展开
        # %2 是和式，嵌入乘法必须补括号（不破语义）
        e = parse(s.expand_history("%2 * 2"))
        self.assertEqual(len(e.args), 2)   # Times 两因子，而非散开

    def test_missing_history(self):
        from cas.session import Session
        from cas.errors import ParseError

        s = Session()
        with self.assertRaises(ParseError):
            s.expand_history("% + 1")
        s.feed("x")
        with self.assertRaises(ParseError):
            s.expand_history("%5 + 1")


class TestDeclareAndConsume(unittest.TestCase):
    """declare/属性消费闭环：属性入账本，decide 区间通道消费。"""

    def test_declare_sign(self):
        from cas.session import Session

        s = Session()
        self.assertIn("assumed", s.declare("x", "positive"))
        from cas.decide import decide, T3

        self.assertIs(decide(parse("x > 0"), s.ctx), T3.YES)

    def test_declare_integer_consumed(self):
        from cas.session import Session
        from cas.decide import decide, T3

        s = Session()
        s.declare("n", "integer")
        s.declare("n", "positive")
        # n∈Z ∧ n>0 ⇒ n≥1（区间收紧到整点）
        self.assertIs(decide(parse("n >= 1"), s.ctx), T3.YES)
        self.assertIs(decide(parse("n > 0"), s.ctx), T3.YES)

    def test_declare_unknown_prop(self):
        from cas.session import Session

        s = Session()
        self.assertIn("unknown property", s.declare("x", "quaternion"))


class TestEqAsRule(unittest.TestCase):
    """等式即规则：账本等式参与 auto 重写。"""

    def test_auto_uses_ledger_equation(self):
        from cas.session import Session

        s = Session()
        s.assume("x^2 = 1")
        s.feed("x^2*y + x^2")
        s.auto()
        self.assertEqual(to_str(s.current), "y + 1")
        self.assertTrue(any(st.rule_id.startswith("eq[") for st in s.log))

    def test_numeric_equation_substitution(self):
        from cas.session import Session

        s = Session()
        s.assume("x = 5")
        s.feed("x + 1")
        s.auto()
        self.assertEqual(to_str(s.current), "6")


class TestPowerRules(unittest.TestCase):
    def test_sqrt_square_auto(self):
        from cas.session import Session

        s = Session()
        s.feed("sqrt(x^2)")
        s.auto()
        self.assertEqual(to_str(s.current), "abs(x)")

    def test_pow_mul_guarded(self):
        from cas.session import Session

        s = Session()
        s.feed("(x*y)^(1/2)")
        out = s.apply("pow_mul")
        self.assertIn("obligation", out)  # 无正性假设 -> 义务
        s.assume("x > 0")
        s.assume("y > 0")
        res = s.apply("pow_mul")
        self.assertEqual(to_str(res), "x^(1/2)*y^(1/2)")


class TestReplayRobustness(unittest.TestCase):
    def test_answer_replays_by_search(self):
        # 义务创建后 current 变化（旧 path 失效），answer 仍能全式搜索重放
        from cas.session import Session

        s = Session()
        s.feed("log(x*y) + a")
        out = s.apply("log_prod")
        self.assertIn("obligation", out)
        s.feed("a + b + log(x*y)")  # log(x*y) 位置变化
        s.assume("x > 0")
        out2 = s.answer(1, "y > 0")
        self.assertIn("answered", out2)
        self.assertIn("log(x) + log(y)", to_str(s.current))

    def test_replay_cleans_ledger(self):
        from cas.session import Session

        s = Session()
        s.feed("x + sin(-x)")
        s.apply("sin_neg", (1,))
        n_before = len(s.ctx.entries)
        s.replay()
        # 重放后 step 账本条目不累积（清旧再入新）
        self.assertEqual(len(s.ctx.entries), n_before)
        self.assertEqual(to_str(s.current), "x - sin(x)")


if __name__ == "__main__":
    unittest.main(verbosity=2)
