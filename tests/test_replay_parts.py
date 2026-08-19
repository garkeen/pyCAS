import os
import tempfile
import unittest

from cas.parser import parse
from cas.pprint import to_str
from cas.session import Session
from cas.term import S


x = S("x")


class TestTranscriptDSL(unittest.TestCase):
    """转录 DSL：handle 统一入口、命令转录、保存/回放、规则指纹。"""

    def test_handle_records_mutations(self):
        s = Session()
        s.handle("x + 1")
        s.handle(":auto")
        s.handle(":help")          # 只读命令不入转录
        s.handle(":steps")
        self.assertEqual(s.transcript, ["x + 1", ":auto"])

    def test_save_replay_roundtrip(self):
        s = Session()
        s.handle("f(x) := x^2 + 1")
        s.handle("f(2)")
        s.handle("y := %")
        s.handle("y + 1")
        fd, path = tempfile.mkstemp(suffix=".pycas")
        os.close(fd)
        try:
            out = s.handle(":save " + path)
            self.assertIn("saved 4 commands", out)
            s2 = Session()
            s2.handle(":replay " + path)
            self.assertEqual(to_str(s2.current), to_str(s.current))
            self.assertIs(s2.current, s.current)   # 驻留保证回放产物指针同一
        finally:
            os.remove(path)

    def test_replay_refuses_on_fingerprint_mismatch(self):
        s = Session()
        s.handle("x + 1")
        fd, path = tempfile.mkstemp(suffix=".pycas")
        os.close(fd)
        try:
            s.handle(":save " + path)
            s2 = Session()
            s2.rules.rules.pop(next(iter(s2.rules.rules)))   # 篡改规则集
            out = s2.handle(":replay " + path)
            self.assertIn("fingerprint mismatch", out)
        finally:
            os.remove(path)


class TestPartsShowcase(unittest.TestCase):
    """eˣsin x 展示工程：分部两次 + 解方程消循环 + 验证，全程可回放。"""

    SCRIPT = [
        "I := integrate(exp(x)*sin(x), x)",
        "I",
        ":parts sin(x)",
        ":parts cos(x)",
        "I = e^x*sin(x) - e^x*cos(x) - I",
        ":solveq integrate(exp(x)*sin(x), x)",
        ":verify % x exp(x)*sin(x)",
    ]

    def test_full_derivation(self):
        s = Session()
        outs = [s.handle(line) for line in self.SCRIPT]
        self.assertIn("VERIFIED", outs[-1])   # :verify 的输出（微分回验）
        # 每一步都入账且可解释（本剧本全是方案步：分部两次 + 线性求解）
        kinds = [st.rule_id for st in s.log]
        self.assertTrue(any(k.startswith("scheme:parts") for k in kinds))
        self.assertIn("scheme:solveq", kinds)
        self.assertEqual(len(s.log), 3)

    def test_result_value(self):
        s = Session()
        for line in self.SCRIPT[:-1]:
            s.handle(line)
        from cas.diff import verify

        # 结果 = 1/2*e^x*(sin x - cos x)，微分回验
        self.assertEqual(
            verify(s.current, x, parse("exp(x)*sin(x)")), "VERIFIED"
        )

    def test_parts_rejects_non_divisible(self):
        s = Session()
        s.handle("integrate(exp(x)*sin(x), x)")
        out = s.handle(":parts exp(2*x)")
        self.assertIn("no inert integral", out)


class TestDefintUSub(unittest.TestCase):
    """定积分正向换元：新限正向求值，全程不求逆。"""

    def test_user_example(self):
        s = Session()
        out = s.handle(":defint (e^x+x)*(e^x+1) x 0 1")
        self.assertIn("u-substitution u=x + exp(x)", out)
        # 值 = 1/2*((e+1)^2 - 1) = e + e^2/2，数值核对
        from cas.evalnum import eval_approx
        import math

        v = s.history[-1]
        self.assertAlmostEqual(eval_approx(v, {}), math.e + math.e ** 2 / 2, places=6)

    def test_nested_substitution(self):
        s = Session()
        out = s.handle(":defint 2*x*exp(x^2) x 0 1")
        self.assertIn("u-substitution", out)
        self.assertIn("VERIFIED", out)

    def test_plain_fallback(self):
        s = Session()
        out = s.handle(":defint x^2 x 0 1")
        self.assertIn("1/3", out)
        self.assertNotIn("u-substitution", out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
