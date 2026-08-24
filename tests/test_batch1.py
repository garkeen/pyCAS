"""第一批采购清单验收：:rule 内联定理 / 名词动词切换 / Refine / Protected / LaTeX。"""

import os
import re
import tempfile
import unittest

from cas import term as T
from cas.context import Context
from cas.latex import to_latex
from cas.parser import parse
from cas.pprint import to_str
from cas.refine import refine
from cas.session import Session


class TestInlineRules(unittest.TestCase):
    """:rule 内联定理定义（tellsimp 同款）：会话规则入规则集、入转录、可回放重建。"""

    def test_define_apply_remove(self):
        s = Session()
        self.assertIn("defined", s.handle(":rule cube_sum = ?x^3 + ?y^3 -> (?x+?y)*(?x^2-?x*?y+?y^2)"))
        self.assertEqual(s.rules.rules["cube_sum"].origin, "session")
        s.handle("a^3 + b^3")
        # :a 输出含规则步解释行，首行为结果式
        self.assertTrue(s.handle(":a cube_sum").startswith("(a + b)*(a^2 + b^2 - a*b)"))
        self.assertIn("removed", s.handle(":unrule cube_sum"))
        self.assertNotIn("cube_sum", s.rules.rules)

    def test_file_rules_protected_from_unrule(self):
        s = Session()
        self.assertIn("only session rules can be removed", s.handle(":unrule sin_neg"))

    def test_fingerprint_excludes_session_rules(self):
        # 会话规则不计指纹：否则保存后回放被自己的新规则拒死
        s = Session()
        fp0 = s.rules_fingerprint()
        s.handle(":rule tmp = ?x^3 -> ?x*?x^2")
        self.assertEqual(s.rules_fingerprint(), fp0)

    def test_replay_rebuilds_session_rule(self):
        s = Session()
        s.handle(":rule cube_sum = ?x^3 + ?y^3 -> (?x+?y)*(?x^2-?x*?y+?y^2)")
        s.handle("a^3 + b^3")
        s.handle(":a cube_sum")
        fd, path = tempfile.mkstemp(suffix=".pycas")
        os.close(fd)
        try:
            s.handle(":save " + path)
            s2 = Session()
            out = s2.handle(":replay " + path)
            self.assertIn("replayed 3 commands", out)
            self.assertIs(s2.current, s.current)   # 驻留保证指针同一
            self.assertEqual(s2.rules.rules["cube_sum"].origin, "session")
        finally:
            os.remove(path)

    def test_rules_listing(self):
        s = Session()
        s.handle(":rule tmp2 = ?x^5 -> ?x^4*?x")
        out = s.handle(":rules")
        self.assertIn("tmp2", out)
        self.assertIn("session", out)


class TestNounVerb(unittest.TestCase):
    """名词/动词切换：' 前缀名词化，:value 全式求值惰性形式。"""

    def test_inert_integral_evaluated(self):
        s = Session()
        s.handle("'integrate(x^2, x)")
        self.assertTrue(s.show().startswith("'"))
        self.assertEqual(s.handle(":value"), "1/3*x^3")
        self.assertTrue(any(st.rule_id == "kernel:value" for st in s.log))

    def test_quote_stripped(self):
        s = Session()
        s.handle("'sin(x)")
        self.assertEqual(s.handle(":value"), "sin(x)")

    def test_nonintegrable_stays_noun(self):
        s = Session()
        s.handle("integrate(exp(exp(x)), x)")
        out = s.handle(":value")
        # M5.2c-iii 嵌套塔解锁后 e^{e^x} 可建塔：积分给出证明性拒答
        # （强于原名词挂起——诚实且信息更多）
        self.assertIn("not elementary", out)

    def test_inert_nested_in_expr(self):
        # 惰性形式嵌在表达式深处也能求值（全式遍历；规范序）
        s = Session()
        s.handle("1 + integrate(x, x)")
        self.assertEqual(s.handle(":value"), "1/2*x^2 + 1")


class TestRefine(unittest.TestCase):
    """Refine 通道：decide 的第二大消费者，只重写账本可判的结构。"""

    def test_sign_driven(self):
        s = Session()
        s.handle(":assume x > 0")
        s.handle("abs(x) + sqrt(x^2) + exp(log(x))")
        self.assertEqual(s.handle(":refine"), "3*x")
        self.assertIn("scheme:refine", [st.rule_id for st in s.log])

    def test_negative_case(self):
        ctx = Context()
        ctx.assume(parse("y < 0"))
        r, changed = refine(parse("abs(y) + sqrt(y^2)"), ctx)
        self.assertTrue(changed)
        self.assertEqual(to_str(r), "-2*y")

    def test_undecidable_untouched(self):
        ctx = Context()
        r, changed = refine(parse("abs(y)"), ctx)
        self.assertFalse(changed)
        self.assertIs(r, parse("abs(y)"))

    def test_log_exp_unconditional(self):
        # N4 迁移：log∘exp 互逆已上收为构造期收缩（contract.py，
        # Log 的 dom 声明即 arg>0 主支语义）——解析即得 y；
        # refine 通道对已收缩输入自然 no-op
        self.assertEqual(to_str(parse("log(exp(y))")), "y")
        ctx = Context()
        r, changed = refine(parse("log(exp(y))"), ctx)
        self.assertFalse(changed)

    def test_piecewise_branch_pick(self):
        ctx = Context()
        ctx.assume(parse("x > 1"))
        r, changed = refine(parse("piecewise(x^2, x > 0, -x, true)"), ctx)
        self.assertTrue(changed)
        self.assertEqual(to_str(r), "x^2")

    def test_piecewise_branch_prune(self):
        ctx = Context()
        ctx.assume(parse("x < 0"))
        r, changed = refine(parse("piecewise(x^2, x > 0, -x, true)"), ctx)
        self.assertTrue(changed)
        # x>0 分支被剪；剩余单 true 分支由 mk 归一塌缩为值本身
        self.assertEqual(to_str(r), "-x")


class TestProtected(unittest.TestCase):
    """Protected：内建头拒绝覆盖（结构头/绑定词头全覆盖）。"""

    def test_heads_rejected(self):
        s = Session()
        for name in ("integrate", "limit", "piecewise", "conjugate"):
            out = s.handle(f"{name}(x) := x")
            self.assertIn("cannot redefine built-in", out, name)
        # sqrt 由 parser 直重写为 Power，形态检查拒定义（同样不可覆盖）
        self.assertIn("error", s.handle("sqrt(x) := x"))

    def test_spec_heads_still_rejected(self):
        s = Session()
        self.assertIn("cannot redefine built-in", s.handle("sin(x) := x"))


class TestLatex(unittest.TestCase):
    """LaTeX 输出（纯展示层）。"""

    def L(self, s):
        return to_latex(parse(s))

    def test_fraction_power(self):
        self.assertEqual(self.L("(x^2 + 1)/(x - 1)"),
                         "\\frac{\\left(x^{2} + 1\\right)}{\\left(x - 1\\right)}")
        self.assertEqual(self.L("1/x^2"), "\\frac{1}{x^{2}}")
        self.assertEqual(self.L("x^(-1)"), "\\frac{1}{x}")

    def test_sqrt(self):
        self.assertEqual(self.L("sqrt(x)"), "\\sqrt{x}")
        self.assertEqual(self.L("x^(1/3)"), "\\sqrt[3]{x}")

    def test_constants_and_trig(self):
        self.assertEqual(self.L("pi + e"), "e + \\pi")   # 规范序
        self.assertEqual(self.L("sin(x)^2"), "\\sin\\left(x\\right)^{2}")

    def test_exp_render_as_e_power(self):
        self.assertEqual(self.L("e^x"), "e^{x}")
        self.assertEqual(self.L("exp(x) * sin(x)"), "e^{x} \\sin\\left(x\\right)")
        self.assertEqual(self.L("e^(x+1)"), "e^{x + 1}")

    def test_annotate_latex_matches_to_latex(self):
        # raw 与 to_latex 逐字节一致；wrapped 的 htmlClass 花括号平衡
        from cas.latex import annotate_latex

        def balanced(s):
            depth = 0
            i = 0
            while i < len(s):
                if s[i] == "\\":
                    i += 2
                    continue
                if s[i] == "{":
                    depth += 1
                elif s[i] == "}":
                    depth -= 1
                    if depth < 0:
                        return False
                i += 1
            return depth == 0

        cases = ["e^x * sin(x)", "(x^2 + 1)/(x - 1)", "sin(x)^2 + cos(x)^2",
                 "x^3 - 2*x + 1", "1/(x+1)", "-(x+1)", "x < 3 && y > 1",
                 "sqrt(x)", "int(x, x)", "x^2/2 + x"]
        for s in cases:
            t = parse(s)
            raw, wrapped = annotate_latex(t)
            self.assertEqual(raw, self.L(s), f"raw mismatch for {s}")
            self.assertTrue(balanced(wrapped), f"unbalanced for {s}")
            self.assertIn("\\htmlClass{tn-0}", wrapped, f"no child class for {s}")

    def test_annotate_latex_paths(self):
        # 每个 tn- 标注的 path 与 server 序列化树一致（深度优先）
        from cas.latex import annotate_latex
        from cas.parser import parse as _parse
        t = _parse("x^2 + y^2")
        _, wrapped = annotate_latex(t)
        for p in ["tn-0-0", "tn-0-1", "tn-1-0", "tn-1-1"]:
            self.assertIn(f"\\htmlClass{{{p}}}", wrapped)

    def test_negative_terms(self):
        self.assertEqual(self.L("x - 1"), "x - 1")
        self.assertEqual(self.L("-x"), "-x")

    def test_comparison_logic(self):
        self.assertEqual(self.L("x >= 0"), "x \\ge 0")
        self.assertEqual(self.L("x != 0"), "x \\ne 0")

    def test_integral_bound(self):
        self.assertEqual(self.L("integrate(sin(x), x)"),
                         "\\int \\sin\\left(x\\right) \\, dx")

    def test_piecewise(self):
        self.assertEqual(self.L("piecewise(x, x >= 0, -x, true)"),
                         "\\begin{cases} x & x \\ge 0 \\\\ -x & \\top \\end{cases}")

    def test_session_command(self):
        s = Session()
        s.handle("(a + b)^2/c")
        self.assertEqual(s.handle(":latex"),
                         "\\frac{\\left(a + b\\right)^{2}}{c}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
