"""手动交互扩展命令测试：子项手术（:tree/:set/:rsub）、等式双侧操作、
变形工具箱（:expand/:extract/:separate/:complete_square）、微积分战术
（:usub/:lhop/:parts 明细）。

设计立场对照（docs/manual.md §3.4）：
- :set/:rsub 的 equivalent 三态标注（YES->VERIFIED / PROBABLE / UNKNOWN->UNVERIFIED，
  NO 拒绝——永不静默错）
- 等式命令的域闸门（div_both 的 t!=0 proviso；apply_both 的域 proviso + 单射性 note）
- :usub 两级策略（精确微分分解优先，主支逆退化）
"""
import unittest

from cas import term as T
from cas.session import Session


class TestTree(unittest.TestCase):
    def test_tree_shows_paths(self):
        s = Session()
        s.handle("x + ln(e^x) = e^x")
        out = s.handle(":tree")
        self.assertIn("()", out)
        self.assertIn("0.1", out)          # lhs 的第二个加项 log(exp(x))
        self.assertIn("log(exp(x))", out)

    def test_tree_readonly_not_recorded(self):
        s = Session()
        s.handle("x + y")
        n0 = len(s.transcript)
        s.handle(":tree")
        self.assertEqual(len(s.transcript), n0)


class TestSetRsub(unittest.TestCase):
    def test_set_probable_tag(self):
        # ln(e^x) -> x：采样支持（PROBABLE），mk 归并 x+x -> 2*x
        s = Session()
        s.handle("x + ln(e^x) = e^x")
        out = s.handle(":set 0.1 x")
        self.assertIn("2*x == exp(x)", out)
        self.assertIn("[PROBABLE]", out)

    def test_set_verified_tag(self):
        # (x-1)*(x+1) -> x^2-1：多项式恒等片段判 YES；(x^2-1)+7 = x^2+6
        s = Session()
        s.handle("(x - 1)*(x + 1) + 7")
        out = s.handle(":set 0 x^2 - 1")
        self.assertIn("x^2 + 6", out)
        self.assertNotIn("UNVERIFIED", out)
        self.assertNotIn("PROBABLE", out)

    def test_set_refused_unverifiable(self):
        # x -> 5：不可验证（采样不产否证，UNKNOWN）-> 拒绝，当前式不动
        s = Session()
        s.handle("x^2")
        out = s.handle(":set 0 5")
        self.assertIn("refused", out)
        self.assertIn("UNKNOWN", out)
        self.assertEqual(s.current, T.pw(T.S("x"), T.N(2)))

    def test_set_bad_path(self):
        s = Session()
        s.handle("x + y")
        out = s.handle(":set 9 z")
        self.assertIn("no subterm", out)

    def test_rsub_replaces_all(self):
        s = Session()
        s.handle("ln(e^x) + ln(e^x)")
        out = s.handle(":rsub ln(e^x)=x")
        self.assertIn("2*x", out)

    def test_rsub_not_found(self):
        s = Session()
        s.handle("x + y")
        out = s.handle(":rsub z^2=w")
        self.assertIn("not found", out)


class TestEquationOps(unittest.TestCase):
    def test_sub_both_moves_term(self):
        s = Session()
        s.handle("x + a = b")
        out = s.handle(":sub_both a")
        self.assertIn("x == b - a", out)

    def test_add_mul_neg_swap(self):
        s = Session()
        s.handle("x = 3")
        s.handle(":add_both 2")
        self.assertIn("== 5", to_cur(s))
        s.handle(":mul_both 2")
        self.assertIn("2*(x + 2) == 10", to_cur(s))
        s.handle(":neg_both")
        self.assertIn("-2*(x + 2) == -10", to_cur(s))
        s.handle(":swap")
        self.assertIn("-10 == -2*(x + 2)", to_cur(s))

    def test_div_both_proviso(self):
        s = Session()
        s.handle("x*t = y")
        out = s.handle(":div_both t")
        self.assertIn("x == y/t", out)
        self.assertIn("proviso: t != 0", out)

    def test_zero_form(self):
        s = Session()
        s.handle("x^2 = 4")
        out = s.handle(":zero_form")
        self.assertIn("x^2 - 4 == 0", out)

    def test_apply_both_log_proviso(self):
        s = Session()
        s.handle("e^x = 5")
        out = s.handle(":apply_both log")
        self.assertIn("log(exp(x)) == log(5)", out)
        self.assertIn("proviso", out)

    def test_apply_both_sin_non_injective_note(self):
        s = Session()
        s.handle("2*x = 1")
        out = s.handle(":apply_both sin")
        self.assertIn("sin(2*x) == sin(1)", out)
        self.assertIn("not injective", out)

    def test_apply_both_sqrt(self):
        # sqrt 无 spec 声明 -> 诚实提示未声明单射性
        s = Session()
        s.handle("x^2 = 2")
        out = s.handle(":apply_both sqrt")
        self.assertIn("x^2^(1/2) == 2^(1/2)", out)
        self.assertIn("undeclared", out)

    def test_requires_equation(self):
        s = Session()
        s.handle("x + 1")
        out = s.handle(":swap")
        self.assertIn("must be an equation", out)


class TestEquationDomainGates(unittest.TestCase):
    """等式双侧操作的域诚实：引入的项必须在解点有定义，否则解集被静默收窄。"""

    def test_add_both_domain_proviso(self):
        s = Session()
        s.handle("x + y = 5")
        out = s.handle(":add_both ln(x-k)")
        self.assertIn("proviso: x - k > 0", out)

    def test_sub_both_domain_proviso(self):
        # 加后减：形式复原但中间步确实收窄过 -> proviso 保守保留
        s = Session()
        s.handle("x + y = 5")
        s.handle(":add_both ln(x-k)")
        out = s.handle(":sub_both ln(x-k)")
        self.assertIn("x + y == 5", out)
        self.assertIn("proviso: x - k > 0", out)

    def test_mul_both_domain_proviso(self):
        s = Session()
        s.handle("x = 3")
        out = s.handle(":mul_both ln(x-k)")
        self.assertIn("proviso: x - k > 0", out)

    def test_add_both_quoted_borrow_form(self):
        # 借用形 'ln(x-k)-ln(x-k)：quote 保结构不被 mk 消掉，域约束随行记账
        s = Session()
        s.handle("x*y = 2")
        out = s.handle(":add_both " + chr(39) + "ln(x-k) - ln(x-k)")
        self.assertIn("proviso: x - k > 0", out)

    def test_add_both_refused_contradictory_domain(self):
        # 与账本矛盾（x<1 vs ln(x-1) 需 x>1）-> 拒绝（ex falso 纪律）
        s = Session()
        s.handle("x + y = 5")
        s.handle(":assume x < 1")
        out = s.handle(":add_both ln(x-1)")
        self.assertIn("domain empty", out)
        self.assertIn("contradicted", out)

    def test_div_both_proviso_unchanged(self):
        s = Session()
        s.handle("x*t = y")
        out = s.handle(":div_both t")
        self.assertIn("proviso: t != 0", out)


class TestDomainAudit(unittest.TestCase):
    """域问题全面排查的回归：set/rsub 换入项域收窄记账 + extract 超越因子。"""

    def test_extract_transcendental_factor(self):
        # 因子为超越项：构造 = 分配律逆（结构可靠），验证接受 PROBABLE
        s = Session()
        s.handle("x*ln(x-k) + y*ln(x-k)")
        out = s.handle(":extract ln(x-k)")
        self.assertIn("log(x - k)*(x + y)", out)

    def test_new_domain_conditions_detects_narrowing(self):
        from cas.parser import parse

        s = Session()
        cons = s._new_domain_conditions(parse("f(x)"), parse("sqrt(x)"))
        self.assertTrue(any("x >= 0" in str(c) for c in cons))

    def test_set_no_spurious_proviso_when_removing_constraint(self):
        # ln(e^x) -> x：约束被移除而非引入 -> 不应有 proviso
        s = Session()
        s.handle("y + ln(e^x)")
        out = s.handle(":set 1 x")
        self.assertIn("[PROBABLE]", out)
        self.assertNotIn("proviso", out)

    def test_separate_preserves_denominator_domain(self):
        s = Session()
        s.handle("(x^2 - 1)/(x - 1)")
        out = s.handle(":separate")
        self.assertIn("(x - 1)", out)   # 分母保留，x != 1 的域不扩大


class TestLoopExtraction(unittest.TestCase):
    """等式链提取：循环分部的方程由机器写（:intro_eq），人不再手抄 RHS。"""

    def test_parts_sign_pullout_and_loop_hint(self):
        # 符号拉出绑定体 -> 循环名词指针收敛 -> [loop] 提示
        s = Session()
        s.handle("I := integrate(exp(x)*sin(x), x)")
        s.handle("I")
        orig = s.current
        s.handle(":parts sin(x)")
        out = s.handle(":parts cos(x)")
        self.assertIn("[loop] I recurs", out)
        self.assertIn("∫[exp(x)*sin(x)]", out)     # 符号已拉出（非 ∫[-...]）
        self.assertIsNotNone(s._named_loop(s.current))
        self.assertIs(orig, s.defs["I"][1])         # 链首名词稳定

    def test_intro_eq_closes_loop(self):
        s = Session()
        for c in ["I := integrate(exp(x)*sin(x), x)", "I",
                  ":parts sin(x)", ":parts cos(x)"]:
            s.handle(c)
        out = s.handle(":intro_eq I")
        self.assertIn("==", out)
        self.assertEqual(s.current.head.name, "Eq")
        kinds = [st.rule_id for st in s.log]
        self.assertIn("scheme:intro_eq", kinds)
        out = s.handle(":solveq I")                 # 按定义名解循环方程
        self.assertIn("1/2*", out)

    def test_loop_flow_verified(self):
        s = Session()
        for c in ["I := integrate(exp(x)*sin(x), x)", "I",
                  ":parts sin(x)", ":parts cos(x)",
                  ":intro_eq I", ":solveq I"]:
            s.handle(c)
        self.assertEqual(s.handle("!verify % x exp(x)*sin(x)"), "VERIFIED")

    def test_solveq_by_def_name(self):
        # :solveq 裸符号名字解析为宏体（变量定义；复合项如 log(x) 不被扁平化吞掉）
        s = Session()
        s.handle("K := log(x)")
        s.handle("2*K + 3 = 7")
        out = s.handle(":solveq K")
        self.assertIn("2", out)

    def test_no_false_loop_hint(self):
        # 无命名积分再现时不提示
        s = Session()
        s.handle("integrate(exp(x), x)")
        out = s.handle(":parts exp(x)")
        self.assertIsInstance(out, str)
        self.assertNotIn("[loop]", out)

    def test_negative_start_loop_with_fold(self):
        # 负号起点：循环再现的是 -I（指针不同）-> :fold 线性折叠归一
        s = Session()
        for c in ["I := integrate(-exp(x)*sin(x), x)", "I",
                  ":parts sin(x)", ":parts cos(x)"]:
            s.handle(c)
        self.assertIsNone(s._named_loop(s.current))     # 折叠前指针不收敛
        out = s.handle(":fold")
        self.assertIn("[loop] I recurs", out)           # 折叠后收敛
        s.handle(":intro_eq I")
        out = s.handle(":solveq I")
        self.assertIn("1/2*", out)
        self.assertEqual(s.handle("!verify % x -exp(x)*sin(x)"), "VERIFIED")

    def test_intro_eq_from_history_node(self):
        # 等式链任意节点：%N 历史引用与当前式连等式
        s = Session()
        s.handle("x + y")
        s.handle("(x + y)^2")
        s.handle(":expand")
        out = s.handle(":intro_eq %1")
        self.assertIn("x + y ==", out)


class TestGuardObligations(unittest.TestCase):
    """守卫条件显式在案：域闸门 UNKNOWN 接义务队列，可作答回滚。"""

    def test_domain_gate_creates_obligation(self):
        s = Session()
        s.handle("x + y = 5")
        s.handle(":add_both ln(x-k)")
        obls = s.handle(":obls")
        self.assertIn("x - k > 0", obls)
        self.assertIn("affects steps [1]", obls)
        self.assertIn("answered", s.handle(":ans 1 x - k > 0"))
        self.assertIn("(none)", s.handle(":obls"))

    def test_apply_both_creates_obligation(self):
        s = Session()
        s.handle("e^x = 5")
        s.handle(":apply_both log")
        self.assertIn("exp(x) > 0", s.handle(":obls"))


class TestReshaping(unittest.TestCase):
    def test_expand(self):
        s = Session()
        s.handle("(x + 1)^2")
        out = s.handle(":expand")
        self.assertIn("x^2 + 2*x + 1", out)

    def test_extract_common_factor(self):
        s = Session()
        s.handle("x^2 + 2*x")
        out = s.handle(":extract x")
        self.assertIn("x*(x + 2)", out)

    def test_extract_refused_non_factor(self):
        s = Session()
        s.handle("x^2 + 2*x + 1")
        out = s.handle(":extract x")
        self.assertIn("refused", out)

    def test_separate(self):
        s = Session()
        s.handle("(a + b)/c")
        out = s.handle(":separate")
        self.assertIn("a/c + b/c", out)

    def test_separate_no_change(self):
        s = Session()
        s.handle("x + 1")
        out = s.handle(":separate")
        self.assertIn("no change", out)

    def test_complete_square(self):
        s = Session()
        s.handle("x^2 + 4*x + 7")
        out = s.handle(":complete_square x")
        self.assertIn("(x + 2)^2 + 3", out)

    def test_complete_square_non_poly_refused(self):
        s = Session()
        s.handle("sin(x)^2 + 2*sin(x)")
        out = s.handle(":complete_square x")
        self.assertIn("not polynomial", out)


class TestUsub(unittest.TestCase):
    def test_exact_differential_route(self):
        # tan 型：body/g' 代入后无 x -> 干净换元
        s = Session()
        s.handle("integrate(sin(x)/cos(x), x)")
        out = s.handle(":usub t=cos(x)")
        self.assertIn("-1/t", out)
        # 换元后可实算：∫-1/t dt = -log(t)
        out = s.handle(":value")
        self.assertIn("-log(t)", out)

    def test_exact_route_exp_x2(self):
        s = Session()
        s.handle("integrate(exp(x^2)*x, x)")
        out = s.handle(":usub t=x^2")
        self.assertIn("exp(t)", out)
        self.assertIn("1/2", out)

    def test_inverse_fallback_route(self):
        # g' 不出现在被积式 -> 主支逆路线（solve 主支解含根式形态）
        s = Session()
        s.handle("integrate(sin(x), x)")
        out = s.handle(":usub t=x^2")
        self.assertIn("dt", out)
        self.assertIn("inverse route", s.log[-1].note)

    def test_requires_inert_integral(self):
        s = Session()
        s.handle("x + 1")
        out = s.handle(":usub t=x^2")
        self.assertIn("inert integral", out)


class TestLhop(unittest.TestCase):
    def test_zero_over_zero(self):
        s = Session()
        s.handle("sin(x)/x")
        out = s.handle(":lhop x 0")
        self.assertIn("cos(x)", out)

    def test_refused_non_indeterminate(self):
        s = Session()
        s.handle("(x + 1)/x")
        out = s.handle(":lhop x 0")
        self.assertIn("not an indeterminate form", out)
        self.assertIn("numerator -> 1", out)


class TestPartsDetail(unittest.TestCase):
    def test_detail_output(self):
        s = Session()
        s.handle("I := integrate(exp(x)*sin(x), x)")
        s.handle("I")
        out = s.handle(":parts sin(x)")
        self.assertIn("u  = sin(x)", out)
        self.assertIn("dv = exp(x) dx", out)
        self.assertIn("du = cos(x) dx", out)
        self.assertIn("v  = exp(x)", out)
        self.assertIn("=>", out)


class TestStepLogIntegration(unittest.TestCase):
    """新命令全部入账可撤销（手动通道纪律）。"""

    def test_undo_after_eq_op(self):
        s = Session()
        s.handle("x + a = b")
        s.handle(":sub_both a")
        self.assertIn("x == b - a", to_cur(s))
        s.handle(":u")
        self.assertIn("a + x == b", to_cur(s))

    def test_steps_record_scheme(self):
        s = Session()
        s.handle("x + a = b")
        s.handle(":sub_both a")
        steps = "\n".join(s.steps())
        self.assertIn("scheme:eq", steps)
        self.assertIn("subtracted a", steps)

    def test_mutating_commands_recorded_in_transcript(self):
        s = Session()
        s.handle("x + a = b")
        s.handle(":sub_both a")
        s.handle(":swap")
        self.assertTrue(any(c.startswith(":sub_both") for c in s.transcript))
        self.assertTrue(any(c.startswith(":swap") for c in s.transcript))


def to_cur(s):
    return s.show()


if __name__ == "__main__":
    unittest.main()
