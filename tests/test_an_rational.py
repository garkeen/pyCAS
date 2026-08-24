import unittest

from cas.parser import parse
from cas.pprint import to_str


def _num_check(F, f, x, points=(0.31, 0.73, 1.17, 2.5), tol=1e-9):
    """d(F) 与 f 在采样点数值一致（答案正确性的独立旁证，不替代证书）。"""
    from cas.diff import d
    from cas.evalnum import eval_approx

    dF = d(F, x)
    for pt in points:
        lhs = eval_approx(dF, {x: pt})
        rhs = eval_approx(f, {x: pt})
        self_tol = tol * max(1.0, abs(rhs))
        if abs(lhs - rhs) > self_tol:
            return False
    return True


class TestAlgebraicRational(unittest.TestCase):
    """M5.4-c：有理积分通道的根式代数常数支持。

    架构裁定：投影期局部参数化（_rcN 不透明符号），通道内按互相
    超越独立参数判定（形式恒等 ⇒ 特化保真），出口回代还原根式。
    全程零全局注册表副作用（ALG_MODULI/ALG_RELATIONS 不动）。
    """

    def setUp(self):
        self.x = parse("x")

    def integ(self, s):
        from cas.integrate import integrate

        return integrate(parse(s), parse("x"))

    def test_textbook_log_form(self):
        # ∫dx/((x-√2)(x+√2)) = [ln(x-√2)-ln(x+√2)]/(2√2)
        F, ok, method, provisos = self.integ("1/((x-2^(1/2))*(x+2^(1/2)))")
        self.assertTrue(ok)
        s = to_str(F)
        self.assertIn("log(x - 2^(1/2))", s)
        self.assertIn("log(x + 2^(1/2))", s)
        f = parse("1/((x-2^(1/2))*(x+2^(1/2)))")
        self.assertTrue(_num_check(F, f, self.x))

    def test_atan_generic_form(self):
        # ∫dx/(x^2+√2)：判别式 4√2 经 A2 区间隔离精确判定 >0
        # → atan 实形式、零 proviso（升级前为 unknown + [D≠0]）
        F, ok, method, provisos = self.integ("1/(x^2+2^(1/2))")
        self.assertTrue(ok)
        self.assertIn("atan", to_str(F))
        self.assertEqual(provisos, [])
        f = parse("1/(x^2+2^(1/2))")
        self.assertTrue(_num_check(F, f, self.x))

    def test_neg_discriminant_real_log_form(self):
        # ∫dx/(x^2-√2)：A2 判别式 -4√2 <0 → 实 ln 差形态（升级前为
        # 复 atan 通形 + proviso，且 evalnum 因负底分数幂无法数值探测）
        F, ok, _m, provisos = self.integ("1/(x^2-2^(1/2))")
        self.assertTrue(ok)
        s = to_str(F)
        self.assertNotIn("atan", s)
        self.assertEqual(provisos, [])
        f = parse("1/(x^2-2^(1/2))")
        self.assertTrue(_num_check(F, f, self.x))

    def test_an_interval_sign_unit(self):
        from cas.integrate import _an_interval_sign, _radical_bracket
        from cas.algfield import (AlgField, register_alg_field,
                                  unregister_alg_fields)
        from cas.poly import SymRat, Poly
        from cas.term import S as _S
        from fractions import Fraction as Fr

        lo, hi = _radical_bracket(Fr(2), 1, 2)      # √2
        self.assertLess(lo * lo, Fr(2))
        self.assertGreater(hi * hi, Fr(2))
        sym = _S("_rc_probe")
        fld = AlgField([Fr(-2), Fr(0), Fr(1)], Fr(1), zero_c=Fr(0),
                       bracket=(lo, hi))
        register_alg_field(sym, fld)
        try:
            # -4α < 0
            D = SymRat(Poly((sym,), {(0,): Fr(-4), (1,): Fr(1)}),
                       Poly.one((sym,)))
            self.assertEqual(_an_interval_sign(D), "neg")
            # 4α > 0
            D2 = SymRat(Poly((sym,), {(0,): Fr(4), (1,): Fr(1)}),
                        Poly.one((sym,)))
            self.assertEqual(_an_interval_sign(D2), "pos")
            # 自由参数不在表内 -> None（回退 decide 路径）
            free = _S("a_free")
            D3 = SymRat(Poly((free,), {(1,): Fr(1)}), Poly.one((free,)))
            self.assertIsNone(_an_interval_sign(D3))
        finally:
            unregister_alg_fields([sym])

    def test_mixed_linear_factor(self):
        # ∫(√2·x+1)/(x²-√2·x)：根 ∈ {0, √2}，判别式 2 为域内平方
        F, ok, _m, _pv = self.integ("(2^(1/2)*x+1)/(x^2-2^(1/2)*x)")
        self.assertTrue(ok)
        s = to_str(F)
        self.assertIn("log(x)", s)
        self.assertIn("2^(1/2)", s)
        f = parse("(2^(1/2)*x+1)/(x^2-2^(1/2)*x)")
        self.assertTrue(_num_check(F, f, self.x,
                                   points=(0.5, 1.9, 3.7)))

    def test_usub_regression(self):
        # 回归：u 换元通道不受影响（√2 保持符号形态）
        res, ok = self.integ("x/(x^2-2^(1/2))")[:2]
        self.assertTrue(ok)
        self.assertEqual(to_str(res), "1/2*log(x^2 - 2^(1/2))")

    def test_no_global_registry_pollution(self):
        # 诚实性核心：投影不登记全局关系表（上次事故教训——全局
        # 注册表泄漏曾致假 VERIFIED）。M7.0-b 后统一登记处 =
        # cas.algfield.ALG_FIELDS，有理通道同样零副作用。
        from cas.algfield import ALG_FIELDS

        before = dict(ALG_FIELDS)
        self.integ("1/((x-2^(1/2))*(x+2^(1/2)))")
        self.assertEqual(ALG_FIELDS, before)

    def test_collect_rad_params_shapes(self):
        from cas.integrate import _collect_rad_params

        m1 = _collect_rad_params(parse("1/(x^2-2^(1/2))"))
        self.assertEqual(len(m1), 1)
        m2 = _collect_rad_params(
            parse("2^(1/2)*x + 3^(1/3) + 2^(1/2)/x"))
        # 同形共享、异形独立：√2 一符，∛3 一符
        self.assertEqual(len(m2), 2)
        m3 = _collect_rad_params(parse("1/(x^2-1)"))
        self.assertEqual(m3, {})
        # 负底不收（分支切割安全）：(-1)^(1/2) 已是保留名 i 域语义
        m4 = _collect_rad_params(parse("x^(1/2)+x"))
        self.assertEqual(m4, {})

    def test_honest_refusal_preserved(self):
        # 超出切片：代数核（变量底根式）仍诚实拒答，不静默降级
        with self.assertRaises(Exception):
            self.integ("1/sqrt(x^2+1)")

    def test_trager_cubic_factorization(self):
        # A3：∫dx/(x³-3x-√2)：x³-3x-√2 = (x+√2)(x²-√2x-1)——
        # 三次参数域因子经 Trager 范数分解提取；atan 实形式由
        # A2 符号通道解锁（判别式 α²+4=6>0）
        F, ok, _m, provisos = self.integ("1/(x^3-3*x-2^(1/2))")
        self.assertTrue(ok)
        s = to_str(F)
        self.assertIn("log(x + 2^(1/2))", s)
        self.assertIn("log(x^2 - x*2^(1/2) - 1)", s)
        f = parse("1/(x^3-3*x-2^(1/2))")
        self.assertTrue(_num_check(F, f, self.x,
                                   points=(0.41, 0.97, 1.83)))

    def test_an_mixed_linear_quadratic(self):
        # 混合线性×二次：部分分式全链（无 Trager 需要，回归守护）
        F, ok, _m, _pv = self.integ("1/((x-2^(1/2))*(x^2+1))")
        self.assertTrue(ok)
        s = to_str(F)
        self.assertIn("log(x - 2^(1/2))", s)
        self.assertIn("atan", s)
        f = parse("1/((x-2^(1/2))*(x^2+1))")
        self.assertTrue(_num_check(F, f, self.x,
                                   points=(0.5, 1.9, 3.7)))

    def test_alg_modulus_reduction_exact(self):
        # M5.4a 休眠 bug 回归：极小多项式必须是符号上的单变量 Poly，
        # α·α 必须模约简为 2（坏键 Poly 曾致 α≡2 静默错域）
        import cas.term as T
        from fractions import Fraction as Fr
        from cas.poly import Poly
        from cas.algfield import ALG_FIELDS, unregister_alg_fields
        from cas.risch import _collect_radical
        from cas.term import S as _S, N as _N

        sq2 = T.pw(_N(2), _N(Fr(1, 2)))
        subs = {}
        _collect_radical(sq2, subs)
        sym = subs[sq2]
        try:
            mp = ALG_FIELDS[sym].minpoly_poly(sym)
            self.assertEqual(mp.vars, (sym,))
            pa = Poly((sym,), {(1,): Fr(1)})
            prod = pa * pa
            self.assertTrue(prod.is_const())
            self.assertEqual(prod.const_val(), 2)
        finally:
            unregister_alg_fields([sym])


class TestTowerANAudit(unittest.TestCase):
    """P1 审计：塔 RDE × ℚ(α) 全分支回归。

    战果：_integrate_in_K 过时守卫拆除（参数/AN 基域有理积分解锁）、
    残数根表示三级回退（Fr/Ga/SymRat）、RatFunc 标量乘泛化。"""

    def setUp(self):
        self.x = parse("x")

    def integ(self, s):
        from cas.integrate import integrate

        return integrate(parse(s), parse("x"))

    def test_base_field_param_rational_unlocked(self):
        # 过时守卫拆除：基域有理积分接受 SymRat 系数
        from cas.diff import d
        from cas.evalnum import eval_approx

        for s in ["sqrt(2)*log(x)", "a*log(x)", "log(x)/a",
                  "(sqrt(2)*x+1)*log(x)"]:
            F, ok, _m, _pv = self.integ(s)
            self.assertTrue(ok, s)
            dF = d(F, self.x)
            env = {parse("a"): 1.7}
            good = all(abs(eval_approx(dF, {self.x: p, **env}) -
                           eval_approx(parse(s), {self.x: p, **env})) < 1e-8
                       for p in (0.51, 1.33))
            self.assertTrue(good, s)

    def test_residue_roots_symrat(self):
        # 残数根 ±(param/radical)：RT 提取不再误判不可积
        from cas.diff import d
        from cas.evalnum import eval_approx

        for s in ["1/(exp(x)+a)", "a/(exp(x)-b)",
                  "sqrt(2)/(exp(x)+1)", "exp(2*x)/(exp(x)+sqrt(2))"]:
            F, ok, _m, _pv = self.integ(s)
            self.assertTrue(ok, s)
            dF = d(F, self.x)
            env = {parse("a"): 1.7, parse("b"): 2.3}
            good = all(abs(eval_approx(dF, {self.x: p, **env}) -
                           eval_approx(parse(s), {self.x: p, **env})) < 1e-8
                       for p in (0.37, 0.79))
            self.assertTrue(good, s)

    def test_proved_refusals_preserved(self):
        # 误证不可积防线：这些案例的 proved 拒答经手算确认正确
        import contextlib

        for s in ["exp(exp(x))",
                  "exp(sqrt(2)*x)/(x^2+1)",
                  "1/(x*log(x-sqrt(2)))"]:
            with contextlib.suppress(Exception):
                continue_marker = None
            raised = False
            try:
                self.integ(s)
            except Exception:
                raised = True
            self.assertTrue(raised, f"{s} 应 proved 拒答")

    def test_nested_radical_coefficients(self):
        # P3 兜底收集：嵌套代数常数作系数（不透明参数，无关系语义）
        from cas.diff import d
        from cas.evalnum import eval_approx

        for s in ["1/(x^2-(1+sqrt(2)))",
                  "1/((x-sqrt(1+sqrt(2)))*(x+sqrt(2)))"]:
            F, ok, _m, _pv = self.integ(s)
            self.assertTrue(ok, s)
            dF = d(F, self.x)
            good = all(abs(eval_approx(dF, {self.x: p}) -
                           eval_approx(parse(s), {self.x: p})) < 1e-9
                       for p in (0.43, 0.91, 1.71))
            self.assertTrue(good, s)

    def test_solveineq_structured_refusal(self):
        # P4：AN 系数不等式给结构化拒答（曾炸裸 non-integer power）
        from cas.session import Session

        s_ = Session()
        out = s_.handle("!solveineq x^2-sqrt(2)>0 x")
        self.assertIn("error", out)
        self.assertIn("coefficient domain", out)


class TestSpecialFunctionOutput(unittest.TestCase):
    """M5.5：Risch proved 拒答后的特殊函数出口层。

    结构化候选族（Ei 线性族/li/Ci/erf）+ diff.verify 背书——
    导数塌缩回初等域后精确判等，未验证候选绝不出门。"""

    def setUp(self):
        self.x = parse("x")

    def integ(self, s):
        from cas.integrate import integrate

        return integrate(parse(s), parse("x"))

    def test_ei_linear_family(self):
        cases = [
            ("exp(x)/x", "Ei"),
            ("exp(x)/(x-1)", "Ei"),
            ("exp(2*x)/(x-1)", "Ei"),
            ("exp(3*x+1)/(2*x)", "Ei"),
        ]
        for s, fn in cases:
            F, ok, method, _pv = self.integ(s)
            self.assertTrue(ok, s)
            self.assertIn(fn, to_str(F), s)
            self.assertIn("special function", method, s)

    def test_li_ci_erf(self):
        F, ok, _m, _pv = self.integ("1/log(x)")
        self.assertTrue(ok)
        self.assertIn("li", to_str(F))
        F, ok, _m, _pv = self.integ("cos(x)/x")
        self.assertTrue(ok)
        self.assertIn("Ci", to_str(F))
        # exp(-x^2)：erf 形态；sqrt(pi) 经命名常数幂参数化让验证链
        # 精确归零（塔零判定），非采样级
        F, ok, _m, _pv = self.integ("exp(-x^2)")
        self.assertTrue(ok)
        self.assertIn("erf", to_str(F))

    def test_symbolic_power_rule(self):
        # M5.6：x^a generic 形态 + [a+1!=0] proviso；
        # principal 承诺开启时符号指数合并升级 VERIFIED。
        # (cx)^a / (3x+1)^a：指数整数移位拆分 + 符号幂原子化 +
        # together 系数折叠三件套解锁（曾误判为 PROBABLE 边界）
        from cas.structure import set_principal_branch

        set_principal_branch(True)
        try:
            cases = ["x^a", "x^(a+1)", "(2*x)^a", "(3*x+1)^a",
                     "x^(-a)", "(c*x)^a"]
            for s in cases:
                F, ok, _m, pv = self.integ(s)
                self.assertTrue(ok, s)
                for p in pv:
                    self.assertIn("!=", to_str(p), s)
        finally:
            set_principal_branch(False)

    def test_const_term_coefficients(self):
        # M5.6#1：非有理常数项作系数（有理通道作用域参数化）
        import math
        from cas.evalnum import eval_approx
        from cas.diff import d

        cases = ["pi*x", "pi/(x^2+1)", "sin(1)*x", "e^2/(x^2+1)",
                 "log(3)/(x-1)", "atan(1/2)/(x^2+1)"]
        for s in cases:
            F, ok, _m, _pv = self.integ(s)
            self.assertTrue(ok, s)
            dF = d(F, self.x)
            good = all(abs(eval_approx(dF, {self.x: p}) -
                           eval_approx(parse(s), {self.x: p})) < 1e-9
                       for p in (0.41, 0.93, 1.77))
            self.assertTrue(good, s)


if __name__ == "__main__":
    unittest.main()
