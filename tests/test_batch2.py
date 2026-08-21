"""第二批采购清单验收：解集/O 项/∞ 极限/反常积分/分段积分/策略步树/自动换元。"""

import unittest

from cas import term as T
from cas.integrate import defint
from cas.latex import to_latex
from cas.limits import limit
from cas.parser import parse
from cas.pprint import to_str
from cas.series import series_term
from cas.session import Session
from cas.sets import finite_set, interval, union_of, EMPTY_SET


class _Base(unittest.TestCase):
    def setUp(self):
        from cas.term import S

        self.x = S("x")


class TestSets(_Base):
    def test_heads_and_print(self):
        self.assertEqual(to_str(finite_set(T.N(1), T.N(2))), "{1, 2}")
        self.assertEqual(to_str(interval(T.N(0), T.N(1), lo_open=False, hi_open=True)), "[0, 1)")
        self.assertEqual(to_str(interval(None, T.N(1))), "(-Infinity, 1)")
        u = union_of(interval(None, T.N(-1)), interval(T.N(1), None))
        self.assertEqual(to_str(u), "(-Infinity, -1) U (1, Infinity)")
        self.assertEqual(to_str(EMPTY_SET), "{}")
        self.assertEqual(to_str(union_of(EMPTY_SET, finite_set(T.N(3)))), "{3}")

    def test_latex(self):
        self.assertEqual(to_latex(finite_set(T.N(-2), T.N(2))), "\\left\\{-2, 2\\right\\}")
        self.assertEqual(to_latex(EMPTY_SET), "\\varnothing")

    def test_solveset_command(self):
        s = Session()
        self.assertEqual(s.handle("!solveset x^2 = 1 x"), "x in {-1, 1}")
        self.assertIn("provisos: a != 0", s.handle("!solveset a*x + b = 0 x"))
        self.assertEqual(s.handle("!solveset x^2 - 1 <= 0 x"), "x in [-1, 1]")
        self.assertEqual(s.handle("!solveset x^2 - 2*x + 1 < 0 x"), "x in {}")
        # 无理根端点诚实拒答
        self.assertIn("honest refusal", s.handle("!solveset x^2 - 2 > 0 x"))


class TestSeriesAndO(_Base):
    def test_series_term(self):
        t = series_term(parse("sin(x)"), self.x, T.N(0), 6)
        self.assertIn("O(x^6)", to_str(t))
        self.assertIn("1/120*x^5", to_str(t))

    def test_series_at_point(self):
        t = series_term(parse("x^2"), self.x, T.N(1), 3)
        # (x-1) 形态展开
        self.assertIn("O(", to_str(t))

    def test_series_command_and_refusal(self):
        s = Session()
        self.assertIn("O(x", s.handle("!series exp(x) x 0 4"))
        self.assertIn("honest refusal", s.handle("!series exp(1/x) x 0 4"))

    def test_o_protected(self):
        s = Session()
        self.assertIn("cannot redefine built-in", s.handle("O(x) := x"))


class TestLimitsAtInfinity(_Base):
    def test_rational(self):
        self.assertEqual(to_str(limit(parse("x^2/(x^2+1)"), self.x, T.INFINITY)), "1")
        self.assertIs(limit(parse("1/x"), self.x, T.INFINITY), T.ZERO)

    def test_direction(self):
        self.assertEqual(limit(parse("x"), self.x, T.neg(T.INFINITY)), T.neg(T.INFINITY))
        self.assertEqual(limit(parse("x"), self.x, T.INFINITY), T.INFINITY)

    def test_essential_honest(self):
        # exp(x) -> +∞（exp 支配关系通道）；真正的本性奇点双向不一致才 UNKNOWN
        self.assertIs(limit(parse("exp(x)"), self.x, T.INFINITY), T.INFINITY)
        self.assertIsNone(limit(parse("exp(1/x)"), self.x, T.ZERO))

    def test_atan_inf(self):
        self.assertEqual(to_str(limit(parse("atan(x)"), self.x, T.INFINITY)), "1/2*π")

    def test_log_inf(self):
        self.assertEqual(limit(parse("log(x)"), self.x, T.INFINITY), T.INFINITY)

    def test_limit_command(self):
        s = Session()
        self.assertEqual(s.handle("!limit 1/x x inf"), "0   [PROBABLE, numeric probe]")
        self.assertEqual(s.handle("!limit x x -inf"), "-Infinity")


class TestImproperIntegral(_Base):
    def D(self, expr, lo, hi):
        return defint(parse(expr), self.x, parse(lo) if lo != "inf" and lo != "-inf"
                      else (T.INFINITY if lo == "inf" else T.neg(T.INFINITY)),
                      parse(hi) if hi != "inf" and hi != "-inf"
                      else (T.INFINITY if hi == "inf" else T.neg(T.INFINITY)))

    def test_convergent(self):
        v, st, _n = self.D("1/x^2", "1", "inf")
        self.assertEqual((to_str(v), st), ("1", "VERIFIED"))
        v, st, _n = self.D("exp(-x)", "0", "inf")
        self.assertEqual((to_str(v), st), ("1", "VERIFIED"))

    def test_divergent(self):
        _v, st, _n = self.D("1/x", "1", "inf")
        self.assertEqual(st, "DIVERGES")

    def test_whole_real_line(self):
        v, st, _n = self.D("1/(1+x^2)", "-inf", "inf")
        self.assertEqual((to_str(v), st), ("π", "VERIFIED"))


class TestPiecewiseIntegral(_Base):
    def test_abs_shape(self):
        v, st, note = defint(parse("piecewise(x-1, x >= 1, 1-x, true)"), self.x, T.N(0), T.N(2))
        self.assertEqual((to_str(v), st), ("1", "VERIFIED"))
        self.assertIn("piecewise", note)

    def test_odd_shape(self):
        v, _st, _n = defint(parse("piecewise(x^2, x >= 0, -x^2, true)"), self.x, T.N(-1), T.N(1))
        self.assertIs(v, T.ZERO)


class TestStrategyTree(_Base):
    def trees(self, expr):
        from cas.istrategy import explain

        return explain(parse(expr), self.x)

    def test_kinds(self):
        self.assertEqual(self.trees("sin(x)").kind, "table")
        self.assertEqual(self.trees("sin(2*x)").kind, "linear")
        self.assertEqual(self.trees("2*x*exp(x^2)").kind, "usub")
        self.assertEqual(self.trees("1/(x^2-1)").kind, "rational")
        self.assertEqual(self.trees("1/(1+sin(x))").kind, "tan-half")
        self.assertEqual(self.trees("exp(exp(x))").kind, "failed")

    def test_usub_child(self):
        st = self.trees("2*x*exp(x^2)")
        self.assertEqual(len(st.children), 1)
        self.assertIn("u = x^2", st.note)

    def test_isteps_command(self):
        s = Session()
        out = s.handle(":isteps 2*x*exp(x^2)")
        self.assertIn("[usub]", out)
        self.assertIn("[table]", out)   # 子步递归分类：∫eᶻ 走 spec 表


class TestIndefiniteUSub(_Base):
    def test_cases_verified(self):
        from cas.integrate import integrate

        for expr, frag in (("2*x*exp(x^2)", "u-substitution u=x^2"),
                           ("cos(x)*exp(sin(x))", "u-substitution u=sin(x)"),
                           ("x/(x^2+1)", "u-substitution u=x^2")):   # 候选按大小升序，u=x² 先命中
            _F, ok, method, _prov = integrate(parse(expr), self.x)
            self.assertTrue(ok, expr)
            self.assertEqual(method, frag, expr)

    def test_bad_substitution_never_leaks(self):
        # x^3/(x^2-1)：伪换元候选必须被回验拒绝，回退正确算法；
        # 验证态取 integrate 内层回验（Poly 层等价，比 equivalent 管线更硬）
        from cas.integrate import integrate

        F, ok, _m, _prov = integrate(parse("x^3/(x^2-1)"), self.x)
        self.assertTrue(ok)


if __name__ == "__main__":
    unittest.main(verbosity=2)
