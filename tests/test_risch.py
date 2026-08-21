"""Risch M5.0 测试：微分域塔构建 + 塔上求导。

核心正确性证据 = 差分验证：塔上 derivation（链式法则独立实现）与
cas.diff.d（spec 表驱动微分器）经数值采样交叉核对——两个独立实现
必须一致。塔构建另测归组/拒绝路径/roundtrip。
"""

import unittest
from fractions import Fraction as Fr

from cas.term import S, N
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify
import cas.term as T

x = S("x")

try:
    from cas.evalnum import eval_approx

    HAS_NUM = True
except ImportError:
    HAS_NUM = False


def _build(s):
    from cas.risch import build_extension

    return build_extension(parse(s), x)


class TestTowerBuild(unittest.TestCase):
    def test_exp_single(self):
        de, fa, fd = _build("exp(-x^2)")
        self.assertEqual([v.name for v in de.levels], ["x", "t"])
        self.assertEqual(de.cases, ["base", "exp"])
        wn, wd = de.ws[1]
        self.assertEqual(to_str(wn.to_term()), "-2*x")
        # f = t / 1
        self.assertEqual(to_str(fa.to_term()), "t")
        self.assertTrue(fd.is_const())

    def test_integer_power_grouping(self):
        # e^x + e^(x/2)：归组到基 x/2，f = t^2 + t
        de, fa, fd = _build("exp(x) + exp(x/2)")
        wn, _wd = de.ws[1]
        self.assertEqual(to_str(wn.to_term()), "1/2")
        self.assertEqual(to_str(fa.to_term()), "t + t^2")

    def test_grouping_higher_degree(self):
        # e^(x^2) 与 e^(2*x^2)：deg 2 的 Fr 倍同样归组
        de, fa, fd = _build("exp(x^2) + exp(2*x^2)")
        self.assertEqual(len(de.levels), 2)
        self.assertEqual(to_str(fa.to_term()), "t + t^2")

    def test_log_primitive_layer(self):
        de, fa, fd = _build("log(x^2 + 1)")
        self.assertEqual(de.cases, ["base", "primitive"])
        wn, wd = de.ws[1]
        self.assertEqual(to_str(wn.to_term()), "2*x")
        self.assertEqual(to_str(wd.to_term()), "x^2 + 1")

    def test_mixed_layers_log_first(self):
        # log 先建（primitive 在下），exp 在外（sympy handle_first='log' 同款）
        de, fa, fd = _build("exp(x)*log(x)")
        self.assertEqual(de.cases, ["base", "primitive", "exp"])
        self.assertEqual(to_str(fa.to_term()), "l*t")

    def test_reject_algebraic_dependency(self):
        from cas.risch import RischUnsupported

        with self.assertRaises(RischUnsupported):
            _build("exp(log(x)/2)")

    def test_reject_nested_transcendental_arg(self):
        from cas.risch import RischUnsupported

        with self.assertRaises(RischUnsupported):
            _build("exp(x*exp(x))")

    def test_reject_trig(self):
        from cas.risch import RischUnsupported

        with self.assertRaises(RischUnsupported):
            _build("sin(x)")

    def test_roundtrip(self):
        from cas.risch import tower_to_term_pair

        for s in ("exp(-x^2)", "exp(x) + exp(x/2)", "log(x^2+1)", "exp(x)*log(x)",
                  "x*exp(x)^3 + 1/(exp(x) + 1)"):
            de, fa, fd = _build(s)
            back = simplify(tower_to_term_pair(fa, fd, de))
            # 回写为通分形态（超越式判等只有采样 PROBABLE）——更强自测：
            # 重新建塔，塔上分式必须逐项还原（Q(x,t) 表示唯一）
            de2, fa2, fd2 = _build(to_str(back))
            self.assertEqual((de2.cases, fa2.monos, fd2.monos),
                             (de.cases, fa.monos, fd.monos),
                             f"roundtrip failed: {s}")


@unittest.skipUnless(HAS_NUM, "evalnum unavailable")
class TestDerivationDifferential(unittest.TestCase):
    """差分验证：derivation（塔上链式法则）vs diff.d（spec 表驱动）。

    对 f 的分子/分母分别求导后按商法则合成，backsubst 成 term，
    与 diff.d 直接结果做多点数值采样对比。
    """

    # 正采样点：log 层要求定义域 >0（exp 类无谓，统一取正）
    SAMPLES = [Fr(1, 3), Fr(1, 2), Fr(5, 2), Fr(11, 4), Fr(7)]

    def _check(self, s):
        from cas.risch import build_extension, derivation, tower_to_term_pair
        from cas.diff import d

        f = parse(s)
        de, fa, fd = _build(s)
        an, ad = derivation(fa, de)
        bn, bd = derivation(fd, de)
        # D(a/d) = (D(a)*d - a*D(d)) / d^2，其中 D(a)=(an/ad), D(d)=(bn/bd)
        # 通分：num = an*d*bd - a*bn*ad，den = ad*bd*d^2
        num = an * fd * bd - fa * bn * ad
        den = ad * bd * fd * fd
        got = simplify(tower_to_term_pair(num, den, de))
        want = d(f, x)
        for xv in self.SAMPLES:
            gv = eval_approx(got, {x: xv})
            wv = eval_approx(want, {x: xv})
            # 相对容差：大数值处 float64 绝对误差放大
            self.assertAlmostEqual(gv, wv, delta=max(1e-9, abs(wv) * 1e-9),
                                   msg=f"{s} at x={xv}")

    def test_exp_tower(self):
        self._check("exp(-x^2)")
        self._check("exp(x) + exp(x/2)")
        self._check("x*exp(x)^3")

    def test_log_tower(self):
        self._check("log(x^2 + 1)")
        self._check("x*log(x)")

    def test_mixed_tower(self):
        self._check("exp(x)*log(x)")
        self._check("(exp(x) + 1)/(exp(x) - 1)")


class TestRischExpIntegrate(unittest.TestCase):
    """M5.1a：exp 单项式积分（Hermite 推广 + residue_reduce）。

    正确性证据 = 双通道：(1) 已知闭式逐项比对；(2) D(result) 与
    被积函数数值采样交叉核对（独立微分引擎）。
    """

    SAMPLES = [Fr(1, 3), Fr(1, 2), Fr(5, 2), Fr(11, 4)]

    def _integrate(self, s):
        from cas.risch import integrate_exp_tower

        return integrate_exp_tower(parse(s), x)[0]

    def _dcheck(self, s, result):
        from cas.diff import d

        # 验证关系：D(F) == f（F=结果，f=被积函数）——数值采样交叉核对
        got = d(result, x)
        want = parse(s)
        for xv in self.SAMPLES:
            gv = eval_approx(got, {x: xv})
            wv = eval_approx(want, {x: xv})
            self.assertAlmostEqual(gv, wv, delta=max(1e-9, abs(wv) * 1e-9),
                                   msg=f"D-check {s} at x={xv}")

    def test_log_form(self):
        r = self._integrate("1/(exp(x)+1)")
        self.assertEqual(to_str(simplify(r)), "x - log(exp(x) + 1)")
        self._dcheck("1/(exp(x)+1)", r)

    def test_log_form_scaled(self):
        r = self._integrate("1/(2*exp(x)+3)")
        self.assertEqual(to_str(simplify(r)), "1/3*x - 1/3*log(exp(x) + 3/2)")
        self._dcheck("1/(2*exp(x)+3)", r)

    def test_pure_log(self):
        r = self._integrate("exp(x)/(exp(x)+1)")
        self.assertEqual(to_str(simplify(r)), "log(exp(x) + 1)")
        self._dcheck("exp(x)/(exp(x)+1)", r)

    def test_hermite_double_pole(self):
        # 重因子：Hermite 推广剥出有理部分 + residue 对数部分
        r = self._integrate("1/(exp(x)+1)^2")
        self.assertEqual(to_str(simplify(r)),
                         "x + (exp(x) + 1)^-1 - log(exp(x) + 1)")
        self._dcheck("1/(exp(x)+1)^2", r)

    def test_hermite_rational_part_only(self):
        r = self._integrate("exp(x)/(exp(x)+1)^2")
        self.assertEqual(to_str(simplify(r)), "-1/(exp(x) + 1)")
        self._dcheck("exp(x)/(exp(x)+1)^2", r)

    def test_poly_part_pending(self):
        # e^(-x^2)：多项式部分 t -> M5.1b RDE（届时给不可初等证明）
        from cas.risch import RischUnsupported

        with self.assertRaises(RischUnsupported) as cm:
            self._integrate("exp(-x^2)")
        self.assertIn("M5.1b", str(cm.exception))


if __name__ == "__main__":
    unittest.main()
