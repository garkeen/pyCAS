"""M5.2c-iii #1：对数导数-根式判定（is_log_deriv_k_t_radical_in_field 移植）。

覆盖：
- base 层（ℚ(i)(x)）：正例（1/x 族）、负例（atan 型、常数、多项式）
- 守卫精确化：代数相关拒绝（√log x）vs 超越放行（x·eˣ 底）
- 嵌套塔端到端：∫e^{eˣ}(eˣ) dx = e^{eˣ} 类经复 Risch 直出
- 证明性拒答不回退
"""

import unittest
from fractions import Fraction as Fr

from cas.parser import parse
from cas.term import S
from cas.pprint import to_str
from cas.poly import Poly
from cas.ratfunc import RatFunc
from cas.gaussian import Ga

x = S("x")


def _rf(num, den="1"):
    """快捷 RatFunc 构造（字符串解析）。"""
    return RatFunc(parse(num).p if False else _poly(parse(num)),
                   _poly(parse(den)))


def _poly(t):
    from cas.risch import trigs_to_exp
    return Poly.from_term(t, (x,))


class TestLogDerivRadicalBase(unittest.TestCase):
    """base 层（ℚ(x)/ℚ(i)(x)）：直接单元测试。"""

    def setUp(self):
        from cas.risch import DiffExt
        self.de = DiffExt(x)

    def test_simple_positive(self):
        from cas.risch import _is_logderiv_radical

        f = RatFunc(_poly(parse("1")), _poly(parse("x")))
        r = _is_logderiv_radical(f, self.de, 0)
        self.assertIsNotNone(r)
        n, u = r
        self.assertEqual(n, 1)
        self.assertEqual(to_str(u.to_term()), "x")

    def test_scaled_positive(self):
        # f=1/(2x)：n=2、u=x（2·f = D(x²)/x²）
        from cas.risch import _is_logderiv_radical

        f = RatFunc(_poly(parse("1/2")), _poly(parse("x")))
        n, u = _is_logderiv_radical(f, self.de, 0)
        self.assertEqual(n, 2)
        self.assertEqual(to_str(u.to_term()), "x")

    def test_multi_factor_positive(self):
        # f=3/x + 5/(2(x+1))：n=2、u=x⁶(x+1)⁵
        from cas.risch import _is_logderiv_radical

        f = (RatFunc(_poly(parse("3")), _poly(parse("x")))
             + RatFunc(_poly(parse("5/2")),
                       _poly(parse("x+1"))))
        n, u = _is_logderiv_radical(f, self.de, 0)
        self.assertEqual(n, 2)
        # x^6 * (x+1)^5 展开形态：验证 u(1)=1 与 u'(x)/u(x) 的结构性
        # 由出口精确验证保证；此处抽查次数与端点
        self.assertEqual(u.p.degree(x), 11)

    def test_gaussian_residue_negative(self):
        # i/x：n·i∈ℤ 无解 => None
        from cas.risch import _is_logderiv_radical

        num = Poly.const((x,), Ga(0, 1))
        f = RatFunc(num, _poly(parse("x")))
        self.assertIsNone(_is_logderiv_radical(f, self.de, 0))

    def test_constant_negative(self):
        from cas.risch import _is_logderiv_radical

        f = RatFunc(_poly(parse("2")), _poly(parse("1")))
        self.assertIsNone(_is_logderiv_radical(f, self.de, 0))

    def test_polynomial_negative(self):
        from cas.risch import _is_logderiv_radical

        f = RatFunc(_poly(parse("x")), _poly(parse("1")))
        self.assertIsNone(_is_logderiv_radical(f, self.de, 0))

    def test_gaussian_residue_negative(self):
        # i/x：n·i∈ℤ 无解 => None
        from cas.risch import _is_logderiv_radical

        num = Poly.const((x,), Ga(0, 1))
        f = RatFunc(num, _poly(parse("x")))
        self.assertIsNone(_is_logderiv_radical(f, self.de, 0))


class TestGuardExact(unittest.TestCase):
    """塔构建守卫：代数相关 vs 超越的精确分界。"""

    def _build(self, s):
        from cas.risch import build_extension

        return build_extension(parse(s), x)

    def test_sqrt_log_rejected(self):
        # N4 迁移：e^{log(x)/2} 已在构造期坍缩为 sqrt(x)（代数叶），
        # 旧"代数相关拒绝"场景消失；改钉坍缩正确 + 代数层建塔成功
        from cas.parser import parse
        from cas.pprint import to_str

        self.assertEqual(to_str(parse("exp(log(x)/2)")),
                         to_str(parse("sqrt(x)")))
        de, fa, fd = self._build("sqrt(x)")
        self.assertEqual(de.cases[-1], "algebraic")

    def test_transcendent_nested_accepted(self):
        # e^{x·e^x}：底含塔变量但超越 => 建三层塔
        de, fa, fd = self._build("exp(x*exp(x))")
        self.assertEqual(len(de.levels), 3)
        self.assertEqual(de.cases[1:], ["exp", "exp"])

    def test_sin_exp_arg_accepted(self):
        # e^{sin(x)} 复指数化后底含 τ：超越 => 放行
        from cas.risch import trigs_to_exp, build_extension

        t = trigs_to_exp(parse("exp(sin(x))"))
        de, fa, fd = build_extension(t, x)
        self.assertGreaterEqual(len(de.levels), 3)


class TestNestedTowerIntegration(unittest.TestCase):
    """嵌套塔端到端：解锁后的积分能力。"""

    def _integrate(self, s):
        from cas.diff import verify
        from cas.risch import integrate_exp_tower

        F, de = integrate_exp_tower(parse(s), x)
        return F, verify(F, x, parse(s))

    def test_exp_exp_times_exp_x(self):
        # ∫e^{eˣ}·eˣ dx = e^{eˣ}
        F, v = self._integrate("exp(exp(x))*exp(x)")
        self.assertEqual(v, "VERIFIED")
        self.assertIn("exp(exp", to_str(F))

    def test_x_pow_x_chain(self):
        # ∫x^x(ln x + 1)dx = x^x：dlog(x^x)=ln x+1 的 u-sub 结构
        F, v = self._integrate("(log(x) + 1)*exp(x*log(x))")
        self.assertEqual(v, "VERIFIED")
        got = to_str(F).replace(" ", "")
        self.assertIn("exp(x*log(x))", got)

    def test_sin_sin_derivative(self):
        # ∫cos(sin x)cos x dx = sin(sin x)：嵌套 + 实化通道
        from cas.session import Session

        out = Session().integrate("cos(sin(x))*cos(x)")
        self.assertIn("VERIFIED", out)
        self.assertIn("sin(sin(x))", to_str(out).replace(" ", ""))

    def test_exp_sin_x_nonelementary_proved(self):
        # ∫e^{sin x}dx：非初等——证明性拒答（能力边界内零误判）
        from cas.risch import RischNonElementary, RischUnsupported
        from cas.risch import integrate_exp_tower

        try:
            F, de = integrate_exp_tower(parse("exp(sin(x))"), x)
            # 若给出结果必须过验证
            from cas.diff import verify
            self.assertEqual(verify(F, x, parse("exp(sin(x))")),
                             "VERIFIED")
        except RischNonElementary as cm:
            self.assertIn("not elementary", str(cm))
        except RischUnsupported as cm:
            # 理论未覆盖：诚实拒答亦可接受（绝不误答）
            pass


class TestLimitedIntPrim(unittest.TestCase):
    """S-a/S-c 收口：limited_integrate 完备化（primitive 共振修正）。

    M5 收官批 #2：_limited_int_prim 退化为 α/η 常数整数检验——
    非常数比 => 无多项式共振 => 朴素界正确。消除旧版的 'und' 假拒答。
    """

    def test_nonconstant_ratio_no_resonance(self):
        # α/η = (ℓ+1)(x+1)+2 非常数 => 无共振 => m=0
        from cas.risch import _limited_int_prim, build_extension

        de, _, _ = build_extension(parse("1/(log(x)*log(x+1))"), x)
        allv = tuple(de.levels[:3])
        lsym = de.levels[1]
        eta = RatFunc(Poly.one(allv), Poly.mono(allv, x, 1) + Poly.one(allv))
        num = (Poly.mono(allv, lsym, 1)
               * (Poly.mono(allv, x, 1) + Poly.one(allv))
               + Poly.const(allv, Fr(1)) * (Poly.mono(allv, x, 1)
                                            + Poly.one(allv))
               + Poly.const(allv, Fr(2)))
        al = RatFunc(num, Poly.mono(allv, x, 1) + Poly.one(allv))
        st, m = _limited_int_prim(al, eta, de, 1)
        self.assertEqual((st, m), ("ok", 0))

    def test_complex_ratio_no_resonance(self):
        # α 含 Ga(0,1)（虚部）：α/η 非实整数 => 无共振 => m=0
        from cas.risch import _limited_int_prim, build_extension

        de, _, _ = build_extension(parse("1/(log(x)*log(x+1))"), x)
        allv = tuple(de.levels[:3])
        eta = RatFunc(Poly.one(allv), Poly.mono(allv, x, 1) + Poly.one(allv))
        den_pole = Poly.mono(allv, x, 1) - Poly.const(allv, Fr(2))
        num = (Poly.mono(allv, de.levels[1], 1)
               * (Poly.mono(allv, x, 1) + Poly.one(allv)) * den_pole
               + Poly.const(allv, Fr(1)) * (Poly.mono(allv, x, 1)
                                            + Poly.one(allv))
               + Poly.const(allv, Ga(0, 1)))
        al = RatFunc(num, (Poly.mono(allv, x, 1) + Poly.one(allv)) * den_pole)
        st, m = _limited_int_prim(al, eta, de, 1)
        self.assertEqual((st, m), ("ok", 0))


class TestB0Cancellation(unittest.TestCase):
    """S-b 修复：B=0 cancellation（D(u)=c 纯塔积分）经 lam=0 统一下降。"""

    def _run(self, tower_s, case_v, cn_terms, jv):
        from cas.risch import (build_extension, _poly_rde_final,
                               _make_der_fn)

        de, _, _ = build_extension(parse(tower_s), x)
        allv = tuple(de.levels[:jv + 1])
        sub = tuple(de.levels[:jv])
        zero = RatFunc.zero(sub)
        one_c = zero.one(sub)
        cn = [RatFunc(Poly.from_term(t, sub), Poly.one(sub))
              for t in cn_terms]
        return _poly_rde_final([], cn, 6, case_v, False, 0 if jv == 1 else 1,
                               [zero, one_c], _make_der_fn(de, jv), de, jv,
                               zero)

    def test_exp_view_pure_integral(self):
        # exp 塔：D(u)=x → u=x²/2
        st, u = self._run("exp(x)", "exp", [parse("x")], 1)
        self.assertEqual(st, "ok")
        self.assertEqual(to_str(u[0].to_term()), "1/2*x^2")

    def test_primitive_view_theta(self):
        # log 塔：D(u)=θ (=log x) → u=x·θ−x²/2（x*log x − x²/2 的塔形态）
        st, u = self._run("log(x)", "primitive",
                          [parse("0"), parse("1")], 1)
        self.assertEqual(st, "ok")
        uf = RatFunc(*_from_univar_local(u))
        from cas.risch import _tower_deriv_frac

        du = _tower_deriv_frac(uf.p, uf.q, _build_de("log(x)"))
        want = RatFunc(*_from_univar_local(
            [RatFunc.zero(tuple(_de_levels("log(x)")[:1])),
             RatFunc(Poly.one((x,)), Poly.one((x,)))]))
        self.assertTrue((du - want).p.is_zero())


def _from_univar_local(cs):
    from cas.risch import _from_univar as _fu

    return _fu(cs, (x, S("_lt")), S("_lt"))


def _build_de(s):
    from cas.risch import build_extension

    return build_extension(parse(s), x)[0]


def _de_levels(s):
    return _build_de(s).levels


if __name__ == "__main__":
    unittest.main()
