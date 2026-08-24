"""M7.0 代数扩张域算术测试（docs/m7_algfield.md 正确性锚点）。"""

import unittest
from fractions import Fraction as Fr

from cas.parser import parse
from cas import term as T
from cas.term import S, N

x = S("x")
from cas.errors import PolyError
from cas.algfield import (AlgField, AlgElem, af_q, af_func, af_norm,
                          af_res, af_irreducible_q)


def _sqrt2_term():
    return parse("sqrt(2)")


class TestQField(unittest.TestCase):
    """ℚ(√2)：基本算术 + 迹/范数锚点。"""

    def setUp(self):
        self.fld = af_q([Fr(-2), Fr(0), Fr(1)], origin=_sqrt2_term())
        self.a = self.fld.gen()

    def test_reduce_on_mul(self):
        a2 = self.a * self.a
        self.assertEqual(a2.cs, [Fr(2)])

    def test_inv(self):
        one = self.fld.const(Fr(1))
        u = one + self.a
        self.assertEqual(u.inv().cs, [Fr(-1), Fr(1)])   # 1/(1+√2) = √2−1

    def test_pow(self):
        p = self.a ** 3                                  # (√2)³ = 2√2
        self.assertEqual(p.cs, [Fr(0), Fr(2)])
        n = self.a ** (-1)                               # 1/√2 = √2/2
        self.assertEqual(n.cs, [Fr(0), Fr(1, 2)])

    def test_trace(self):
        self.assertEqual(self.fld.trace(self.a), Fr(0))
        one = self.fld.const(Fr(1))
        self.assertEqual(self.fld.trace(one), Fr(2))
        a2 = self.a * self.a                             # Tr((√2)²)=s₂=4
        self.assertEqual(self.fld.trace(a2), Fr(4))

    def test_norm(self):
        v = self.fld.const(Fr(3)) + self.fld.const(Fr(4)) * self.a
        # N(3+4√2) = 9 − 32 = −23
        self.assertEqual(af_norm(v), Fr(-23))
        self.assertEqual(af_norm(self.a), Fr(-2))        # (√2)(−√2) = −2

    def test_div_and_eq(self):
        one = self.fld.const(Fr(1))
        q = one / (one + self.a)
        self.assertEqual(q, -one + self.a)

    def test_mixed_field_rejected(self):
        fld2 = af_q([Fr(-3), Fr(0), Fr(1)])
        with self.assertRaises(PolyError):
            _ = self.a + fld2.gen()

    def test_squarefree_guard(self):
        from fractions import Fraction as _F
        with self.assertRaises(PolyError):
            AlgField([_F(0), _F(0), _F(0), _F(1)], _F(1))   # T³ 非无平方


class TestGaussParity(unittest.TestCase):
    """ℚ(i)：与 Ga 高斯有理域逐值对拍。"""

    def test_product_parity(self):
        fld = af_q([Fr(1), Fr(0), Fr(1)])                # T²+1
        a = fld.gen()
        for (ar, ai), (br, bi) in [((1, 2), (3, -1)), ((-2, 5), (7, 3)),
                                   ((0, 1), (0, 1))]:
            e1 = fld.const(Fr(ar)) + fld.const(Fr(ai)) * a
            e2 = fld.const(Fr(br)) + fld.const(Fr(bi)) * a
            prod = e1 * e2
            g = _ga(ar, ai) * _ga(br, bi)
            self.assertEqual(prod.cs[0] if len(prod.cs) > 0 else Fr(0),
                             g.re)
            self.assertEqual(prod.cs[1] if len(prod.cs) > 1 else Fr(0),
                             g.im)

    def test_i_pow_cycle(self):
        fld = af_q([Fr(1), Fr(0), Fr(1)])
        a = fld.gen()
        self.assertEqual((a ** 3).cs, [Fr(0), Fr(-1)])   # i³ = −i
        self.assertEqual((a ** 4).cs, [Fr(1)])           # i⁴ = 1

    def test_norm_units(self):
        fld = af_q([Fr(1), Fr(0), Fr(1)])
        a = fld.gen()
        u = fld.const(Fr(1)) + a                         # N(1+i) = 2
        self.assertEqual(af_norm(u), Fr(2))


class TestCubic(unittest.TestCase):
    """ℚ(∛2)。"""

    def setUp(self):
        self.fld = af_q([Fr(-2), Fr(0), Fr(0), Fr(1)])
        self.a = self.fld.gen()

    def test_norm_gen(self):
        # N(α) = Πβⱼ = 2（monic T³−2 常数项 −2 ⟹ Πβⱼ = 2）
        self.assertEqual(af_norm(self.a), Fr(2))

    def test_trace_gen_sq(self):
        a2 = self.a * self.a
        self.assertEqual(self.fld.trace(a2), Fr(0))

    def test_mul_reduction(self):
        lhs = (self.a * self.a + self.a) * (self.a + self.fld.const(Fr(1)))
        # α³+α²+α²+α ≡ 2 + α + 2α²
        self.assertEqual(lhs.cs, [Fr(2), Fr(1), Fr(2)])


class TestFunctionBase(unittest.TestCase):
    """函数基 K = ℚ(x)(α)，α = √(x²+1)。"""

    def setUp(self):
        xv = S("x")
        rf = lambda s: __import__("cas.ratfunc", fromlist=["RatFunc"]) \
            .RatFunc.from_term(parse(s), (xv,))
        self.xv = xv
        self.rf = rf
        # m = T² − (x²+1)，升序 [-(x²+1), 0, 1]
        self.fld = af_func(
            [-rf("x^2+1"), rf("0"), rf("1")], (xv,), origin=None)
        self.a = self.fld.gen()
        self.x = self.fld.elem([rf("x")])

    def test_conic_identity(self):
        # (x+α)(x−α) ≡ x² − α² ≡ −1
        p = (self.x + self.a) * (self.x - self.a)
        self.assertEqual(p.cs[0].to_term(), N(Fr(-1)))
        self.assertTrue(len(p.cs) == 1)

    def test_norm_x_plus_alpha(self):
        # N(x+α) = (x+β)(x−β) = x² − β² = −1
        v = self.x + self.a
        nrm = af_norm(v)
        self.assertEqual(nrm.to_term(), N(Fr(-1)))

    def test_inv_roundtrip(self):
        v = self.x + self.a
        one = self.fld.const(self.rf("1"))
        self.assertEqual(v * v.inv(), one)


class TestResultant(unittest.TestCase):

    def test_res_anchor(self):
        # Res(T²−2, 3−T) = (3−√2)(3+√2) = 7
        fld = af_q([Fr(0), Fr(1)], Fr(1))
        r = af_res([Fr(-2), Fr(0), Fr(1)], [Fr(3), Fr(-1)], fld)
        self.assertEqual(r, Fr(7))

    def test_res_zero_arg(self):
        fld = af_q([Fr(-2), Fr(0), Fr(1)], Fr(1))
        r = af_res(fld.m, [], fld)
        self.assertEqual(r, Fr(0))


class TestRetraction(unittest.TestCase):

    def test_to_term_numeric(self):
        fld = af_q([Fr(-2), Fr(0), Fr(1)], origin=_sqrt2_term())
        v = fld.const(Fr(3)) + fld.const(Fr(2)) * fld.gen()   # 3+2√2
        t = v.to_term()
        from cas.evalnum import eval_approx
        val = eval_approx(t, {})
        self.assertAlmostEqual(float(val), 3.0 + 2.0 * 2 ** 0.5, places=10)


class TestIrreducibility(unittest.TestCase):

    def test_q_irreducible(self):
        self.assertIs(af_irreducible_q(af_q([Fr(-2), Fr(0), Fr(1)])), True)
        self.assertIs(af_irreducible_q(af_q([Fr(-1), Fr(0), Fr(1)])), False)

    def test_non_q_unknown(self):
        xv = S("x")
        from cas.ratfunc import RatFunc
        fld = af_func([RatFunc.from_term(N(Fr(-2)), (xv,)),
                       RatFunc.zero((xv,)),
                       RatFunc.one((xv,))], (xv,))
        self.assertIsNone(af_irreducible_q(fld))


class TestCapelli(unittest.TestCase):
    """M7.2 Capelli 二项式不可约判定（T^n − G over ℚ(params)）。

    锚点含 Sophie Germain 经典：T⁴+4 = (T²+2T+2)(T²−2T+2) 可约
    （G=−4 ∈ −4K⁴ 判据 ii）；T⁴+16 在 ℚ 上不可约（易错对照）。
    """

    def _poly(self, vs, d):
        from cas.poly import Poly
        return Poly(vs, {k: Fr(v) for k, v in d.items()})

    def setUp(self):
        from cas.poly import Poly
        self.one = Poly((), {(): Fr(1)})
        self.a = S("a")

    def test_quadratic_symbolic(self):
        from cas.algfield import binomial_irreducible
        G = self._poly((self.a,), {(0,): -4, (2,): 1})
        self.assertTrue(binomial_irreducible(G, self.one, 2))
        G2 = self._poly((self.a,), {(2,): 1})
        self.assertFalse(binomial_irreducible(G2, self.one, 2))

    def test_sophie_germain(self):
        from cas.algfield import binomial_irreducible
        self.assertFalse(binomial_irreducible(
            self._poly((), {(): -4}), self.one, 4))
        # T^4+16 在 ℚ 上确实不可约（√2 系数因子）
        self.assertTrue(binomial_irreducible(
            self._poly((), {(): -16}), self.one, 4))

    def test_higher_degree_and_denominator(self):
        from cas.algfield import binomial_irreducible
        self.assertFalse(binomial_irreducible(
            self._poly((), {(): 8}), self.one, 3))       # ∛8 = 2
        self.assertTrue(binomial_irreducible(
            self.one, self._poly((self.a,), {(1,): 1}), 2))  # T²−1/a
        b = S("b")
        pa = self._poly((self.a, b), {(2, 0): 1})
        pb = self._poly((self.a, b), {(0, 4): 1})
        self.assertFalse(binomial_irreducible(pa * pb, self.one, 4))
        self.assertTrue(binomial_irreducible(pa + pb, self.one, 4))


class TestSymbolicRadicalGuard(unittest.TestCase):
    """M7.2 符号底根式登记 + 塔路径诚实边界。"""

    def test_symbolic_registration(self):
        import cas.term as T
        from cas.risch_core import _collect_radical
        from cas.algfield import ALG_FIELDS, unregister_alg_fields

        rad = parse("(a^2-4)^(1/2)")
        subs = {}
        _collect_radical(rad, subs, xv=x)
        self.assertEqual(len(subs), 1)
        sym = subs[rad]
        try:
            fld = ALG_FIELDS[sym]
            self.assertIsNotNone(fld.key)
            self.assertEqual(fld.key[0], "sym")
            mp = fld.minpoly_poly(sym)
            self.assertEqual(mp.degree(sym), 2)
        finally:
            unregister_alg_fields([sym])

    def test_degenerate_radical_refused(self):
        # √(a²)：极小多项式 T²−a² 可约（a 是平方根本身）——诚实拒绝，
        # 绝不静默登记错误域
        from cas.risch_core import RischUnsupported, _collect_radical

        rad = parse("(a^2)^(1/2)")
        with self.assertRaises(RischUnsupported):
            _collect_radical(rad, {}, xv=x)

    def test_tower_guard_instant_refusal(self):
        # ∫eˣ/(e²ˣ+a·eˣ+1)：残数 ∈ ℚ(a,√(a²−4))——塔路径即时诚实
        # 拒答（修复前：系数 gcd 次数爆炸挂死）
        from cas.integrate import integrate
        from cas.risch_core import RischUnsupported

        f = parse("exp(x)/(exp(2*x)+a*exp(x)+1)")
        with self.assertRaises(RischUnsupported) as cm:
            integrate(f, x)
        self.assertIn("coefficient-field upgrade", str(cm.exception))


def _ga(re, im):
    from cas.gaussian import Ga
    return Ga(Fr(re), Fr(im))


if __name__ == "__main__":
    unittest.main()
