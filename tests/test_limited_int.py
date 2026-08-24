"""_limited_int_prim 完备化版（M5 收官批 #2）专项测试。

核心定理：α = m·η + D(z)、z ∈ K₀[τ]（多项式）=> α/η = 整数常数。
逆否：α/η 非整数常数 => 无多项式共振 => 朴素界正确。

完备化把旧版有界探测（m∈1..16 + _integrate_in_K）退化为比率检验——
消除所有 'und' 假拒答路径。
"""

import unittest
from fractions import Fraction as Fr

from cas.parser import parse
from cas.poly import Poly
from cas.ratfunc import RatFunc
from cas.gaussian import Ga
from cas.risch import DiffExt, _limited_int_prim, _embed


def _rf_const(c, vars_):
    return RatFunc(Poly.const(vars_, Fr(c)), Poly.one(vars_))


class TestLimitedIntComplete(unittest.TestCase):
    """α/η 比率检验：整数常数 = 共振；否则无共振。"""

    def setUp(self):
        self.x = parse("x")
        self.de = DiffExt(self.x)

    def test_integer_ratio_resonance(self):
        # α = 3·η => m=3
        eta = _rf_const(Fr(2), (self.x,))
        al = _rf_const(Fr(6), (self.x,))
        st, m = _limited_int_prim(al, eta, self.de, 0)
        self.assertEqual((st, m), ("ok", 3))

    def test_noninteger_ratio_no_resonance(self):
        # α/η = 3/2 => 非整数 => m=0
        eta = _rf_const(Fr(2), (self.x,))
        al = _rf_const(Fr(3), (self.x,))
        st, m = _limited_int_prim(al, eta, self.de, 0)
        self.assertEqual((st, m), ("ok", 0))

    def test_negative_ratio_no_resonance(self):
        # α/η = -2 => 负 => 无正共振 => m=0
        eta = _rf_const(Fr(1), (self.x,))
        al = _rf_const(Fr(-2), (self.x,))
        st, m = _limited_int_prim(al, eta, self.de, 0)
        self.assertEqual((st, m), ("ok", 0))

    def test_complex_ratio_no_resonance(self):
        # α/η 含虚部 => 非实整数 => m=0
        eta = _rf_const(Fr(1), (self.x,))
        al = RatFunc(Poly.const((self.x,), Ga(0, 1)),
                     Poly.one((self.x,)))
        st, m = _limited_int_prim(al, eta, self.de, 0)
        self.assertEqual((st, m), ("ok", 0))

    def test_nonconstant_ratio_no_resonance(self):
        # α/η = x（非常数）=> m=0（旧版此处 'und' 假拒答！）
        eta = _rf_const(Fr(1), (self.x,))
        al = RatFunc(Poly.mono((self.x,), self.x, 1),
                     Poly.one((self.x,)))
        st, m = _limited_int_prim(al, eta, self.de, 0)
        self.assertEqual((st, m), ("ok", 0))

    def test_eta_zero(self):
        # η=0 => m=0（无共振对象）
        eta = RatFunc.zero((self.x,))
        al = _rf_const(Fr(5), (self.x,))
        st, m = _limited_int_prim(al, eta, self.de, 0)
        self.assertEqual((st, m), ("ok", 0))


if __name__ == "__main__":
    unittest.main()
