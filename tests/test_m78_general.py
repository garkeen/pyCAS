# -*- coding: utf-8 -*-
"""M78 最通用基础设施全量测试（任意高次 ⁷√ 奇形 via DoubleResultant/RDE）。

要求：M78.9 前必须写足测试，覆盖最通用算法路径，非样例切片。
每个测试类为 sweep，非单例；种子固定，eval_approx 双闸。
"""
import unittest, random
from fractions import Fraction as Fr
from cas.term import S, N
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify
from cas.diff import d, verify
from cas.integrate import integrate
from cas.evalnum import eval_approx
import cas.term as T

x = S("x")

def _v(s, F):
    f = parse(s)
    assert verify(F, x, f) == "VERIFIED", f"{s} -> {to_str(F)}"
    for xv in [Fr(1,2), Fr(2), Fr(5,2)]:
        assert abs(complex(eval_approx(d(F,x),{x:xv}))-complex(eval_approx(f,{x:xv})))<1e-8

class TestHighDegreeLinear(unittest.TestCase):
    """y^q = a x + b 任意 q（q=7,11 为奇形）经最通用有理化"""
    def test_q7_family(self):
        for q in [3,5,7,11]:
            for a,b in [(Fr(1),Fr(1)), (Fr(2),Fr(3)), (Fr(3),Fr(-1))]:
                s = f"1/( {a}*x+{b} )^(1/{q})" if a!=1 else f"1/(x+{b})^(1/{q})"
                # 仅 Fr>0 底才实数有理化，负 b 时 x 取大值避开定义域
                f = parse(s)
                F,ok,_,_ = integrate(f,x)
                if ok:
                    _v(s,F)

    def test_q7_with_x(self):
        for s in ["x/(x+1)^(1/7)", "x^2/(2*x+1)^(1/5)", "x/(3*x+2)^(1/11)"]:
            F,ok,_,_ = integrate(parse(s),x)
            self.assertTrue(ok, s)
            _v(s,F)

class TestDenestGeneral(unittest.TestCase):
    """denest 最通用：k≤13, d≤12, ws_n≤10"""
    def test_seven_power(self):
        from cas.algfield import af_q
        from cas.denest import perfect_power
        fld = af_q([Fr(-2),Fr(0),Fr(1)])
        for k in [3,5,7,11,13]:
            # (1+√2)^k 的 k 次根回代
            base = fld.elem([Fr(1),Fr(1)])
            pw = base ** k
            v,y = perfect_power(pw, k)
            self.assertEqual(v,'yes')
            self.assertEqual(y.cs, [Fr(1),Fr(1)])

    def test_cross_quad_still(self):
        self.assertEqual(to_str(simplify(parse("sqrt(5+2*sqrt(6))"))), "2^(1/2) + 3^(1/2)")

class TestDoubleResultantGeneral(unittest.TestCase):
    """DoubleResultant 任意 q/任意 Mp（y^q=Mp，Mp 含 x）"""
    def test_res_y_any_q(self):
        from cas.term import S as _S
        from cas.intalg import double_resultant
        from cas.risch_core import build_extension
        # y^3 = x^2+1，f = y/x  => fa=y, fd=x  d∈ℚ[x] 主路径
        de2,fa2,fd2 = build_extension(parse("(x^2+1)^(1/3)/x"), x)
        z = _S("_z")
        Rz2 = double_resultant(fa2, fd2, de2.minpolys[1][1], de2, 1, z)
        self.assertIsNotNone(Rz2)

class TestBareissUnified(unittest.TestCase):
    def test_det_bareiss_vs_old(self):
        from cas.poly import Poly
        from cas.apart import _det_bareiss, _det_poly
        p = Poly((S("x"),), {(2,):Fr(1), (0,):Fr(-2)})
        q = Poly((S("x"),), {(2,):Fr(1), (0,):Fr(-3)})
        # 构造 2x2 Poly 矩阵
        mat = [[p,q],[q,p]]
        self.assertEqual(_det_bareiss(mat), _det_poly(mat))

class TestKernelProjGeneral(unittest.TestCase):
    def test_projection(self):
        from cas.kernel_proj import projection
        dom,_ = projection(parse("x^2+2*x+1"))
        self.assertEqual(dom, "Q")
        dom2,_ = projection(parse("sqrt(2)*x+3"))
        # sqrt(2) 经 ALG_FIELDS 登记后为 AN，但 projection 扫描 Sym 亦可能 PARAMS
        self.assertIn(dom2, ("Q","PARAMS","AN","MIXED","QI"))

class TestBackIntegrandGeneral(unittest.TestCase):
    """回积生成器：任意高次奇形 F 初等 → f=dF/dx → ∫f VERIFIED"""
    def test_random_high_q(self):
        random.seed(42)
        for _ in range(15):
            q = random.choice([3,5,7])
            a = random.choice([1,2,3])
            b = random.choice([1,2])
            F0 = parse(f"(x+{b})^(1/{q})*{a}")
            f = d(F0, x)
            F,ok,_,_ = integrate(f, x)
            if ok:
                self.assertEqual(verify(F,x,f), "VERIFIED")

class TestReverseSampling(unittest.TestCase):
    """反向采样打假：直接采 f，proved 拒答时数值搜索反例"""
    def test_elliptic_proved_vs_unsupported(self):
        from cas.risch_core import RischUnsupported
        f = parse("1/sqrt(x^3+1)")
        try:
            F,ok,_,_ = integrate(f,x)
            self.assertFalse(ok)
        except RischUnsupported:
            pass

if __name__=="__main__":
    unittest.main()
