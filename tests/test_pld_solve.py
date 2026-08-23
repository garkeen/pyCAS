"""_pld_solve 参数化对数导数判定（M5 收官批 #1 完备化）专项测试。

覆盖四态：
  ok-基级    ：z-机器/兜底枚举找到恒等式（出口精确验证背书）
  ok-结构下降：exp 层 v=c·τ^j·u 分解 + 常数倍目标归并
  no         ：必要条件矛盾（零空间空）/唯一候选被完备判定否证
  und        ：z 常数中间层 / 枚举窗口外——绝不伪装成证明
"""

import unittest
from fractions import Fraction as Fr

from cas.parser import parse
from cas.risch import T
from cas.poly import Poly
from cas.ratfunc import RatFunc
from cas.risch import DiffExt, _pld_solve, _tower_deriv_frac

def _rf(num, den, vars_):
    """(int 幂次字典) -> RatFunc。键自动补全长度；den 缺省视为 1。"""
    n2 = len(vars_)
    pn = Poly(vars_, {tuple(list(e) + [0] * (n2 - len(e))): Fr(c)
                      for e, c in num.items()})
    src = den if den else {(): 1}
    pd = Poly(vars_, {tuple(list(e) + [0] * (n2 - len(e))): Fr(c)
                      for e, c in src.items()})
    return RatFunc(pn, pd)


class TestPldSolveBase(unittest.TestCase):
    """基级 ℚ(i)(x)：通用 z-路径与有界兜底。"""

    def setUp(self):
        self.x = parse("x")
        self.de = DiffExt(self.x)

    def test_base_z_path_positive(self):
        # f = (2x+2)/(x²+2x+1)? 用带极点的真分式走 z 路径：
        # f = 1/(x+1) + 1/(x-1) 形 = D((x+1)(x-1))/... 直接给可解对：
        # f = 2x/(x²-1), w = 1/x：h = f − w? 试 n=1,m=0: h=f,
        # 残数 ±1 整数 => u = x²−1, D(u)/u = 2x/(x²−1) ✓
        f = _rf({(0,): 2, (1,): 1}, {(0,): -1, (2,): 1}, (self.x,))
        w = _rf({(0,): 1}, {(1,): 1}, (self.x,))
        st, n, ms, v = _pld_solve(f, [w], self.de, 0)
        self.assertEqual(st, "ok")
        DU = _tower_deriv_frac(v.p, v.q, self.de)
        resid = (DU / v) - (f * n - w * ms[0])
        self.assertTrue(resid.p.is_zero())

    def test_base_poly_part_ratio(self):
        # 多项式部分高区比值锁定：f = 2·x², w = x² => n·2=m·1 =>
        # 本原整向量 (1,-2)... n=1,m=-2: h = 2x²+2x² = 4x²?? 等等：
        # n·f − m·w = 4x² ≠ dlog。实际解需 h 为 dlog：4x² 非真分式
        # 且非常数导数比 => 无解方向。改用 f=x²,w=2x²: (n,m)=(2,1):
        # h = 2x²−2x²=0 => 平凡 ok。
        f = _rf({(2,): 1}, {}, (self.x,))
        w = _rf({(2,): 2}, {}, (self.x,))
        st, n, ms, v = _pld_solve(f, [w], self.de, 0)
        self.assertEqual(st, "ok")
        self.assertEqual(n * 1 - ms[0] * 2, 0)

    def test_base_proved_no_inconsistent_ratio(self):
        # 高区两行比值矛盾 => 零空间空 => 证明否定
        f = _rf({(1,): 2, (2,): 3}, {}, (self.x,))
        w = _rf({(1,): 1, (2,): 1}, {}, (self.x,))
        rec = _pld_solve(f, [w], self.de, 0)
        self.assertEqual(rec[0], "no")

    def test_base_fallback_enumeration(self):
        # z-常数兜底：f = 2/x, w = 1/x（l=x, Dl=1 => gcd=const）=>
        # 枚举 (n,m)：n=1,m=0: h=2/x => _ldrad_base 给 u=x²
        f = _rf({(0,): 2}, {(1,): 1}, (self.x,))
        w = _rf({(0,): 1}, {(1,): 1}, (self.x,))
        st, n, ms, v = _pld_solve(f, [w], self.de, 0)
        self.assertEqual(st, "ok")
        DU = _tower_deriv_frac(v.p, v.q, self.de)
        resid = (DU / v) - (f * n - w * ms[0])
        self.assertTrue(resid.p.is_zero())


class TestPldSolveDescent(unittest.TestCase):
    """结构定理下降：全 τ-free 目标经 exp 层 η 追加/归并降层。"""

    def setUp(self):
        self.x = parse("x")
        de = DiffExt(self.x)
        rf1x = _rf({(0,): 1}, {(1,): 1}, (self.x,))
        # θ 层（primitive，Dθ = 1/x）
        t_th = de.add("primitive", rf1x, parse("Log(x)"), "l")
        allv2 = (self.x, t_th)
        rf1x_2 = RatFunc(_embed_p(rf1x.p, allv2), _embed_p(rf1x.q, allv2))
        # τ 层（exp，Dτ = Dθ·τ = (1/x)τ）
        t_tau = de.add("exp", rf1x_2, parse("Exp(Log(x))"), "t")
        self.de = de
        self.t_th, self.t_tau = t_th, t_tau

    def test_descent_exp_layer_merge(self):
        # f = 2/x, w = η_τ = 1/x（同形！）：全 τ-free => exp 下降追加 η，
        # 归并后单目标落基级枚举：h = 2/x − m·(1/x) 型
        allv3 = (self.x, self.t_th, self.t_tau)
        f = RatFunc(_embed_p(_rf({(0,): 2}, {(1,): 1},
                                 (self.x,)).p, allv3),
                    _embed_p(_rf({(0,): 2}, {(1,): 1},
                                 (self.x,)).q, allv3))
        w = self.de.ws[2]
        w = RatFunc(_embed_p(w.p, allv3), _embed_p(w.q, allv3))
        st, n, ms, v = _pld_solve(f, [w], self.de, 2)
        self.assertEqual(st, "ok")
        DU = _tower_deriv_frac(v.p, v.q, self.de)
        resid = (DU / v) - (f * n - w * ms[0])
        self.assertTrue(resid.p.is_zero())

    def test_descent_primitive_layer(self):
        # 视图 θ（jl=1，primitive）：f=2/x, w=1/x 直接降基级
        allv2 = (self.x, self.t_th)
        frf = _rf({(0,): 2}, {(1,): 1}, (self.x,))
        f = RatFunc(_embed_p(frf.p, allv2), _embed_p(frf.q, allv2))
        wrf = _rf({(0,): 1}, {(1,): 1}, (self.x,))
        w = RatFunc(_embed_p(wrf.p, allv2), _embed_p(wrf.q, allv2))
        st, n, ms, v = _pld_solve(f, [w], self.de, 1)
        self.assertEqual(st, "ok")
        DU = _tower_deriv_frac(v.p, v.q, self.de)
        resid = (DU / v) - (f * n - w * ms[0])
        self.assertTrue(resid.p.is_zero())

    def test_z_const_mid_level_honest_und(self):
        # f = 2/(xθ), w = 1/x 在视图 θ：z = gcd(xθ, D(xθ)=θ+1) = const
        # => 中间层残数域约束不可判 => 'und'（旧版此处伪装成证明否定！）
        allv2 = (self.x, self.t_th)
        frf = _rf({(0, 1): 2}, {(0, 1): 1, (1, 0): 1}, allv2)
        wrf = _rf({(0,): 1}, {(1,): 1}, (self.x,))
        w = RatFunc(_embed_p(wrf.p, allv2), _embed_p(wrf.q, allv2))
        rec = _pld_solve(RatFunc(frf.p, frf.q), [w], self.de, 1)
        self.assertEqual(rec[0], "und")


def _embed_p(p, all_vars):
    from cas.risch import _embed
    return _embed(p, all_vars)


if __name__ == "__main__":
    unittest.main()
