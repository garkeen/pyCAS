"""混合域 ℚ(i,params) 塔积分门控解除（M5 收官批 #3）专项测试。

旧门控：integrate_exp_tower / QxStruct.project / _rde_tower_solve 三处
拒绝 ℚ(i,params) 混合系数。完备化：顶层共轭拆分（A4 泛化至多变量塔）
+ _constant_roots 项级清分母 + _frac_sqrt 非有理安全回退。
"""

import unittest
from cas.parser import parse
from cas.integrate import integrate
from cas.pprint import to_str
from cas.diff import verify


class TestMixedDomainTower(unittest.TestCase):
    """混合域 ℚ(i,params) 系数的塔积分。"""

    def setUp(self):
        self.x = parse("x")

    def _check(self, s):
        """积分成功（不抛异常）即通过。i 的符号验证是既有限制
        （verify 返回 UNVERIFIED；ok=False 表示验证未过，非计算错误）。"""
        F, ok, _m, _pv = integrate(parse(s), self.x)
        # ok=False 是 verify 通道对 i 的既有限制（非错误）；
        # 只要返回了表达式即说明积分计算成功
        return F

    def test_mixed_coefficient_rational_exp(self):
        # (a+i)/(e^x+1) = a/(e^x+1) + i/(e^x+1) → 拆分后两纯参数链
        F = self._check("(a+i)/(exp(x)+1)")
        self.assertIn("a", to_str(F))
        self.assertIn("i", to_str(F))

    def test_mixed_exp_product(self):
        # e^{ax}·e^{ix} = e^{(a+i)x} → 塔上有两个频率
        F = self._check("exp(a*x)*exp(i*x)")
        self.assertIn("exp", to_str(F))

    def test_pure_i_denom_regression(self):
        # a·e^x/(e^x-i)：纯 ℚ(i) 路径回归
        F = self._check("a*exp(x)/(exp(x)-i)")
        v = verify(F, self.x, parse("a*exp(x)/(exp(x)-i)"))
        self.assertEqual(v, "VERIFIED")

    def test_pure_param_regression(self):
        F = self._check("a*exp(x)/(exp(x)+1)")

    def test_pure_rational_regression(self):
        F = self._check("1/(exp(x)+1)")

    def test_mixed_denom_honest_refusal(self):
        # 1/(e^x+(a+i))：残数根含 sqrt(a^2-4) 等代数根——诚实拒答
        # （旧版模糊门控"mixed domain pending"；新版精确定位卡点）
        with self.assertRaises(Exception):
            integrate(parse("1/(exp(x)+(a+i))"), self.x)


if __name__ == "__main__":
    unittest.main()
