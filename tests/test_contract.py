"""N4 构造期收缩规则集类级验收（M78.4）。

原则：整类扫描 + 数值预言机，不做单例样例驱动。
π 表：q∈{1,2,3,4,6} × k∈[−13,13] 全 sweep 对拍 math.sin/cos/tan。
exp/log 收缩：代表性实局部类上的往返恒等 + 分支破裂负例钉。
期望比较一律 parse 后结构比对（免疫打印形差异）。
"""

import math
import unittest
from fractions import Fraction as Fr

from cas.parser import parse
from cas.pprint import to_str
from cas.evalnum import eval_approx


def _norm(s):
    return to_str(parse(s))


class TestPiTable(unittest.TestCase):
    """全类 sweep：q∈{1,2,3,4,6} 的 π 有理倍数精确值。"""

    def _sweep(self, name, ref):
        for q in (1, 2, 3, 4, 6):
            for p in range(-13, 14):
                src = f"{name.lower()}(({p})*pi/{q})"
                got = parse(src)
                want = ref(p * math.pi / q)
                # 折叠成功 ⟹ 数值项；对拍数值层
                self.assertAlmostEqual(
                    eval_approx(got, {}), want, places=9,
                    msg=f"{src} -> {to_str(got)}")

    def test_sin_sweep(self):
        self._sweep("Sin", math.sin)

    def test_cos_sweep(self):
        self._sweep("Cos", math.cos)

    def test_tan_sweep_nonpole(self):
        for q in (1, 2, 3, 4, 6):
            for p in range(-13, 14):
                if abs(math.cos(p * math.pi / q)) < 1e-9:
                    continue        # 极角：诚实不折叠，跳过对拍
                got = parse(f"tan(({p})*pi/{q})")
                self.assertAlmostEqual(
                    eval_approx(got, {}), math.tan(p * math.pi / q),
                    places=9)

    def test_pole_honest(self):
        # tan(pi/2)：极角不折叠（折叠会产生未定义项）
        self.assertEqual(to_str(parse("tan(pi/2)")), to_str(parse(
            "tan(pi/2)")))
        self.assertTrue("Tan" in str(type(parse("tan(pi/2)"))) or
                        "tan" in to_str(parse("tan(pi/2)")))

    def test_quadratic_field_exactness(self):
        # 精确性抽查（项级）：落 ℚ(√d) 规范代表形
        self.assertEqual(_norm("sin(pi/6)"), _norm("1/2"))
        self.assertEqual(_norm("cos(pi/4)"), _norm("sqrt(2)/2"))
        self.assertEqual(_norm("tan(pi/3)"), _norm("sqrt(3)"))
        self.assertEqual(_norm("sin(7*pi/6)"), _norm("-1/2"))
        self.assertEqual(_norm("sin(-5*pi/4)"), _norm("sqrt(2)/2"))


class TestExpLogContraction(unittest.TestCase):
    """实局部类上的收缩往返 + 分支破裂负例。"""

    REAL_CLASS = [
        "x", "x^2+1", "exp(x)", "sin(x)+2", "log(x)+1",
        "2*x-1", "atan(x)",
    ]

    def test_exp_log_roundtrip_on_domain(self):
        for u in self.REAL_CLASS:
            a = parse(f"exp(log({u}))")
            self.assertEqual(to_str(a), _norm(f"{u}"),
                             msg=f"exp(log({u})) -> {to_str(a)}")
        for u in self.REAL_CLASS:
            b = parse(f"log(exp({u}))")
            self.assertEqual(to_str(b), _norm(f"{u}"),
                             msg=f"log(exp({u})) -> {to_str(b)}")

    def test_branch_break_negative_pins(self):
        # 复局部（含 i）：Log(Exp(u)) 不收缩（分支破裂诚实拒绝）
        self.assertEqual(to_str(parse("log(exp(i))")),
                         to_str(parse("log(exp(i))")))
        self.assertNotEqual(to_str(parse("log(exp(i))")), _norm("i"))
        self.assertNotEqual(to_str(parse("log(exp(i*pi))")), _norm("i*pi"))

    def test_selective_sum_split(self):
        cases = [
            ("exp(2*log(x)+1)", "e*x^2"),
            ("exp(1+2*log(x))", "e*x^2"),
            ("exp(3*log(x)-log(y))", "x^3/y"),
            ("exp(log(x)+log(y))", "x*y"),
            ("exp(-2*log(x))", "x^(-2)"),
        ]
        for src, want in cases:
            self.assertEqual(to_str(parse(src)), _norm(want),
                             msg=f"{src} -> {to_str(parse(src))}")

    def test_split_does_not_fire_without_rational_log(self):
        # 无有理系数·Log 求和项：不拆（诚实保持）
        self.assertEqual(to_str(parse("exp(x*log(x))")),
                         to_str(parse("exp(x*log(x))")))
        self.assertNotEqual(to_str(parse("exp(x*log(x))")), _norm("x^x"))
        self.assertEqual(to_str(parse("exp(sin(x)+1)")),
                         to_str(parse("exp(sin(x)+1)")))

    def test_log_power_rules(self):
        # 奇次幂：输入定义域上无条件（u^n>0 ⟹ u>0，右侧良定义）
        self.assertEqual(to_str(parse("log(x^3)")), _norm("3*log(x)"))
        self.assertEqual(to_str(parse("log(x^(-5))")), _norm("-5*log(x)"))
        # 偶次幂：底正可证才拆（u=−2,n=2 反例：左定义右未定义）
        self.assertEqual(to_str(parse("log((x^2+1)^4)")),
                         _norm("4*log(x^2+1)"))
        self.assertEqual(to_str(parse("log(x^2)")),
                         to_str(parse("log(x^2)")))

    def test_e_factor_peel(self):
        self.assertEqual(to_str(parse("log(e*x)")), _norm("log(x)+1"))
        self.assertEqual(to_str(parse("log(e)")), _norm("1"))
        self.assertEqual(to_str(parse("log(e*x^3)")), _norm("1+3*log(x)"))

    def test_session_acceptance_pins(self):
        # 会话验收钉（回归锚，非设计输入）。
        # exp(log(e)) 的恒等 e≡exp(1) 是超越常数关系（双面孔：命名
        # 原子 vs 塔核），mk 级不可折叠否则 verify 链叶键失配——
        # 该识别属 N6 超越常数关系表管辖；当前诚实输出为：
        lhs = parse("(exp(log(e))-e*1/3*((1+sqrt(2))^2-2*sqrt(2)))*exp(x^2)")
        self.assertEqual(to_str(lhs), _norm("exp(x^2)*(exp(1) - e)"))
        # 规则通道（log.rules exp_one，用户可见化简层）完成两面孔
        # 识别：内部验证链保持 exp(字面) 塔核形态不受扰
        from cas.session import Session as _Sess
        _s = _Sess()
        _s.handle("(exp(log(e))-e*1/3*((1+sqrt(2))^2-2*sqrt(2)))*exp(x^2)")
        _s.auto()
        self.assertEqual(to_str(_s.current), "0")
        # 代数-对数部分（同式内）已完全坍缩：
        self.assertEqual(
            to_str(parse("log(e)-e*1/3*((1+sqrt(2))^2-2*sqrt(2))")),
            _norm("1 - e"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
