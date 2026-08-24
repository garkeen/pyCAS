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
from cas.poly import Poly
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
        self.assertEqual(to_str(de.ws[1].to_term()), "-2*x")
        # f = t / 1
        self.assertEqual(to_str(fa.to_term()), "t")
        self.assertTrue(fd.is_const())

    def test_integer_power_grouping(self):
        # e^x + e^(x/2)：归组到基 x/2，f = t^2 + t
        de, fa, fd = _build("exp(x) + exp(x/2)")
        self.assertEqual(to_str(de.ws[1].to_term()), "1/2")
        self.assertEqual(to_str(fa.to_term()), "t + t^2")

    def test_grouping_higher_degree(self):
        # e^(x^2) 与 e^(2*x^2)：deg 2 的 Fr 倍同样归组
        de, fa, fd = _build("exp(x^2) + exp(2*x^2)")
        self.assertEqual(len(de.levels), 2)
        self.assertEqual(to_str(fa.to_term()), "t + t^2")

    def test_log_primitive_layer(self):
        de, fa, fd = _build("log(x^2 + 1)")
        self.assertEqual(de.cases, ["base", "primitive"])
        self.assertEqual(to_str(de.ws[1].p.to_term()), "2*x")
        self.assertEqual(to_str(de.ws[1].q.to_term()), "x^2 + 1")

    def test_mixed_layers_log_first(self):
        # log 先建（primitive 在下），exp 在外（sympy handle_first='log' 同款）
        de, fa, fd = _build("exp(x)*log(x)")
        self.assertEqual(de.cases, ["base", "primitive", "exp"])
        self.assertEqual(to_str(fa.to_term()), "l*t")

    def test_reject_algebraic_dependency(self):
        # N4 迁移：exp(r·log u) 类代数相关形态已在构造期坍缩为代数叶
        # （e^{log(x)/2} = sqrt(x)），旧守卫场景整体消失（同批：
        # refine log-exp 规则 / auto 重写步均上收为构造期收缩）。
        # 改钉新行为：坍缩精确 + 建塔走代数层成功。
        from cas.parser import parse
        from cas.pprint import to_str

        self.assertEqual(to_str(parse("exp(log(x)/2)")),
                         to_str(parse("sqrt(x)")))
        de, fa, fd = _build("sqrt(x)")
        self.assertEqual(de.cases, ["base", "algebraic"])

    def test_accept_nested_transcendental(self):
        # M5.2c-iii：exp(x*exp(x)) 底含塔变量但超越（精确判定非对数
        # 导数-根式）=> 放行建嵌套塔（原保守守卫一律拒绝，已解锁）
        de, fa, fd = _build("exp(x*exp(x))")
        self.assertEqual(len(de.levels), 3)
        self.assertEqual(de.cases[1:], ["exp", "exp"])

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
        # e^(-x^2)：RDE y' - 2x*y = 1 无有理解 -> 不可初等证明（M5.1b）
        from cas.risch import RischNonElementary

        with self.assertRaises(RischNonElementary) as cm:
            self._integrate("exp(-x^2)")
        self.assertIn("not elementary", str(cm.exception))
        self.assertIn("Risch differential equation", str(cm.exception))

    def test_rde_positive_powers(self):
        # 正幂频率：RDE 多项式解
        r = self._integrate("x^2*exp(x)")
        self.assertEqual(to_str(simplify(r)), "exp(x)*(x^2 - 2*x + 2)")
        self._dcheck("x^2*exp(x)", r)
        r2 = self._integrate("exp(2*x)")
        self.assertEqual(to_str(simplify(r2)), "1/2*exp(2*x)")
        self._dcheck("exp(2*x)", r2)

    def test_rde_negative_frequency(self):
        # 负幂频率 t^-1 = exp(-x)：y' - y = 1 -> y = -1
        r = self._integrate("exp(-x)")
        self.assertEqual(to_str(simplify(r)), "-exp(-x)")
        self._dcheck("exp(-x)", r)

    def test_frequency_cancellation(self):
        # t * t^-1 = 1：频率归并后 k=0 -> x 层
        r = self._integrate("exp(x)*exp(-x)")
        self.assertEqual(to_str(simplify(r)), "x")
        self._dcheck("exp(x)*exp(-x)", r)

    def test_multilayer_nonelementary(self):
        # 双层 exp 塔（M5.2b 递归）：e^x 分量积出、e^(x^2) 分量 RDE 无解
        # => 整体不可初等（频率分量代数独立 => 和可积 <=> 各项可积）
        from cas.risch import RischNonElementary

        with self.assertRaises(RischNonElementary) as cm:
            self._integrate("exp(x) + exp(x^2)")
        self.assertIn("not elementary", str(cm.exception))


class TestRischPrimitive(unittest.TestCase):
    """M5.2a：primitive 层积分（limited_integrate 循环 + Hermite/residue）。

    正确性证据 = 已知闭式逐项比对 + D(result) 数值采样交叉核对。
    """

    SAMPLES = [Fr(3, 2), Fr(5, 2), Fr(7, 3)]

    def _integrate(self, s):
        from cas.risch import integrate_exp_tower

        return integrate_exp_tower(parse(s), x)[0]

    def _dcheck(self, s, result):
        from cas.diff import d

        got = d(result, x)
        want = parse(s)
        for xv in self.SAMPLES:
            gv = eval_approx(got, {x: xv})
            wv = eval_approx(want, {x: xv})
            self.assertAlmostEqual(gv, wv, delta=max(1e-9, abs(wv) * 1e-9),
                                   msg=f"D-check {s} at x={xv}")

    def test_basic_log(self):
        r = self._integrate("log(x)")
        self.assertEqual(to_str(simplify(r)), "x*log(x) - x")
        self._dcheck("log(x)", r)

    def test_poly_times_log(self):
        r = self._integrate("x*log(x)")
        self.assertEqual(to_str(simplify(r)), "1/2*log(x)*x^2 - 1/4*x^2")
        self._dcheck("x*log(x)", r)

    def test_degree_raise(self):
        # ∫log(x)/x = log(x)^2/2：升次（primitive 特有，exp 无此概念）
        r = self._integrate("log(x)/x")
        self.assertEqual(to_str(simplify(r)), "1/2*log(x)^2")
        self._dcheck("log(x)/x", r)
        r2 = self._integrate("(log(x)+1)/x")
        self.assertEqual(to_str(simplify(r2)), "log(x) + 1/2*log(x)^2")
        self._dcheck("(log(x)+1)/x", r2)

    def test_log_squared(self):
        r = self._integrate("log(x)^2")
        self.assertEqual(to_str(simplify(r)),
                         "-2*x*log(x) + x*log(x)^2 + 2*x")
        self._dcheck("log(x)^2", r)

    def test_nested_log(self):
        # ∫dx/(x*log(x)) = log(log(x))：真分式 residue 出塔内 θ 的对数
        r = self._integrate("1/(x*log(x))")
        self.assertEqual(to_str(simplify(r)), "log(log(x))")
        self._dcheck("1/(x*log(x))", r)

    def test_li_nonelementary(self):
        # ∫dx/log(x)：residue 无常数根 -> 不可初等证明（sympy risch 同判）
        from cas.risch import RischNonElementary

        with self.assertRaises(RischNonElementary) as cm:
            self._integrate("1/log(x)")
        self.assertIn("not elementary", str(cm.exception))

    def test_exp_log_nonelementary(self):
        # M5.2c-ii：∫e^x·log(x)dx = e^x·Ei 类，频率方程 y'+y=log(x)
        # 在 ℚ(x,log x) 无有理解——primitive 视角逐度下降 round0
        # D(s)+s=-1/x 判 proved（Ei 成分的机器证明）
        from cas.risch import RischNonElementary, integrate_exp_tower

        with self.assertRaises(RischNonElementary) as cm:
            integrate_exp_tower(parse("exp(x)*log(x)"), x)
        self.assertIn("not elementary", str(cm.exception))

    def test_exp_log_mixed(self):
        # M5.2c-ii：e^x(log x + 1/x) 可积——round0 rhs=1/x-(1/x)*s_1=0，
        # 解 u=log x；与 e^x*log(x) 的 proved 形成判定分界对照
        from cas.risch import integrate_exp_tower

        r = integrate_exp_tower(parse("exp(x)*(1/x + log(x))"), x)[0]
        self.assertEqual(to_str(simplify(r)), "exp(x)*log(x)")
        self._dcheck("exp(x)*(1/x + log(x))", r)


class TestTrigViaComplexExp(unittest.TestCase):
    """M5.3：三角/双曲经复指数——session 级验收（VERIFIED = 出口精确
    验证背书；答案形态为 ℚ(i) 复指数式，实化回 sin/cos 属后续出口层）。"""

    def _int(self, s):
        from cas.session import Session

        return Session().integrate(s)

    def test_tan(self):
        # ∫tan x dx：复形态 = -log(cos x)（差常数意义下精确）
        out = self._int("tan(x)")
        self.assertIn("VERIFIED", out)

    def test_exp_sin(self):
        # 旗舰可积：∫e^x sin x = e^x(sin x - cos x)/2 的 ℚ(i) 形态
        out = self._int("exp(x)*sin(x)")
        self.assertIn("VERIFIED", out)

    def test_exp_cos(self):
        out = self._int("exp(x)*cos(x)")
        self.assertIn("VERIFIED", out)

    def test_sin_over_x_nonelementary(self):
        # M5.5 升级：sin(x)/x 不再拒答，出特殊函数出口 Si(x)
        # （Risch 证明不可积 → 特殊函数匹配 → verify 背书）
        from cas.session import Session

        out = Session().integrate("sin(x)/x")
        self.assertIn("VERIFIED", out)
        self.assertIn("Si(", out)

    def test_constant_integrand(self):
        # 常被积函数快捷通道：∫c dx = c·x（c 不含积分变量；此处直接
        # 打 risch 层，session 的变量自动检测会改取 y 为积分变量）
        from cas.pprint import to_str
        from cas.risch import integrate_exp_tower

        r, _de = integrate_exp_tower(parse("sin(y)"), parse("x"))
        self.assertEqual(to_str(simplify(r)), "x*sin(y)")


class TestConstLogParam(unittest.TestCase):
    """M5.6 首项：变指数幂归一 + Log(常量) 参数化（∫a^x 全族解锁）。

    语义：变指数幂 b^e（e 含 x，底任意）-> Exp(e·Log(b))——通用桥接
    恒等式，与 diff.py 幂规则的单值 Log(b) 承诺自洽；Log(不含 x 的
    项) 作独立超越参数进系数域（ℚ(params,c) 上零等价可判定，
    Richardson 安全），出口回代；状态必须 VERIFIED（出口精确验证背书）。
    """

    def _int(self, s):
        from cas.session import Session

        return Session().integrate(s)

    def test_2_to_x(self):
        out = self._int("2^x")
        self.assertIn("VERIFIED", out)
        self.assertIn("log(2)", out)

    def test_x_times_2_to_x(self):
        # 教科书形态 e^{x ln2}(x/ln2 - 1/ln²2)，分部积分同款
        out = self._int("x*2^x")
        self.assertIn("VERIFIED", out)

    def test_10_to_x(self):
        out = self._int("10^x")
        self.assertIn("VERIFIED", out)
        self.assertIn("log(10)", out)

    def test_mixed_with_rational(self):
        # 参数通道与有理分量共存
        out = self._int("2^x + x")
        self.assertIn("VERIFIED", out)

    def test_numeric_base_power_norm(self):
        # 4^x 经变指数幂归一走同一参数通道
        out = self._int("4^x")
        self.assertIn("VERIFIED", out)

    def test_frac_base(self):
        # 有理底：log(1/3) 参数化，负系数域线性代数
        out = self._int("(1/3)^x")
        self.assertIn("VERIFIED", out)

    def test_param_base_direct(self):
        # 符号参数底 y^x：Log(y) 作独立超越参数（对 x 积分）
        from cas.pprint import to_str
        from cas.risch import integrate_exp_tower

        F, _de = integrate_exp_tower(parse("y^x"), parse("x"))
        self.assertIn("log(y)", to_str(F))

    def test_x_power_x_now_proved_nonelementary(self):
        # 通用化红利：x^x 用户形态直达 Risch 证明（此前仅 exp(x*log(x))
        # 输入可达；变指数幂归一后 Power 形态同路）
        from cas.session import Session

        out = Session().integrate("x^x")
        self.assertIn("NOT ELEMENTARY", out)
        self.assertIn("proved", out)

    def test_exp_regression(self):
        # 回归：普通 Exp 不受参数化影响（spec 表路径）
        out = self._int("exp(2*x)")
        self.assertIn("VERIFIED", out)


class TestGaRationalInt(unittest.TestCase):
    """M5.3.1：ℚ(i) 有理积分——共轭分母展开实虚拆分归约 ℚ 双通道。

    数学：g = p/q，q̄ 系数共轭；q·q̄ 共轭不动 ⟹ 实系数；分子
    p·q̄ = f + i·h，∫g = ∫f + i·∫h（各自全 ℚ 链）。状态必须 VERIFIED。
    """

    def _int(self, s):
        from cas.session import Session

        return Session().integrate(s)

    def test_const_ga_numerator(self):
        # (1+i)/(x²+1) = (1+i)·atan(x)
        out = self._int("(1+i)/(x^2+1)")
        self.assertIn("VERIFIED", out)
        self.assertIn("atan", out)

    def test_ga_pole_pair(self):
        # 1/((x-1)(x+i))：复极点残数实虚拆分，答案为实 log/atan 组合
        out = self._int("1/((x-1)*(x+i))")
        self.assertIn("VERIFIED", out)

    def test_real_regression(self):
        # 回归：纯 ℚ 有理路径不受拆分通道影响
        out = self._int("1/(x^2+1)")
        self.assertIn("atan(x)", out)

    def test_quadratic_irreducible(self):
        # 实二次不可约因子（正判别式）：atan + log 混合
        out = self._int("x/(x^2-2*x+5)")
        self.assertIn("VERIFIED", out)


class TestLogPairingRealify(unittest.TestCase):
    """M5.3.2 出口实化切片二：Laurent 共轭自反 log 配对。

    Log(u)（u 为单虚频率指数多项式）满足 cₙ = conj(c_{d+m−n}) 时
    精确剥出线性项 + 实三角 log；候选整体 verify 背书后才接受。
    """

    def _int(self, s):
        from cas.session import Session

        return Session().integrate(s)

    def test_tan_real_form(self):
        # 旗舰：∫tan x = -log(2 cos x)（差常数意义下与 -log cos x 同）
        out = self._int("tan(x)")
        self.assertIn("VERIFIED", out)
        self.assertIn("cos(x)", out)
        self.assertNotIn("exp(", out)

    def test_nonelementary_unaffected(self):
        # 证明性拒答路径不受出口实化影响
        out = self._int("x*tan(x)")
        self.assertIn("NOT ELEMENTARY", out)
        self.assertIn("proved", out)

    def test_real_slice1_regression(self):
        # 切片一共轭对实化回归：eˣsin 保持实形态
        out = self._int("exp(x)*sin(x)")
        self.assertIn("VERIFIED", out)
        self.assertIn("sin(x)", out)


class TestParamProvisos(unittest.TestCase):
    """M5.6#4 阶段一：参数分母 proviso（generic 答案的成立条件）。

    e^{ax}/a 在 a=0 无定义而原函数存在——静默输出即撒谎；答案中的
    纯参数分母必须声明 Ne(D,0)。Log(常量) 分母是真实非零常数，
    不产生 proviso。
    """

    def _int(self, s):
        from cas.session import Session

        return Session().handle(f"!integrate {s} x")

    def test_exp_ax(self):
        out = self._int("exp(a*x)")
        self.assertIn("VERIFIED", out)
        self.assertIn("proviso", out)
        self.assertIn("a != 0", out)

    def test_a_power_x(self):
        # 退化点 log(a)=0（即 a=1：此时被积函数退化为 1）
        out = self._int("a^x")
        self.assertIn("VERIFIED", out)
        self.assertIn("log(a) != 0", out)

    def test_parts_ax(self):
        out = self._int("x*exp(a*x)")
        self.assertIn("VERIFIED", out)
        self.assertIn("a != 0", out)

    def test_const_log_no_proviso(self):
        # log(2) 是真实非零常数——不得误报
        out = self._int("2^x")
        self.assertIn("VERIFIED", out)
        self.assertNotIn("proviso", out)

    def test_direct_api_provisos_slot(self):
        from cas.integrate import integrate
        from cas.parser import parse

        _F, _ok, _m, provisos = integrate(parse("exp(a*x)"), parse("x"))
        self.assertTrue(any("Ne" in str(type(p)) or p is not None
                            for p in provisos))
        self.assertEqual(len(provisos), 1)


class TestAlgebraicConstants(unittest.TestCase):
    """M5.4 切片 a：根式/命名常数进系数域（参数化 + 关系登记）。

    sqrt(2)/2^(1/3) 类代数常数与 pi/gamma 命名常数同走独立超越参数
    通道（Richardson 安全），关系 monic 多项式入 ALG_RELATIONS 登记
    （SAE 语义：元素=次数<deg(m) 多项式，reduce=udivmod 余项——
    关系感知算术后续切片接入）。
    """

    def _int(self, s):
        from cas.session import Session

        return Session().handle(f"!integrate {s} x")

    def test_exp_sqrt2_x(self):
        out = self._int("exp(sqrt(2)*x)")
        self.assertIn("VERIFIED", out)
        self.assertIn("2^(1/2)", out)

    def test_sqrt2_power_x(self):
        # 底含根式：变指数幂归一 + Log(sqrt(2)) 参数化双机联动
        out = self._int("sqrt(2)^x")
        self.assertIn("VERIFIED", out)

    def test_cube_root_slope(self):
        # 三次根斜率：q=3 极小多项式 X^3-2 登记
        out = self._int("cos(2^(1/3)*x)")
        self.assertIn("VERIFIED", out)
        self.assertIn("2^(1/3)", out)

    def test_quadratic_split_conservative(self):
        # x^2-2 在 Q 上不分裂：保守 RootOf-log 形态（值正确）
        out = self._int("1/(x^2-2)")
        self.assertIn("VERIFIED", out)


class TestLatentRefusalPathPins(unittest.TestCase):
    """M6.7 拆分审计发现的两个潜伏 NameError 的回归钉。

    均在诚实拒答/缩放路径上，主路径测试不覆盖、一触即崩：
    1. _const_blockage_hint 引用 simplify 却从未导入——塔覆盖失败
       且被积式含超越常数项时崩（Richardson 卡点提示路径）；
    2. _wn_normalize 调用从未定义的 _fu_sub——weak normalization
       发现正重数 normal 因子时崩（intpar.spad :1237 右端缩放）。
    """

    def test_const_blockage_hint_no_nameerror(self):
        # exp(sin(1))*x：Exp 参数 sin(1) 非塔上有理式 -> 塔覆盖失败；
        # 提示扫描发现常数三角项 -> 必须走 simplify（修复前 NameError）
        from cas.risch import build_extension, RischUnsupported

        with self.assertRaises(RischUnsupported) as ei:
            build_extension(T.times(T.exp(T.sin(N(1))), x), x)
        self.assertIn("constant problem", str(ei.exception))
        self.assertIn("sin(1)", str(ei.exception))

    def test_fu_sub_contract(self):
        # 直接契约钉：n1/d1 - n2/d2 = (n1*d2 - n2*d1)/(d1*d2)，无约分。
        # 3/2 - 1/4 -> (3*4 - 1*2) / (2*4) = 10/8
        from cas.ratfunc import RatFunc
        from cas.risch_rdesup import _fu_add, _fu_sub

        zero = RatFunc.zero(())
        one_c = zero.one(zero.p.vars)
        rf = lambda v: one_c * Fr(v)

        n, d = _fu_sub([rf(3)], [rf(2)], [rf(1)], [rf(4)], zero)
        self.assertEqual([c.const_val() for c in n], [Fr(10)])
        self.assertEqual([c.const_val() for c in d], [Fr(8)])
        # 对偶性：_fu_sub(a,b,c,d) 与 _fu_add(a,b,-c,d) 同结果
        n_s, d_s = _fu_sub([rf(3)], [rf(2)], [rf(1)], [rf(4)], zero)
        n_a, d_a = _fu_add([rf(3)], [rf(2)], [rf(-1)], [rf(4)], zero)
        self.assertEqual([c.const_val() for c in n_s],
                         [c.const_val() for c in n_a])
        self.assertEqual([c.const_val() for c in d_s],
                         [c.const_val() for c in d_a])

    def test_wn_normalize_scaling_semantics(self):
        # 缩放步语义钉（真塔 jv=1 视图）：_wn_normalize 对正重数 normal
        # 因子执行 fn2/fd2 -= mv*D(pi)/pi——修复前该步调用不存在的
        # _fu_sub 直接 NameError。此处以与实现相同的 _make_der_fn 取
        # D(pi)，并以 _fu_add 对偶作参考实现核对（intpar.spad :1237）。
        #
        # 注：不以 jv=0 合成多项式直驱 _wn_normalize 全流程——空变量
        # 基域是生产不可达配置（求解器入口仅 j>=2 -> jv>=1），其上
        # univar 常数算术退化膨胀，非本钉目标。
        from cas.parser import parse
        from cas.ratfunc import RatFunc
        from cas.risch_core import DiffExt
        from cas.risch_rdesup import _make_der_fn, _fu_add, _fu_sub

        de = DiffExt(x)                       # levels=[x]
        w = RatFunc.from_term(parse("1/x"), (x,))
        de.add("primitive", w, T.mk(T.S("Log"), (x,)), "l")
        der_fn = _make_der_fn(de, 1)
        zero = RatFunc.zero((x,))

        def RT(s):
            return RatFunc.from_term(parse(s), (x,))

        def eq_lists(xs, ys):
            """RatFunc 无值等词：按 (分子 monos, 分母 monos) 结构比对。"""
            return len(xs) == len(ys) and all(
                xp.p.monos == yp.p.monos and xp.q.monos == yp.q.monos
                for xp, yp in zip(xs, ys))

        # pi = tau + 1：D(pi) = w = 1/x -> 缩放项 mv*D(pi) = [3/x]
        pi = [RT("1"), RT("1")]
        n2 = [c * Fr(3) for c in der_fn(pi)]
        self.assertEqual(len(n2), 1)
        # fn2/fd2 - mv*D(pi)/pi == _fu_add 对偶参考实现
        from cas.pprint import to_str
        self.assertEqual(to_str(n2[0].to_term()), "3/x")
        # fn2/fd2 - mv*D(pi)/pi == _fu_add 对偶参考实现
        fn = [RT("5"), RT("2")]               # 5 + 2*tau（任意干净输入）
        fd = [RT("3")]
        got_n, got_d = _fu_sub(fn, fd, n2, pi, zero)
        exp_n, exp_d = _fu_add(fn, fd, [RT("-3/x")], pi, zero)
        self.assertTrue(eq_lists(got_n, exp_n))
        self.assertTrue(eq_lists(got_d, exp_d))


class TestM71ResidueField(unittest.TestCase):
    """M7.1 z-常数中间层：代数常数残根落域（ℚ(α) 残数 → VERIFIED）。

    数学背景：∫eˣdx/(e²ˣ−2) 中 τ=eˣ 层的残数为 ±1/(2√2) ∈ ℚ(√2)
    ——修复前 honest 'und'（"algebraic residue roots beyond ..."），
    修复后残根经 ALG_FIELDS 建域、参数化符号穿算术、出口回化根式。
    """

    def _integ(self, s):
        from cas.integrate import integrate

        return integrate(parse(s), x)

    def test_alg_const_residue_unlocked(self):
        from cas.diff import verify

        f = parse("exp(x)/(exp(2*x)-2)")
        F, ok, m, provisos = self._integ("exp(x)/(exp(2*x)-2)")
        self.assertTrue(ok)
        # 理论形态：(1/(2√2))·ln((eˣ−√2)/(eˣ+√2)) = (±√2/4)(ln 差)
        s = to_str(F)
        self.assertIn("log(exp(x) - 2^(1/2))", s)
        self.assertIn("log(exp(x) + 2^(1/2))", s)
        self.assertIn("2^(1/2)", s)
        self.assertNotIn("_a", s)             # 参数化符号必须全部回化
        self.assertEqual(verify(F, x, f), "VERIFIED")

    def test_rational_residue_still_works(self):
        # 对照：有理残数路径不受影响 ∫eˣ/(e²ˣ−1) = ½ln((eˣ−1)/(eˣ+1))
        from cas.diff import verify

        f = parse("exp(x)/(exp(2*x)-1)")
        F, ok, _m, _pv = self._integ("exp(x)/(exp(2*x)-1)")
        self.assertTrue(ok)
        self.assertEqual(verify(F, x, f), "VERIFIED")

    def test_nonconst_residue_proved_refusal(self):
        # ∫dx/(eˣ+x)：唯一极点残数 1/(1-x) 非常数（p 与 D(p) 互素，
        # 正规极点前提成立）⟹ Liouville 定理 proved 不可初等——
        # 方向安全序钉：绝不允许未来改动把它翻成可积或 'und'
        from cas.risch_core import RischNonElementary

        with self.assertRaises(RischNonElementary):
            self._integ("1/(exp(x)+x)")

    def test_string_var_normalized(self):
        # M7.1 附带诚实性修复：字符串变量名曾绕过驻留 Sym 归一，
        # eˣ 建层后残留检查误判 "not covered"（错拒载体伪装成超界）
        from cas.integrate import integrate
        from cas.diff import verify

        f = parse("exp(x)/(exp(2*x)-2)")
        F, ok, _m, _pv = integrate(f, "x")
        self.assertTrue(ok)
        self.assertEqual(verify(F, x, f), "VERIFIED")


class TestM78AlgebraicLayer(unittest.TestCase):
    """M78 合并地基：代数生成元入塔（'algebraic' 层）。

    数学锚：θ=√(x²+1)，D(θ)=η·θ，η=x/(x²+1)；θ² ≡ x²+1（塔不变量
    约简）；exp 与 algebraic 层共存。独立预言机 = diff.d 对回代根式
    形态的数值采样（两个独立实现必须一致）。
    """

    def _build(self, s):
        from cas.risch import build_extension

        return build_extension(parse(s), x)

    def test_build_and_structure(self):
        de, fa, fd = self._build("1/sqrt(x^2+1)")
        self.assertEqual(de.cases, ["base", "algebraic"])
        self.assertEqual(de.minpolys[1][0], 2)
        # f = 1/t：分子 1，分母 θ
        t = de.levels[1]
        self.assertTrue(fa.is_const() and fa.const_val() == 1)
        self.assertEqual(to_str(fd.to_term()), t.name)

    def test_derivation_matches_diff_oracle(self):
        # D(√(x²+1)) = x/√(x²+1)：塔上 derivation 与 diff.d 数值对拍
        from cas.risch_core import derivation

        de, _fa, _fd = self._build("1/sqrt(x^2+1)")
        t = de.levels[1]
        tpoly = Poly.mono(de.vars, t, 1)
        dn, dd = derivation(tpoly, de)
        # 塔上值：η·θ；先把塔符号代入回代形态再数值采样
        from cas.diff import d as diff_d
        from cas.evalnum import eval_approx

        theta_term = de.terms[1]          # 回代形态
        num_s = T.subst(dn.to_term(), {t: theta_term})
        den_s = T.subst(dd.to_term(), {t: theta_term})
        lhs = T.div(num_s, den_s)
        rhs = diff_d(theta_term, x)
        for pt in (0.7, 1.9, 3.2):
            env = {x: pt}
            lv = eval_approx(lhs, env)
            rv = eval_approx(rhs, env)
            self.assertAlmostEqual(float(lv), float(rv), places=8)

    def test_tower_invariant_reduction(self):
        from cas.risch_core import _ta_reduce

        de, _fa, _fd = self._build("1/sqrt(x^2+1)")
        t = de.levels[1]
        tpoly = Poly.mono(de.vars, t, 1)
        red = _ta_reduce(tpoly * tpoly, de)
        self.assertEqual(to_str(red.to_term()), "x^2 + 1")

    def test_mixed_exp_algebraic(self):
        de, fa, fd = self._build("exp(x)/sqrt(x^2+1)")
        self.assertEqual(de.cases, ["base", "exp", "algebraic"])
        t_exp, t_alg = de.levels[1], de.levels[2]
        # f = t_exp / t_alg
        self.assertEqual(to_str(fa.to_term()), t_exp.name)
        self.assertEqual(to_str(fd.to_term()), t_alg.name)

    def test_degenerate_radical_refused(self):
        # √((x+1)²) 型：极小多项式 T²−(x²+2x+1) 在 ℚ(x) 可约——
        # 诚实拒绝（Capelli 判定），绝不建错误域
        from cas.risch_core import RischUnsupported

        with self.assertRaises(RischUnsupported):
            self._build("1/sqrt(x^2+2*x+1)")


if __name__ == "__main__":
    unittest.main()
