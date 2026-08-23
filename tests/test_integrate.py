import unittest

from cas.parser import parse


class TestIntegrate(unittest.TestCase):
    def t(self, s):
        from cas.integrate import integrate

        return integrate(parse(s), parse("x"))[:2]

    def test_verified_cases(self):
        cases = [
            "1", "x", "x^2", "1/(x-1)", "1/(x^2-1)", "x/(x^2-1)", "1/(x^2+1)",
            "x/(x^2+1)", "1/(x^2+x+1)", "1/(x^3-1)", "x/(x^3-1)", "1/(x^2+1)^2",
            "1/(x^2*(x+1))", "(x^3+1)/(x^2+1)", "1/(x^4-1)", "x^5/(x^4-1)",
            "1/(x^2+2*x+2)", "1/(x^3+x)", "1/(x^5-1)", "1/(x^3-2)", "x^2/(x^3-2)",
            "1/(x^4+x^3+x^2+x+1)", "1/((x^2+1)*(x+1)^3)", "(2*x+1)/(x^2+x+1)",
        ]
        for s in cases:
            res, ok = self.t(s)
            self.assertTrue(ok, s)

    def test_known_results(self):
        from cas.pprint import to_str

        res, ok = self.t("x")
        self.assertEqual(to_str(res), "1/2*x^2")
        res, ok = self.t("x^2")
        self.assertEqual(to_str(res), "1/3*x^3")
        res, ok = self.t("1/(x^2-1)")
        self.assertEqual(to_str(res), "1/2*log(x - 1) - 1/2*log(x + 1)")
        res, ok = self.t("1/x")
        self.assertEqual(to_str(res), "log(x)")
        res, ok = self.t("1/(x+1)")
        self.assertEqual(to_str(res), "log(x + 1)")
        res, ok = self.t("x^2/(x-1)")
        self.assertEqual(
            to_str(res), "x + log(x - 1) + 1/2*x^2"
        )

    def test_linear_power(self):
        from cas.pprint import to_str

        res, ok = self.t("1/(x-1)^3")
        self.assertTrue(ok)
        self.assertEqual(to_str(res), "-1/2/(x - 1)^2")
        res, ok = self.t("1/(x^2*(x+1))")
        self.assertTrue(ok)


class TestTrigReduce(unittest.TestCase):
    def r(self, s):
        from cas.trig import trig_reduce

        return trig_reduce(parse(s), parse("x"))

    def test_reduce(self):
        from cas.pprint import to_str

        cases = [
            ("sin(x)^2 + cos(x)^2", "1"),
            ("sin(x)^2", "-1/2*cos(2*x) + 1/2"),
            ("cos(x)^2", "1/2*cos(2*x) + 1/2"),
            ("sin(x)*cos(x)", "1/2*sin(2*x)"),
            ("sin(x)^4 + cos(x)^4", "1/4*cos(4*x) + 3/4"),
            ("sin(x)^3", "3/4*sin(x) - 1/4*sin(3*x)"),
            ("cos(x)^3", "3/4*cos(x) + 1/4*cos(3*x)"),
            ("sin(x)^2 - cos(x)^2", "-cos(2*x)"),
            ("sin(x)^2*cos(x)^2", "-1/8*cos(4*x) + 1/8"),
        ]
        for src, want in cases:
            r = self.r(src)
            self.assertIsNotNone(r, src)
            self.assertEqual(to_str(r), want, src)

    def test_equivalent(self):
        from cas.trig import trig_equivalent

        x = parse("x")
        self.assertIs(trig_equivalent(parse("sin(x)^2+cos(x)^2"), parse("1"), x), True)
        self.assertIs(trig_equivalent(parse("sin(x)^4-cos(x)^4"), parse("sin(x)^2-cos(x)^2"), x), True)
        self.assertIs(trig_equivalent(parse("sin(x)^2"), parse("cos(x)^2"), x), False)

    def test_unsupported(self):
        # sin(2*x) 为合法单谐波（整数频率支持后可归约），不再列入
        for s in ("x+sin(x)", "x*sin(x)", "sin(x)/cos(x)", "1/(1+sin(x))"):
            self.assertIsNone(self.r(s), s)


class TestTrigIntegrate(unittest.TestCase):
    def t(self, s):
        from cas.integrate import integrate

        return integrate(parse(s), parse("x"))[:2]

    def test_verified_cases(self):
        cases = [
            "sin(x)", "cos(x)", "1/(1+sin(x))", "1/(1+cos(x))", "1/cos(x)",
            "1/sin(x)", "sin(x)^2", "cos(x)^2", "1/(sin(x)^2)", "sin(x)*cos(x)",
            "1/(2+sin(x))", "sin(x)/(1+cos(x))", "1/(1+sin(x)+cos(x))", "sin(x)^3",
            "1/(1+cos(x)^2)", "1/(sin(x)*cos(x))", "cos(x)/(1-sin(x))",
            "1/(sin(x)^2+2*cos(x)^2)", "sin(x)^2*cos(x)^2", "1/(cos(x)^2*sin(x))",
        ]
        for s in cases:
            res, ok = self.t(s)
            self.assertTrue(ok, s)

    def test_known_results(self):
        from cas.pprint import to_str

        res, ok = self.t("1/(1+cos(x))")
        self.assertEqual(to_str(res), "tan(1/2*x)")
        res, ok = self.t("1/sin(x)")
        self.assertEqual(to_str(res), "log(tan(1/2*x))")
        res, ok = self.t("1/(1+sin(x))")
        self.assertEqual(to_str(res), "-2/(tan(1/2*x) + 1)")
        res, ok = self.t("1/(1+sin(x)+cos(x))")
        self.assertEqual(to_str(res), "log(tan(1/2*x) + 1)")
        res, ok = self.t("1/(sin(x)^2)")
        self.assertEqual(to_str(res), "-1/2/tan(1/2*x) + 1/2*tan(1/2*x)")

    def test_unsupported(self):
        from cas.errors import PolyError
        from cas.risch import RischNonElementary

        # exp(x)/sin(2x) 已入 spec anti 表（含线性复合）；和式仍未支持；
        # sin(y) 自 M5.3 起走常被积函数通道（∫c dx = c·x）不再 unsupported
        with self.assertRaises(PolyError, msg="x+sin(x)"):
            self.t("x+sin(x)")
        # x^x：M5.6 变指数幂归一后 = exp(x*log x)，塔可建造，
        # Risch 判定给出更强结论——证明性拒答（非 unsupported）
        with self.assertRaises(RischNonElementary, msg="x^x"):
            self.t("x^x")

    def test_linear_composition(self):
        # 线性复合 f(a x+b)：∫ = anti(a x+b)/a（微分回验）
        res, ok = self.t("sin(2*x)")
        self.assertTrue(ok)
        res, ok = self.t("exp(-x)")
        self.assertTrue(ok)


if __name__ == "__main__":
    unittest.main(verbosity=2)
