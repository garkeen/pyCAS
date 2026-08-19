"""差分测试：sympy 仅作测试预言机（oracle）。

运行时零依赖（cas 包从不 import sympy）；仅测试期用 sympy 独立复核地基算法。
未安装 sympy 时自动跳过。
"""

import random
import unittest
from fractions import Fraction as Fr

from cas.term import S, N, plus, times
from cas.parser import parse
from cas.pprint import to_str

try:
    import sympy

    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False


x, y = S("x"), S("y")


def _sy(s):
    return sympy.sympify(s.replace("^", "**"))


@unittest.skipUnless(HAS_SYMPY, "sympy not installed")
class TestRingEvalOracle(unittest.TestCase):
    """环层求值与化简保语义：对照 sympy 精确有理计算。"""

    def _rand_expr(self, rng, depth):
        if depth == 0 or rng.random() < 0.3:
            if rng.random() < 0.5:
                return N(Fr(rng.randint(-5, 5), rng.randint(1, 4)))
            return rng.choice([x, y])
        a = self._rand_expr(rng, depth - 1)
        b = self._rand_expr(rng, depth - 1)
        return plus(a, b) if rng.random() < 0.5 else times(a, b)

    def test_eval_exact_matches_sympy(self):
        from cas.evalnum import eval_exact

        sx, sy = sympy.Symbol("x"), sympy.Symbol("y")
        rng = random.Random(7)
        for _ in range(30):
            e = self._rand_expr(rng, 3)
            ex = Fr(rng.randint(1, 5), rng.randint(1, 3))
            ey = Fr(rng.randint(-4, 4), rng.randint(1, 3))
            ours = eval_exact(e, {x: ex, y: ey})
            expr_sym = _sy(to_str(e)).subs(
                {sx: sympy.Rational(ex.numerator, ex.denominator),
                 sy: sympy.Rational(ey.numerator, ey.denominator)}
            )
            theirs = sympy.together(expr_sym)
            self.assertEqual(ours, Fr(theirs.p, theirs.q))

    def test_simplify_preserves_value(self):
        from cas.simplify import simplify
        from cas.evalnum import eval_exact

        rng = random.Random(11)
        env = {x: Fr(2, 3), y: Fr(-1, 4)}
        for _ in range(20):
            e = self._rand_expr(rng, 3)
            self.assertEqual(eval_exact(simplify(e), env), eval_exact(e, env))


@unittest.skipUnless(HAS_SYMPY, "sympy not installed")
class TestIntegrateOracle(unittest.TestCase):
    """积分结果对照 sympy 微分（独立于内部 verify 通道）。"""

    CASES = [
        "1/(x^2-1)", "x^2/(x-1)", "1/(x-1)^3", "x^3/(x^2-1)",
        "(2*x+1)/(x^2+x+1)", "1/(x^2+x+1)",
    ]

    def test_derivative_matches_sympy(self):
        from cas.integrate import integrate

        sx = sympy.Symbol("x")
        for s in self.CASES:
            res, ok, _method = integrate(parse(s), x)
            self.assertTrue(ok, s)
            fs = to_str(res)
            if "rootof" in fs:
                continue  # RootOf 输出 sympy 无对应语法，内部 verify 已覆盖
            F = _sy(fs)
            f = _sy(s)
            self.assertEqual(sympy.simplify(sympy.diff(F, sx) - f), 0, s)


@unittest.skipUnless(HAS_SYMPY, "sympy not installed")
class TestFactorOracle(unittest.TestCase):
    """因式分解对照 sympy.factor_list（系数、因子集、重数）。"""

    CASES = [
        "x^4-5*x^2+4", "x^6-1", "6*x^2-5*x-6", "x^3-2", "x^4+4",
        "2*x^2+4*x+2", "-x^2+1", "2*x^3-3*x^2-3*x+2",
    ]

    def test_factorization_matches_sympy(self):
        from cas.factor import factor
        from cas.poly import Poly

        sx = sympy.Symbol("x")
        for s in self.CASES:
            c, facs = factor(Poly.from_term(parse(s), (x,)))
            coeff_sym, flist = sympy.factor_list(_sy(s), sx)
            self.assertEqual(
                Fr(c.numerator, c.denominator),
                Fr(int(coeff_sym.p), int(coeff_sym.q)),
                s,
            )
            self.assertEqual(len(flist), len(facs), s)
            for f_sym, m in flist:
                hit = [
                    m == om and sympy.simplify(f_sym - _sy(str(g))) == 0
                    for g, om in facs
                ]
                self.assertTrue(any(hit), s)


@unittest.skipUnless(HAS_SYMPY, "sympy not installed")
class TestMgcdOracle(unittest.TestCase):
    """多元 gcd 对照 sympy（相伴意义下相等）。"""

    def test_random(self):
        sx, sy = sympy.symbols("x y")
        rng = random.Random(5)
        faclist = ["x+y", "x-y", "x+1", "y+2", "x^2+y", "x*y+1", "x^2-y^2"]
        for _ in range(20):
            g_s = sympy.sympify(rng.choice(faclist).replace("^", "**")) ** rng.randint(1, 2)
            p_s = sympy.expand(g_s * sympy.expand(sympy.sympify(rng.choice(faclist).replace("^", "**"))))
            q_s = sympy.expand(g_s * sympy.expand(sympy.sympify(rng.choice(faclist).replace("^", "**"))))
            from cas.poly import Poly, mgcd

            g = mgcd(
                Poly.from_term(parse(str(p_s).replace("**", "^")), (x, y)),
                Poly.from_term(parse(str(q_s).replace("**", "^")), (x, y)),
            )
            ours = sympy.sympify(to_str(g.to_term()).replace("^", "**"))
            gs = sympy.gcd(p_s, q_s)
            self.assertTrue(
                sympy.cancel(ours / gs).is_polynomial(sx, sy)
                and sympy.cancel(gs / ours).is_polynomial(sx, sy),
                f"{p_s} vs {q_s}: {ours} vs {gs}",
            )


@unittest.skipUnless(HAS_SYMPY, "sympy not installed")
class TestParamSolveOracle(unittest.TestCase):
    """参数化二次方程：随机代入参数后，根与 sympy.solve 一致。"""

    def test_random_assignments(self):
        from cas.solve import solve
        from cas.evalnum import eval_approx
        from cas.term import S as _S

        rng = random.Random(9)
        sa, sb, sc = sympy.symbols("a b c")
        sx = sympy.Symbol("x")
        checked = 0
        while checked < 8:
            va = Fr(rng.randint(1, 5), rng.randint(1, 3))
            vb = Fr(rng.randint(-6, 6), 1)
            vc = Fr(rng.randint(-6, 6), 1)
            if vb * vb - 4 * va * vc <= 0:
                continue  # 只要判别式正的情形（两不同实根）
            checked += 1
            r = solve(parse("a*x^2 + b*x + c"), _S("x"))
            self.assertEqual(r.status, "ok")
            env = {_S("a"): va, _S("b"): vb, _S("c"): vc}
            ours = sorted(round(eval_approx(s, env), 9) for s in r.solutions)
            theirs = sorted(
                round(complex(v.subs({sa: sympy.Rational(va.numerator, va.denominator),
                                       sb: sympy.Rational(vb.numerator, vb.denominator),
                                       sc: sympy.Rational(vc.numerator, vc.denominator)})).real, 9)
                for v in sympy.solve(sa * sx ** 2 + sb * sx + sc, sx)
            )
            self.assertEqual(len(ours), len(theirs))
            for o, t in zip(ours, theirs):
                self.assertAlmostEqual(o, t, places=7)


if __name__ == "__main__":
    unittest.main(verbosity=2)
