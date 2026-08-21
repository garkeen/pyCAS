"""Gröbner 基与方程组求解测试。

单元：单项式序 / 多变元除法 / Buchberger / reduced basis 唯一性。
端到端：solve_system 各状态（ok/contradiction/positive-dim/partial）+ !gsolve。
差分：reduced Gröbner 基对照 sympy（未安装自动跳过）。
"""

import unittest

from cas.term import S
from cas.parser import parse
from cas.pprint import to_str
from cas.simplify import simplify, expand
import cas.term as T

try:
    import sympy

    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False

x, y, z = S("x"), S("y"), S("z")


def _poly(s, vs=(x, y, z)):
    from cas.poly import Poly

    return Poly.from_term(simplify(expand(parse(s))), vs)


def _sys(*eqs):
    return [_poly(e) for e in eqs]


def _term(s):
    return simplify(expand(parse(s)))


class TestGroebnerCore(unittest.TestCase):
    def test_reduce_zero(self):
        from cas.groebner import _reduce, lex_key

        # f = x*(xy-1) + y*(y^2-1) 属于理想 -> 对 G 归约必为零
        f = _poly("x^2*y - x + y^3 - y")
        G = [_poly("x*y - 1"), _poly("y^2 - 1")]
        r = _reduce(f, G, lex_key)
        self.assertTrue(r.is_zero())

    def test_groebner_circle_line(self):
        from cas.groebner import groebner, reduced_basis

        G = reduced_basis(groebner(_sys("x^2+y^2-1", "x+y-1"), "lex"), "lex")
        strs = sorted(to_str(g.to_term()) for g in G)
        self.assertEqual(strs, ["x + y - 1", "y^2 - y"])

    def test_reduced_basis_unique(self):
        # 同理想、不同输入顺序 -> 同一 reduced 基（固定序下唯一）
        from cas.groebner import groebner, reduced_basis

        G1 = reduced_basis(groebner(_sys("x^2+y^2-1", "x+y-1"), "lex"), "lex")
        G2 = reduced_basis(groebner(_sys("x+y-1", "(x+y-1)*(x-3)", "x^2+y^2-1"), "lex"), "lex")
        s1 = sorted(to_str(g.to_term()) for g in G1)
        s2 = sorted(to_str(g.to_term()) for g in G2)
        self.assertEqual(s1, s2)

    def test_contradiction_one_in_ideal(self):
        from cas.groebner import groebner

        G = groebner(_sys("x-1", "x-2"), "grevlex")
        self.assertTrue(any(g.is_const() and not g.is_zero() for g in G))

    def test_budget_guard(self):
        # 护栏存在（不触发即可）：cyclic-n 小规模正常完成
        from cas.groebner import groebner

        G = groebner(_sys("x^2-y-1", "y^2-x-1"), "grevlex")
        self.assertTrue(G)


@unittest.skipUnless(HAS_SYMPY, "sympy not installed")
class TestGroebnerOracle(unittest.TestCase):
    """reduced Groebner 基对照 sympy（同序同基）。"""

    def _match(self, fs_str, vs, order):
        from cas.groebner import groebner, reduced_basis

        polys = _sys(*fs_str)
        G = reduced_basis(groebner(polys, order), order)
        ours = set()
        for g in G:
            ours.add(to_str(g.to_term()))
        sym_vs = [sympy.Symbol(v.name) for v in vs]
        sym_fs = [sympy.sympify(f.replace("^", "**")) for f in fs_str]
        key = "lex" if order == "lex" else "grevlex"
        S_G = sympy.groebner(sym_fs, *sym_vs, order=key)
        theirs = set()
        for g in S_G:
            # sympy str 输出 ** 幂符号 -> pyCAS ^ 语法
            theirs.add(to_str(simplify(expand(parse(str(g).replace("**", "^"))))))
        self.assertEqual(ours, theirs)

    def test_lex_basis(self):
        self._match(["x^2+y^2-1", "x+y-1"], (x, y), "lex")

    def test_grevlex_basis(self):
        self._match(["x^2*y-y*x^2+x*y-y^2", "x^2-y^2"], (x, y), "grevlex")

    def test_three_var_basis(self):
        self._match(["x+y+z-3", "x^2+y^2+z^2-3", "x*y+x*z+y*z-3"], (x, y, z), "lex")


class TestSolveSystem(unittest.TestCase):
    def test_zero_dim_ok(self):
        from cas.groebner import solve_system

        r = solve_system([_term("x^2+y^2-1"), _term("x+y-1")], (x, y))
        self.assertEqual(r.status, "ok")
        sols = {tuple(to_str(t) for t in sol) for sol in r.solutions}
        self.assertEqual(sols, {("1", "0"), ("0", "1")})

    def test_three_var_permutations(self):
        from cas.groebner import solve_system

        r = solve_system(
            [_term("x+y+z-6"), _term("x*y+y*z+x*z-11"), _term("x*y*z-6")], (x, y, z)
        )
        self.assertEqual(r.status, "ok")
        self.assertEqual(len(r.solutions), 6)   # (1,2,3) 的全部排列
        for sol in r.solutions:
            vals = sorted(T.num_val(t) for t in sol)
            self.assertEqual(vals, [1, 2, 3])

    def test_contradiction(self):
        from cas.groebner import solve_system

        r = solve_system([_term("x-1"), _term("x-2")], (x, y))
        self.assertEqual(r.status, "contradiction")

    def test_positive_dim(self):
        from cas.groebner import solve_system

        r = solve_system([_term("x-y")], (x, y))
        self.assertEqual(r.status, "positive-dim")
        # 三变量两独立方程同样是 1 维曲线
        r2 = solve_system([_term("x+y+z-6"), _term("x*y+y*z+x*z-11")], (x, y, z))
        self.assertEqual(r2.status, "positive-dim")

    def test_partial_nonrational_truncation(self):
        from cas.groebner import solve_system

        # 回代遇 RootOf 解：Q 系数域无法继续，诚实截断
        r = solve_system([_term("x^3+x+1"), _term("y-x^2")], (x, y))
        self.assertEqual(r.status, "partial")
        self.assertIn("non-rational root", r.note)

    def test_not_polynomial(self):
        from cas.groebner import solve_system

        r = solve_system([parse("sin(x)-1"), parse("y-x")], (x, y))
        self.assertEqual(r.status, "unsupported")

    def test_eq_form_input(self):
        # Eq 形态入口归一（f = g -> f - g）
        from cas.groebner import solve_system

        r = solve_system([parse("x^2 == 4"), parse("y == x - 1")], (x, y))
        self.assertEqual(r.status, "ok")
        sols = {tuple(to_str(t) for t in sol) for sol in r.solutions}
        self.assertEqual(sols, {("2", "1"), ("-2", "-3")})


class TestGsolveCommand(unittest.TestCase):
    def setUp(self):
        from cas.session import Session

        self.s = Session()

    def test_end_to_end(self):
        out = self.s.handle("!gsolve x^2+y^2==1 && x+y==1 for x,y")
        self.assertIn("(1, 0)", out)
        self.assertIn("(0, 1)", out)
        self.assertIn("[VERIFIED]", out)

    def test_usage_errors(self):
        self.assertIn("usage", self.s.handle("!gsolve x==1"))
        # 单方程单变量 = 一元求解退化情形，正常工作
        out = self.s.handle("!gsolve x^2==4 for x")
        self.assertIn("2", out)
        self.assertIn("VERIFIED", out)

    def test_contradiction_output(self):
        out = self.s.handle("!gsolve x==1 && x==2 for x,y")
        self.assertIn("contradiction", out)

    def test_positive_dim_output(self):
        out = self.s.handle("!gsolve x==y for x,y")
        self.assertIn("positive-dimensional", out)


if __name__ == "__main__":
    unittest.main()
