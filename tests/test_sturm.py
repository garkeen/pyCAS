import unittest

from fractions import Fraction as Fr

from cas.term import S
from cas.parser import parse
from cas.poly import Poly
from cas.sturm import real_root_count, isolate_real_roots, squarefree_part, _eval_at


try:
    import sympy

    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False


x = S("x")


def P(s):
    return Poly.from_term(parse(s), (x,))


class TestSturmCount(unittest.TestCase):
    def test_counts(self):
        self.assertEqual(real_root_count(P("x^2-1"), Fr(-5), Fr(5)), 2)
        self.assertEqual(real_root_count(P("x^2+1"), Fr(-5), Fr(5)), 0)
        self.assertEqual(real_root_count(P("x^3-x"), Fr(-5), Fr(5)), 3)
        # 重根不计（不同实根个数）
        self.assertEqual(real_root_count(P("(x-1)^2"), Fr(-5), Fr(5)), 1)
        # 子区间
        self.assertEqual(real_root_count(P("x^2-1"), Fr(0), Fr(5)), 1)

    def test_squarefree_part(self):
        sq = squarefree_part(P("(x-1)^2*(x+1)"))
        self.assertEqual(sq.degree(x), 2)


class TestIsolation(unittest.TestCase):
    def check_isolation(self, s, expect_n):
        p = P(s)
        ivs = isolate_real_roots(p)
        self.assertEqual(len(ivs), expect_n, s)
        sq = squarefree_part(p)
        prev_hi = None
        for lo, hi in ivs:
            self.assertLess(lo, hi, s)
            if prev_hi is not None:
                self.assertLessEqual(prev_hi, lo, s)
            # 端点处符号变化（根在闭区间内）
            self.assertLessEqual(_eval_at(sq, x, lo) * _eval_at(sq, x, hi), 0, s)
            prev_hi = hi
        return ivs

    def test_cases(self):
        self.check_isolation("x^2-2", 2)
        self.check_isolation("x^3-2", 1)
        self.check_isolation("x^3-x", 3)
        self.check_isolation("x^2+1", 0)
        self.check_isolation("x^4-5*x^2+4", 4)

    def test_rootof_real_isolation(self):
        from cas.algnum import real_isolation

        self.assertEqual(real_isolation(P("x^2+1")), [])
        ivs = real_isolation(P("x^3-2"))
        self.assertEqual(len(ivs), 1)
        lo, hi = ivs[0]
        # ³√2 ∈ (1, 2)
        self.assertLessEqual(lo, Fr(3, 2))
        self.assertGreaterEqual(hi, Fr(5, 4))


@unittest.skipUnless(HAS_SYMPY, "sympy not installed")
class TestIsolationOracle(unittest.TestCase):
    """对照 sympy 实根个数与位置。"""

    def test_matches_sympy(self):
        for s in ("x^3-x", "x^4-5*x^2+4", "x^3-2", "x^2+1", "x^5-x-1"):
            ivs = isolate_real_roots(P(s))
            poly_sym = sympy.Poly(sympy.sympify(s.replace("^", "**")), sympy.Symbol("x"))
            roots = sympy.nroots(poly_sym)
            nreal = sum(1 for r in roots if abs(r.as_real_imag()[1]) < 1e-10)
            self.assertEqual(len(ivs), nreal, s)
            for r in roots:
                if abs(r.as_real_imag()[1]) < 1e-10:
                    re_r = float(r.as_real_imag()[0])
                    hits = [1 for lo, hi in ivs if float(lo) - 1e-9 <= re_r <= float(hi) + 1e-9]
                    # 恰在相邻隔离区间共享端点上的精确根可命中两次（半开区间约定）
                    self.assertGreaterEqual(sum(hits), 1, f"{s}: root {r}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
