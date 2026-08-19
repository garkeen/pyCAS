import unittest

from fractions import Fraction as Fr

from cas import term as T
from cas.term import S, N, PI, plus, times, pw, neg, gt, lt, le, ne, eq, abs_
from cas.context import Context
from cas.decide import decide, T3, contradicted, domain_ok, satisfiable
from cas.domain import dom_condition
from cas.parser import parse
from cas.pprint import to_str


x, y, a, b = S("x"), S("y"), S("a"), S("b")


class TestDecide(unittest.TestCase):
    def test_numeric(self):
        ctx = Context()
        self.assertIs(decide(lt(N(1), N(2)), ctx), T3.YES)
        self.assertIs(decide(eq(N(1), N(2)), ctx), T3.NO)

    def test_axioms(self):
        ctx = Context()
        self.assertIs(decide(gt(PI, N(0)), ctx), T3.YES)
        self.assertIs(decide(lt(pw(x, N(2)), N(0)), ctx), T3.NO)

    def test_ledger(self):
        ctx = Context()
        ctx.assume(gt(a, N(0)))
        self.assertIs(decide(gt(a, N(0)), ctx), T3.YES)
        self.assertTrue(contradicted(lt(a, N(0)), ctx))

    def test_chain(self):
        ctx = Context()
        ctx.assume(lt(a, b))
        ctx.assume(lt(b, x))
        self.assertIs(decide(lt(a, x), ctx), T3.YES)

    def test_poly_eq(self):
        ctx = Context()
        e1 = plus(pw(plus(x, N(1)), N(2)), neg(pw(x, N(2))))
        self.assertIs(decide(eq(e1, plus(times(N(2), x), N(1))), ctx), T3.YES)

    def test_derive_rules(self):
        ctx = Context()
        self.assertIs(decide(le(pw(x, N(2)), N(0)), ctx), T3.UNKNOWN)
        self.assertIs(decide(le(N(0), pw(x, N(2))), ctx), T3.YES)
        self.assertIs(decide(lt(pw(x, N(2)), N(0)), ctx), T3.NO)
        self.assertIs(decide(gt(pw(x, N(2)), N(0)), ctx), T3.UNKNOWN)
        ctx2 = Context()
        ctx2.assume(gt(x, N(0)))
        self.assertIs(decide(gt(pw(x, N(2)), N(0)), ctx2), T3.YES)
        self.assertIs(decide(ne(x, N(0)), ctx2), T3.YES)
        self.assertIs(decide(gt(times(x, y), N(0)), ctx2), T3.UNKNOWN)
        ctx3 = Context()
        ctx3.assume(gt(x, N(0)))
        ctx3.assume(lt(y, N(0)))
        self.assertIs(decide(gt(times(x, y), N(0)), ctx3), T3.NO)
        self.assertIs(decide(lt(times(x, y), N(0)), ctx3), T3.YES)
        ctx4 = Context()
        ctx4.assume(gt(a, N(0)))
        ctx4.assume(gt(b, N(0)))
        self.assertIs(decide(gt(plus(a, b), N(0)), ctx4), T3.YES)
        ctx5 = Context()
        ctx5.assume(eq(x, N(0)))
        self.assertIs(decide(eq(times(x, y), N(0)), ctx5), T3.YES)
        self.assertIs(decide(gt(plus(x, y), N(0)), ctx5), T3.UNKNOWN)

    def test_domain(self):
        from cas.domain import R, Q, Z

        self.assertIs(R.nonneg(N(2)), True)
        self.assertIs(R.nonneg(N(-2)), False)
        self.assertIs(R.pos(PI), True)
        self.assertIs(R.nonneg(pw(x, N(2))), True)
        self.assertIs(R.nonneg(abs_(x)), True)
        self.assertIs(Q.contains(N(2)), True)
        self.assertIs(Q.contains(N(Fr(1, 2))), True)
        self.assertIs(Z.contains(N(2)), True)
        self.assertIs(Z.contains(N(Fr(1, 2))), None)


class TestDomain(unittest.TestCase):
    def test_unary_minus_binds_looser_than_power(self):
        t = parse("-x^2")
        self.assertIsInstance(t, T.Expr)
        self.assertEqual(t.head.name, "Times")
        self.assertEqual(to_str(t), "-x^2")
        self.assertEqual(to_str(parse("-2^2")), "-4")
        self.assertEqual(to_str(parse("1 - x^2")), "-x^2 + 1")

    def test_dom_condition(self):
        self.assertEqual(len(dom_condition(parse("ln(-x^2)"))), 1)
        self.assertEqual(to_str(dom_condition(parse("ln(-x^2)"))[0]), "-x^2 > 0")
        cons = dom_condition(parse("ln(ln(x))"))
        self.assertEqual(len(cons), 2)
        self.assertIn(to_str(parse("ln(x) > 0")), [to_str(c) for c in cons])
        self.assertIn("x > 0", [to_str(c) for c in cons])
        self.assertEqual(to_str(dom_condition(parse("1/x^2"))[0]), "x != 0")
        self.assertEqual(to_str(dom_condition(parse("1/x"))[0]), "x != 0")
        self.assertEqual(to_str(dom_condition(parse("sqrt(x)"))[0]), "x >= 0")
        self.assertEqual(to_str(dom_condition(parse("x^(-1/2)"))[0]), "x > 0")
        self.assertEqual(to_str(dom_condition(parse("x^(-1/3)"))[0]), "x != 0")
        self.assertEqual(dom_condition(parse("x + 1")), [])

    def test_domain_ok(self):
        self.assertIs(domain_ok(parse("ln(-x^2) != 0"), Context()), T3.NO)
        self.assertIs(domain_ok(parse("cos(x) != 0"), Context()), T3.YES)
        self.assertIs(domain_ok(parse("ln(2*x)"), Context()), T3.UNKNOWN)
        ctx = Context()
        ctx.assume(parse("x = -1"))
        self.assertIs(domain_ok(parse("sqrt(x) > 0"), ctx), T3.NO)
        ctx2 = Context()
        ctx2.assume(parse("x = 0"))
        self.assertIs(domain_ok(parse("1/x > 0"), ctx2), T3.NO)
        self.assertIs(domain_ok(parse("cos(x) != 0"), ctx2), T3.YES)

    def test_satisfiable(self):
        self.assertIs(satisfiable([], Context()), T3.YES)
        self.assertIs(satisfiable([parse("x > 0")], Context()), T3.UNKNOWN)
        self.assertIs(
            satisfiable([parse("x > 0"), parse("x < 0")], Context()), T3.NO
        )

    def test_assume_domain_gate(self):
        from cas.session import Session

        s = Session()
        self.assertIn("domain empty", s.assume("ln(-x^2) != 0"))
        self.assertIn("assumed", s.assume("cos(x) != 0"))
        s2 = Session()
        s2.assume("x = 0")
        self.assertIn("domain empty", s2.assume("1/x > 0"))

    def test_sign_precision(self):
        ctx = Context()
        self.assertIs(decide(parse("-x^2 > 0"), ctx), T3.NO)
        self.assertIs(decide(parse("-x^2 <= 0"), ctx), T3.YES)
        self.assertIs(decide(parse("-x^2 >= 0"), ctx), T3.UNKNOWN)
        self.assertIs(decide(parse("x^2 <= 0"), ctx), T3.UNKNOWN)
        ctx2 = Context()
        ctx2.assume(parse("x = 5"))
        self.assertIs(decide(parse("x < 3"), ctx2), T3.NO)
        ctx3 = Context()
        ctx3.assume(parse("x = 0"))
        self.assertIs(decide(parse("x > 0"), ctx3), T3.NO)


class TestContext(unittest.TestCase):
    def test_clone_independent(self):
        c = Context()
        c.assume(parse("x > 0"))
        d = c.clone()
        d.assume(parse("x < 5"))
        self.assertEqual(len(c.entries), 1)
        self.assertEqual(len(d.entries), 2)
        self.assertIs(decide(parse("x < 5"), c), T3.UNKNOWN)
        self.assertIs(decide(parse("x < 5"), d), T3.YES)

    def test_check_and_assume(self):
        c = Context()
        c.assume(parse("x > 0"))
        st, why = c.check_and_assume(parse("x > 10"))
        self.assertIs(st, T3.YES)
        self.assertIsNone(why)
        st, why = c.check_and_assume(parse("x < 0"))
        self.assertIs(st, T3.NO)
        self.assertEqual(why, "contradiction")
        st, why = c.check_and_assume(parse("ln(-x^2) != 0"))
        self.assertIs(st, T3.NO)
        self.assertEqual(why, "domain")
        self.assertEqual(len(c.entries), 2)

    def test_branch(self):
        c = Context()
        c.assume(parse("x > 0"))
        bs = c.branch(parse("x > 100"), parse("x < -5"), parse("x = 5"))
        self.assertEqual([b.status for b in bs], ["open", "empty", "open"])
        self.assertIs(decide(parse("x > 100"), bs[0].ctx), T3.YES)
        self.assertEqual(len(c.entries), 1)

    def test_num_bound_channel(self):
        c = Context()
        c.assume(parse("x > 0"))
        self.assertIs(decide(parse("x >= -5"), c), T3.YES)
        self.assertIs(decide(parse("x != -1"), c), T3.YES)
        self.assertIs(decide(parse("x < 5"), c), T3.UNKNOWN)
        c2 = Context()
        c2.assume(parse("x > 100"))
        self.assertIs(decide(parse("x < 10"), c2), T3.NO)
        self.assertIs(decide(parse("x > 50"), c2), T3.YES)
        c3 = Context()
        c3.assume(parse("x < 3"))
        self.assertIs(decide(parse("x < 5"), c3), T3.YES)
        self.assertIs(decide(parse("x > 10"), c3), T3.NO)

    def test_answer_gate(self):
        from cas.session import Session

        s = Session()
        s.assume("y < 10")
        s.feed("log(x*y)")
        s.apply("log_prod")
        self.assertIn("answer rejected", s.answer(1, "y > 100"))
        self.assertIn("assumed", s.assume("x > 0"))
        self.assertIn("answered", s.answer(1, "y > 0"))
        self.assertEqual(to_str(s.current), "log(x) + log(y)")

    def test_commit_guard_gate(self):
        from cas.session import Session

        s = Session()
        s.assume("x = 5")
        s.feed("log(x^2) + log(y)")
        s.apply("log_prod", (0,))
        self.assertIsNone(s.locked)


class TestEquivalent(unittest.TestCase):
    def test_equiv_basic(self):
        from cas.decide import equivalent

        self.assertIs(equivalent(parse("x"), parse("x")), T3.YES)
        self.assertIs(equivalent(parse("x + x"), parse("2*x")), T3.YES)
        self.assertIs(equivalent(parse("2"), parse("3")), T3.NO)
        self.assertIs(equivalent(parse("x^2"), parse("x")), T3.UNKNOWN)
        self.assertIs(equivalent(parse("1/x"), parse("x^-1")), T3.YES)
        # 三角层决策过程（多角度基归零）：M2.0 接线后为符号 YES
        self.assertIs(equivalent(parse("sin(x)^2 + cos(x)^2"), parse("1")), T3.YES)

    def test_equiv_ctx(self):
        from cas.decide import equivalent

        ctx = Context()
        ctx.assume(parse("x = 5"))
        self.assertIs(equivalent(parse("x + 1"), parse("6"), ctx), T3.YES)
        self.assertIs(equivalent(parse("x"), parse("5"), ctx), T3.YES)

    def test_equiv_verify_alignment(self):
        from cas.diff import verify

        xv = parse("x")
        F = parse("x^3/3")
        self.assertEqual(verify(F, xv, parse("x^2")), "VERIFIED")
        self.assertEqual(verify(parse("x^2"), xv, parse("x")), "UNVERIFIED")
        self.assertEqual(verify(parse("x^3"), xv, parse("x^2")), "UNVERIFIED")


class TestDecideRegressions(unittest.TestCase):
    """区间传播通道与等式代入回归。"""

    def test_decide_interval(self):
        ctx = Context()
        ctx.assume(parse("x > 2"))
        self.assertIs(decide(parse("x + 1 > 3"), ctx), T3.YES)
        self.assertIs(decide(parse("x + 1 > 5"), ctx), T3.UNKNOWN)
        self.assertIs(decide(parse("2*x > 4"), ctx), T3.YES)
        self.assertIs(decide(parse("x - 3 < 0"), ctx), T3.UNKNOWN)
        ctx2 = Context()
        ctx2.assume(parse("x == y"))
        ctx2.assume(parse("y < 3"))
        self.assertIs(decide(parse("x < 3"), ctx2), T3.YES)
        ctx3 = Context()
        ctx3.assume(parse("x > 0"))
        self.assertIs(decide(parse("x + 5 >= 5"), ctx3), T3.YES)

    def test_decide_eq_not_confused_with_lt(self):
        ctx = Context()
        ctx.assume(parse("x = 5"))
        self.assertIs(decide(parse("x < 5"), ctx), T3.NO)
        self.assertIs(decide(parse("x <= 5"), ctx), T3.YES)
        self.assertIs(decide(parse("x != 5"), ctx), T3.NO)
        self.assertIs(decide(parse("x + 1 > 6"), ctx), T3.NO)
        self.assertIs(decide(parse("x + 1 > 5"), ctx), T3.YES)


if __name__ == "__main__":
    unittest.main(verbosity=2)
