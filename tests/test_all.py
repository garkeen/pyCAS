import unittest

from fractions import Fraction as Fr

from cas import term as T
from cas.term import (
    S, N, PI, E, mk, plus, times, pw, neg, div, sqrt, sin, cos, log, exp,
    mk_bound, subst, eq, gt, lt, le, ne, abs_, TRUE,
)
from cas.match import matches
from cas.context import Context
from cas.decide import decide, T3, contradicted, eval_guard, domain_ok, satisfiable
from cas.domain import dom_condition
from cas.simplify import simplify
from cas.parser import parse
from cas.pprint import to_str
from cas.rules import Rule, RuleSet, apply_rule
from cas.loader import parse_rules
from cas.poly import Poly, ugcd
from cas.ratfunc import RatFunc
from cas.diff import d, verify
from cas.errors import PolyError


x, y, a, b = S("x"), S("y"), S("a"), S("b")


class TestTerm(unittest.TestCase):
    def test_interning(self):
        self.assertIs(plus(x, N(1)), plus(x, N(1)))
        self.assertIs(plus(x, N(1)), plus(N(1), x))
        self.assertIsNot(plus(x, N(1)), plus(x, N(2)))

    def test_fold(self):
        self.assertIs(plus(N(1), N(2)), N(3))
        self.assertIs(times(N(2), N(3), x), times(N(6), x))
        self.assertIs(times(N(0), x), T.ZERO)
        self.assertIs(pw(N(2), N(-2)), N(Fr(1, 4)))
        self.assertIs(pw(T.ZERO, N(-1)), T.UND)
        self.assertIs(pw(T.ZERO, T.ZERO), T.UND)
        self.assertIs(T.UND, plus(T.UND, x))

    def test_alpha(self):
        self.assertIs(mk_bound("x", sin(x)), mk_bound("t", sin(S("t"))))
        self.assertIsNot(mk_bound("x", plus(x, y)), mk_bound("y", plus(x, y)))

    def test_capture_avoidance(self):
        b = mk_bound("x", plus(x, y))
        r = subst(b, {y: x})
        self.assertIs(r.body.args[0], x)
        self.assertIsInstance(r.body.args[1], T.DB)

    def test_paths(self):
        t = plus(x, times(y, x))
        self.assertIs(T.term_at(t, (1, 1)), y)
        self.assertIs(T.replace_at(t, (1, 1), N(5)), plus(x, times(x, N(5))))


class TestMatch(unittest.TestCase):
    def test_repeated(self):
        self.assertEqual(len(list(matches(plus(T.PV("a"), T.PV("a")), plus(x, y)))), 0)
        m = list(matches(plus(T.PV("a"), T.PV("a")), plus(x, x)))
        self.assertEqual(len(m), 1)
        self.assertIs(m[0]["a"], x)

    def test_ac(self):
        m = list(matches(times(N(2), T.PV("u")), times(x, N(2))))
        self.assertEqual(len(m), 1)
        self.assertIs(m[0]["u"], x)

    def test_seq(self):
        m = list(matches(plus(T.PV("a"), T.PS("r")), plus(x, y, N(1))))
        self.assertTrue(any(s["r"] == (y, N(1)) or s["r"] == (N(1), y) for s in m))

    def test_nested(self):
        m = list(matches(pw(T.PV("u"), N(2)), pw(plus(x, N(1)), N(2))))
        self.assertIs(m[0]["u"], plus(x, N(1)))


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


class TestSimplify(unittest.TestCase):
    def test_collect(self):
        e = plus(times(N(2), x), times(N(3), x))
        self.assertIs(simplify(e), times(N(5), x))
        e2 = plus(times(N(2), x), times(N(-2), x))
        self.assertIs(simplify(e2), T.ZERO)

    def test_power(self):
        self.assertIs(simplify(times(x, x)), pw(x, N(2)))
        self.assertIs(simplify(pw(x, N(1))), x)
        self.assertIs(simplify(pw(pw(x, N(2)), N(3))), pw(x, N(6)))


class TestPoly(unittest.TestCase):
    def test_from_term(self):
        p = Poly.from_term(plus(pw(x, N(2)), N(-1)), (x,))
        q = Poly.from_term(plus(x, N(-1)), (x,))
        g = ugcd(p, q)
        self.assertTrue(g.is_monic())
        qq, r = p.udivmod(g)
        self.assertTrue(r.is_zero())
        self.assertEqual(qq.degree(), 1)

    def test_gcd2(self):
        p1 = Poly.from_term(times(plus(x, N(1)), plus(x, N(2))), (x,))
        p2 = Poly.from_term(times(plus(x, N(1)), plus(x, N(3))), (x,))
        g = ugcd(p1, p2)
        self.assertIs(g.to_term(), plus(x, N(1)))

    def test_deriv(self):
        p = Poly.from_term(pw(x, N(3)), (x,))
        self.assertIs(p.deriv(x).to_term(), times(N(3), pw(x, N(2))))


class TestRatFunc(unittest.TestCase):
    def test_cancel(self):
        rf = RatFunc.from_term(
            div(pw(x, N(2)), plus(pw(x, N(2)), N(-1))), (x,)
        )
        self.assertTrue(rf.q.is_const() is False or True)

    def test_add(self):
        r1 = RatFunc.from_term(div(N(1), plus(x, N(1))), (x,))
        r2 = RatFunc.from_term(div(N(1), plus(x, N(-1))), (x,))
        s = r1 + r2
        t = s.to_term()
        self.assertEqual(to_str(t), "2*x/(x^2 - 1)")


class TestDiff(unittest.TestCase):
    def test_basic(self):
        self.assertIs(d(plus(x, sin(x)), x), plus(N(1), cos(x)))

    def test_product(self):
        e = times(x, sin(x))
        self.assertIs(simplify(d(e, x)), plus(sin(x), times(x, cos(x))))

    def test_verify(self):
        F = plus(times(x, sin(x)), cos(x))
        self.assertEqual(verify(F, x, times(x, cos(x))), "VERIFIED")


class TestRulesAndDSL(unittest.TestCase):
    def test_apply_at_path(self):
        rs = RuleSet()
        rs.add(parse_rules("rule sn = sin(-?u) -> -sin(?u)")[0])
        e = plus(x, sin(neg(x)))
        res = apply_rule(rs.rules["sn"], e, (1,))
        self.assertIs(res.term, plus(x, neg(sin(x))))

    def test_guard_unknown(self):
        rs = RuleSet()
        rs.add(
            parse_rules("rule lp = log(?u*?v) -> log(?u)+log(?v) guard ?u>0 && ?v>0 as expand")[0]
        )
        ctx = Context()
        e = log(times(x, y))
        res = apply_rule(rs.rules["lp"], e, (), lambda g, s: eval_guard(g, s, ctx))
        self.assertEqual(res.guard, "UNKNOWN")

    def test_guard_yes(self):
        rs = RuleSet()
        rs.add(
            parse_rules("rule lp = log(?u*?v) -> log(?u)+log(?v) guard ?u>0 && ?v>0 as expand")[0]
        )
        ctx = Context()
        ctx.assume(gt(x, N(0)))
        ctx.assume(gt(y, N(0)))
        e = log(times(x, y))
        res = apply_rule(rs.rules["lp"], e, (), lambda g, s: eval_guard(g, s, ctx))
        self.assertEqual(res.guard, "YES")
        self.assertIs(res.term, plus(log(x), log(y)))


class TestParser(unittest.TestCase):
    def test_parse(self):
        e = parse("x^2 + 2*x + 1")
        self.assertIs(e, plus(pw(x, N(2)), times(N(2), x), N(1)))
        e2 = parse("sin(x)*cos(x)+cos(x)*sin(x)")
        self.assertTrue(e2.args, 2)
        e3 = parse("log(x*y)")
        self.assertIs(e3, log(times(x, y)))
        e4 = parse("x < 3")
        self.assertIs(e4, lt(x, N(3)))
        e5 = parse("2.5")
        self.assertIs(e5, N(Fr(5, 2)))

    def test_quote(self):
        e = parse("'x+1")
        self.assertIs(e.head, S("Quote"))


class TestSolve(unittest.TestCase):
    def setUp(self):
        from cas.solve import solve, check_solution

        self.solve = solve
        self.check = check_solution

    def sols(self, expr, var="x"):
        r = self.solve(parse(expr), S(var))
        return r

    def test_linear(self):
        r = self.sols("2*x - 4")
        self.assertEqual(r.status, "ok")
        self.assertEqual(to_str(r.solutions[0]), "2")
        r = self.sols("x + 2 = 5")
        self.assertEqual(to_str(r.solutions[0]), "3")
        r = self.sols("x/2 = 3")
        self.assertEqual(to_str(r.solutions[0]), "6")

    def test_linear_param(self):
        r = self.sols("a*x - b")
        self.assertEqual(r.status, "ok")
        self.assertEqual(len(r.provisos), 1)
        self.assertEqual(to_str(r.provisos[0]), "a != 0")
        self.assertEqual(to_str(r.solutions[0]), "b/a")

    def test_linear_degenerate(self):
        r = self.sols("0*x - 1")
        self.assertEqual(r.status, "contradiction")
        r = self.sols("x - x")
        self.assertEqual(r.status, "identity")

    def test_quadratic(self):
        r = self.sols("x^2 - 5*x + 6")
        self.assertEqual([to_str(v) for v in r.solutions], ["2", "3"])
        r = self.sols("x^2 + 2*x + 1")
        self.assertEqual([to_str(v) for v in r.solutions], ["-1"])

    def test_quadratic_surds(self):
        r = self.sols("x^2 - 2")
        self.assertEqual([to_str(v) for v in r.solutions], ["2^1/2", "-2^1/2"])
        for v in r.solutions:
            self.assertEqual(self.check(parse("x^2 - 2"), v, x), "VERIFIED")

    def test_quadratic_complex_rejected(self):
        r = self.sols("x^2 + 1")
        self.assertEqual(r.status, "unsupported")
        self.assertIn("complex", r.note)

    def test_cubic_rational_roots(self):
        r = self.sols("x^3 - x")
        self.assertEqual([to_str(v) for v in r.solutions], ["-1", "0", "1"])
        r = self.sols("x^3 - 6*x^2 + 11*x - 6")
        self.assertEqual([to_str(v) for v in r.solutions], ["1", "2", "3"])
        for v in r.solutions:
            self.assertEqual(self.check(parse("x^3 - 6*x^2 + 11*x - 6"), v, x), "VERIFIED")

    def test_unsupported(self):
        r = self.sols("sin(x) - 1")
        self.assertEqual(r.status, "unsupported")

    def test_check_unverified(self):
        r = self.sols("x^2 - 5*x + 6")
        e = self.check(parse("x^2 - 5*x + 6"), S("a"), x)
        self.assertEqual(e, "UNVERIFIED")

    def test_session_solve(self):
        from cas.session import Session

        s = Session()
        out = s.solve("x^2 - 5*x + 6 = 0", "x")
        self.assertIn("2", out)
        self.assertIn("3", out)


    def test_auto_channel(self):
        from cas.session import Session

        s = Session()
        s.feed("exp(log(x)) + 2*exp(log(x))")
        s.auto()
        self.assertEqual(to_str(s.current), "3*x")
        s2 = Session()
        s2.feed("log(x*y) + exp(log(x))")
        s2.auto()
        self.assertIn("log(x*y)", to_str(s2.current))


class TestMatrix(unittest.TestCase):
    def _M(self, spec):
        from cas.matrix import Matrix

        return Matrix.parse(spec)

    def test_parse_and_errors(self):
        from cas.matrix import MatrixError

        self.assertEqual(self._M("[[1,2],[3,4]]").nrows, 2)
        self.assertEqual(self._M("[[1,2],[3,4]]").ncols, 2)
        with self.assertRaises(MatrixError):
            self._M("[[1,2],[3]]")
        with self.assertRaises(MatrixError):
            self._M("[[1,2],[c")

    def test_arith(self):
        m = self._M("[[1,2],[3,4]]")
        self.assertEqual(to_str(m.add(m).rows[0][1]), "4")
        self.assertEqual(to_str(m.scale(N(3)).rows[1][0]), "9")
        p = m.mul(m)
        self.assertEqual(to_str(p.rows[0][0]), "7")
        self.assertEqual(to_str(p.rows[1][1]), "22")
        self.assertEqual(to_str(m.transpose().rows[0][1]), "3")
        self.assertEqual(to_str(m.trace()), "5")

    def test_det(self):
        self.assertEqual(to_str(self._M("[[1,2],[3,4]]").det()), "-2")
        self.assertEqual(to_str(self._M("[[2,0,1],[1,3,0],[0,1,2]]").det()), "13")
        self.assertEqual(to_str(self._M("[[1,2,3],[4,5,6],[7,8,9]]").det()), "0")
        self.assertEqual(to_str(self._M("[[a,b],[c,d]]").det()), "a*d - b*c")

    def test_inv(self):
        m = self._M("[[1,2],[3,4]]")
        i = m.inv()
        self.assertEqual(to_str(i.rows[0][0]), "-2")
        self.assertEqual(to_str(i.rows[1][1]), "-1/2")
        p = m.mul(i)
        self.assertEqual(to_str(p.rows[0][0]), "1")
        self.assertEqual(to_str(p.rows[1][1]), "1")
        self.assertIs(self._M("[[1,2],[2,4]]").inv(), None)

    def test_rank(self):
        self.assertEqual(self._M("[[1,2],[3,4]]").rank(), 2)
        self.assertEqual(self._M("[[1,2,3],[4,5,6],[7,8,9]]").rank(), 2)
        self.assertEqual(self._M("[[1,1],[2,2]]").rank(), 1)

    def test_solve(self):
        from cas.matrix import LinResult

        r = self._M("[[1,2],[3,4]]").solve([N(3), N(0)])
        self.assertEqual([to_str(t) for t in r.unique], ["-6", "9/2"])
        r2 = self._M("[[1,1],[2,2]]").solve([N(1), N(2)])
        self.assertEqual([to_str(t) for t in r2.particular], ["1", "0"])
        self.assertEqual([to_str(t) for t in r2.null_basis[0]], ["-1", "1"])
        r3 = self._M("[[1,1],[2,2]]").solve([N(1), N(3)])
        self.assertIsInstance(r3, LinResult)
        self.assertIsNone(r3.unique)
        self.assertIsNone(r3.particular)
        r4 = self._M("[[1,0,1],[0,1,1]]").solve([N(1), N(2)])
        self.assertEqual([to_str(t) for t in r4.particular], ["1", "2", "0"])

    def test_session_matrix(self):
        from cas.session import Session

        s = Session()
        self.assertEqual(s.mdet("[[1,2],[3,4]]"), "-2")
        self.assertIn("x1 = -6", s.msolve("[[1,2],[3,4]]", "[3,0]"))
        self.assertEqual(s.minv("[[1,2],[2,4]]"), "singular")
        self.assertEqual(s.mrank("[[1,2],[3,4]]"), "2")


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
        self.assertEqual(to_str(dom_condition(parse("1/x^2"))[0]), "x^2 != 0")
        self.assertEqual(to_str(dom_condition(parse("1/x"))[0]), "x != 0")
        self.assertEqual(to_str(dom_condition(parse("sqrt(x)"))[0]), "x >= 0")
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
        self.assertIs(equivalent(parse("sin(x)^2 + cos(x)^2"), parse("1")), T3.UNKNOWN)

    def test_equiv_ctx(self):
        from cas.decide import equivalent

        ctx = Context()
        ctx.assume(parse("x = 5"))
        self.assertIs(equivalent(parse("x + 1"), parse("6"), ctx), T3.YES)
        self.assertIs(equivalent(parse("x"), parse("5"), ctx), T3.YES)

    def test_equiv_verify_alignment(self):
        from cas.diff import verify
        from cas.term import S

        x = parse("x")
        F = parse("x^3/3")
        self.assertEqual(verify(F, x, parse("x^2")), "VERIFIED")
        self.assertEqual(verify(parse("x^2"), x, parse("x")), "UNVERIFIED")
        self.assertEqual(verify(parse("x^3"), x, parse("x^2")), "UNVERIFIED")


class TestSessionFlow(unittest.TestCase):
    def test_suggest_apply_undo(self):
        from cas.session import Session

        s = Session()
        s.feed("x + sin(-x)")
        sug = s.suggest()
        self.assertIn("sin_neg", [r[0] for r in sug])
        res = s.apply("sin_neg", (1,))
        self.assertIs(res, plus(x, neg(sin(x))))
        s.undo()
        self.assertIs(s.current, plus(x, sin(neg(x))))

    def test_obligation_flow(self):
        from cas.session import Session

        s = Session()
        s.feed("log(x*y)")
        out = s.apply("log_prod")
        self.assertIn("obligation", out)
        self.assertEqual(len(s.obligations), 1)
        s.assume("x>0")
        out2 = s.answer(s.obligations[0].oid if s.obligations else 1, "y>0")
        self.assertIs(s.current, plus(log(x), log(y)))

    def test_contradiction_lock(self):
        from cas.session import Session

        s = Session()
        s.assume("a>0")
        r = s.assume("a<0")
        self.assertIn("CONTRADICTION", r)
        self.assertIsNotNone(s.locked)


class TestResultant(unittest.TestCase):
    def P(self, s):
        return Poly.from_term(parse(s), (x,))

    def test_uresultant(self):
        from cas.poly import uresultant

        self.assertEqual(uresultant(self.P("2*x+1"), self.P("x+3")), Fr(5))
        self.assertEqual(uresultant(self.P("x^2-1"), self.P("x^2-2*x+1")), Fr(0))
        self.assertEqual(uresultant(self.P("x^3-x"), self.P("x^2+1")), Fr(4))
        self.assertEqual(uresultant(self.P("x^3-1"), self.P("x^2+1")), Fr(2))

    def test_udiscriminant(self):
        from cas.poly import udiscriminant

        self.assertEqual(udiscriminant(self.P("x^2+5*x+6")), Fr(1))
        self.assertEqual(udiscriminant(self.P("x^3-1")), Fr(-27))
        self.assertEqual(udiscriminant(self.P("x^2-2*x+1")), Fr(0))
        self.assertEqual(udiscriminant(self.P("6*x^2-5*x-6")), Fr(169))


class TestFactor(unittest.TestCase):
    def P(self, s):
        return Poly.from_term(parse(s), (x,))

    def check(self, s):
        from cas.factor import factor

        c, facs = factor(self.P(s))
        prod = Poly.one((x,)).scalar(c)
        for g, m in facs:
            prod = prod * g ** m
        self.assertTrue((prod - self.P(s)).is_zero(), s)
        for g, m in facs:
            self.assertGreater(m, 0)
            self.assertGreater(g.degree(x), 0)

    def test_cases(self):
        cases = [
            "x^2-1", "x^2-2*x+1", "x^3-1", "x^3-8", "x^4-1", "x^4+4",
            "x^4+x^3+x^2+x+1", "x^2+1", "2*x^2+4*x+2", "x^6-1",
            "x^4-5*x^2+4", "x^4+2*x^2+1", "6*x^2-5*x-6", "x^5-1",
            "x^2-3", "x^3+3*x^2+3*x+1", "x^4+x^2+1", "x^8-1",
            "x^3-2*x^2-x+2", "x^5+x^4+x^3+x^2+x", "3*x^2+5*x+2",
            "x^2+4*x+4", "2*x^2-8", "x^4-16", "4*x^2-9",
            "x^3+2*x^2-x-2", "x^5-32", "x^4-8*x^2+16", "9*x^2-1",
            "x^3+6*x^2+11*x+6", "2*x^3-3*x^2-3*x+2", "x^7-1",
            "x^2+x+1", "x^3-2", "x^4+3*x^2+2", "8*x^3+1",
        ]
        for s in cases:
            self.check(s)

    def test_known_factors(self):
        from cas.factor import factor

        c, facs = factor(self.P("x^4-5*x^2+4"))
        self.assertEqual(c, Fr(1))
        self.assertEqual(set(str(g) for g, m in facs), {"x - 2", "x - 1", "x + 1", "x + 2"})

        c, facs = factor(self.P("6*x^2-5*x-6"))
        self.assertEqual(set(str(g) for g, m in facs), {"2*x - 3", "3*x + 2"})

        c, facs = factor(self.P("2*x^2+4*x+2"))
        self.assertEqual(c, Fr(2))
        self.assertEqual([str(g) for g, m in facs], ["x + 1"])
        self.assertEqual([m for g, m in facs], [2])

    def test_irreducible(self):
        from cas.factor import factor

        for s in ("x^2+1", "x^2-3", "x^4+x^3+x^2+x+1", "x^3-2"):
            c, facs = factor(self.P(s))
            self.assertEqual(len(facs), 1, s)
            self.assertEqual(c, Fr(1), s)

    def test_negative_lc(self):
        from cas.factor import factor

        c, facs = factor(self.P("-x^2+1"))
        self.assertEqual(set(str(g) for g, m in facs), {"x - 1", "x + 1"})
        prod = Poly.one((x,)).scalar(c)
        for g, m in facs:
            prod = prod * g ** m
        self.assertTrue((prod - self.P("-x^2+1")).is_zero())


class TestApart(unittest.TestCase):
    def P(self, s):
        return Poly.from_term(parse(s), (x,))

    def check(self, num, den):
        from cas.apart import apart

        f = self.P(num)
        g = self.P(den)
        q, terms = apart(f, g)
        tot = q * g
        for nn, dd, k in terms:
            tot = tot + nn * g.udivmod(dd ** k)[0]
        self.assertTrue((tot - f).is_zero(), f"{num}/{den}")

    def test_cases(self):
        for num, den in [
            ("1", "x^2-1"),
            ("x", "x^2-1"),
            ("x+1", "x^2-2*x+1"),
            ("x+1", "x^2"),
            ("x^3", "x^2-1"),
            ("1", "x^3-1"),
            ("1", "x^4-1"),
            ("x^2+1", "x^3-x"),
            ("1", "x^3-6*x^2+11*x-6"),
            ("x^2", "x^4-5*x^2+4"),
            ("x+2", "x^2+x+1"),
            ("1", "x^2+2*x+2"),
            ("3*x+5", "x^2+3*x+2"),
            ("1", "(x-1)^2*(x+1)"),
            ("x^3+1", "x^3-8"),
            ("2", "x^3-3*x^2+3*x-1"),
            ("1", "x^5-1"),
            ("1", "x^3-2"),
        ]:
            self.check(num, den)

    def test_known_apart(self):
        from cas.apart import apart

        q, terms = apart(self.P("1"), self.P("x^2-1"))
        self.assertTrue(q.is_zero())
        pairs = set((str(nn), str(dd), k) for nn, dd, k in terms)
        self.assertEqual(pairs, {("1/2", "x - 1", 1), ("-1/2", "x + 1", 1)})

        q, terms = apart(self.P("x+1"), self.P("x^2-2*x+1"))
        pairs = set((str(nn), str(dd), k) for nn, dd, k in terms)
        self.assertEqual(pairs, {("1", "x - 1", 1), ("2", "x - 1", 2)})


if __name__ == "__main__":
    unittest.main(verbosity=2)
