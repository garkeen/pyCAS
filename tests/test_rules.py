import unittest

from cas import term as T
from cas.term import S, N, plus, times, pw, neg, sin, cos, log, exp, gt
from cas.context import Context
from cas.decide import decide, T3, eval_guard
from cas.simplify import simplify
from cas.parser import parse
from cas.pprint import to_str
from cas.rules import RuleSet, apply_rule
from cas.loader import parse_rules


x, y = S("x"), S("y")


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


class TestM2Rules(unittest.TestCase):
    """M2.0：规则系统实处化 —— FunctionSpec / 类型洞 / 全式搜索 / 重写日志。"""

    def test_special_point_folding(self):
        # 特殊点构造即折叠（来自 FunctionSpec.special）
        self.assertIs(parse("sin(0)"), T.ZERO)
        self.assertIs(parse("cos(0)"), T.ONE)
        self.assertIs(parse("sin(pi)"), T.ZERO)
        self.assertIs(parse("cos(pi)"), T.MONE)
        self.assertIs(parse("cos(pi/2)"), T.ZERO)
        self.assertIs(parse("exp(0)"), T.ONE)
        self.assertIs(parse("log(1)"), T.ZERO)
        self.assertIs(parse("atan(0)"), T.ZERO)
        # 洞参数不折叠（模式语义保持）
        pat = parse_rules("rule id = sin(?u) -> sin(?u)")[0]
        self.assertIsInstance(pat.pattern, T.Expr)

    def test_diff_via_spec(self):
        from cas.diff import d
        from cas.term import tan

        self.assertIs(d(exp(sin(x)), x), times(exp(sin(x)), cos(x)))
        self.assertIs(d(log(x), x), pw(x, T.MONE))
        self.assertIs(simplify(d(tan(x), x)), plus(N(1), pw(tan(x), N(2))))

    def test_decide_spec_bounds(self):
        ctx = Context()
        self.assertIs(decide(parse("abs(sin(x)) <= 1"), ctx), T3.YES)
        self.assertIs(decide(parse("sin(x) <= 1"), ctx), T3.YES)
        self.assertIs(decide(parse("sin(x) >= -1"), ctx), T3.YES)
        self.assertIs(decide(parse("sin(x) <= 0"), ctx), T3.UNKNOWN)
        self.assertIs(decide(parse("abs(cos(x)) <= 2"), ctx), T3.YES)

    def test_spec_generated_parity_rules(self):
        from cas.session import Session

        s = Session()
        r = s.rules.rules.get("sin_neg")
        self.assertIsNotNone(r)
        self.assertEqual(r.origin, "spec")
        self.assertTrue(r.auto)
        self.assertIsNotNone(s.rules.rules.get("cos_neg"))

    def test_apply_searches_without_path(self):
        from cas.session import Session

        s = Session()
        s.feed("x + sin(-x)")
        res = s.apply("sin_neg")  # 不指定路径，自动搜索
        self.assertIs(res, plus(x, neg(sin(x))))
        self.assertEqual(s.apply("sin2_cos2"), "rule sin2_cos2 does not match anywhere")

    def test_auto_logs_steps(self):
        from cas.session import Session

        s = Session()
        # N4 迁移：log∘exp 收缩已上收构造期（contract.py），解析即 3*x，
        # auto 无重写步可记——本用例改验规则引擎记账通道仍然工作
        # （奇偶性规则：spec origin 自动通道）
        s.feed("exp(log(x)) + 2*exp(log(x))")
        s.auto()
        self.assertEqual(to_str(s.current), "3*x")

        s2 = Session()
        s2.feed("y + sin(-x) + cos(-x)")
        s2.auto()
        rule_ids = [st.rule_id for st in s2.log]
        self.assertGreaterEqual(len(rule_ids), 1)

    def test_auto_rewrites_parity(self):
        from cas.session import Session

        s = Session()
        s.feed("y + sin(-x) + cos(-x)")
        s.auto()
        self.assertEqual(to_str(s.current), "y + cos(x) - sin(x)")

    def test_typed_holes(self):
        rule = parse_rules("rule fnum = f(?x::num) -> g(?x)")[0]
        self.assertEqual(rule.pattern.head.name, "f")
        res = apply_rule(rule, parse("f(2)"), ())
        self.assertEqual(res.guard, "YES")
        self.assertEqual(to_str(res.term), "g(2)")
        res2 = apply_rule(rule, parse("f(y)"), ())
        self.assertEqual(res2.guard, "NOMATCH")
        rule2 = parse_rules("rule fsym = f(?x::sym) -> ?x")[0]
        self.assertEqual(apply_rule(rule2, parse("f(y)"), ()).guard, "YES")
        self.assertEqual(apply_rule(rule2, parse("f(2)"), ()).guard, "NOMATCH")

    def test_rule_priority_dsl(self):
        r = parse_rules("rule pz = sin(?x) -> ?x prio 5")[0]
        self.assertEqual(r.priority, 5)
        r2 = parse_rules("rule pd = cos(?x) -> ?x")[0]
        self.assertEqual(r2.priority, 100)

    def test_pprint_via_spec(self):
        self.assertEqual(to_str(parse("atan(x)")), "atan(x)")
        self.assertEqual(to_str(parse("arcsin(x)")), "arcsin(x)")


if __name__ == "__main__":
    unittest.main(verbosity=2)
