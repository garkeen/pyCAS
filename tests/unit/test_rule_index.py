# -*- coding: utf-8 -*-
"""The rule-set root-key index: candidate narrowing is a pure filter.

The index narrows the rules tried at a path to those whose pattern can match
there. These tests pin that the narrowed selection equals a full scan over a
representative rule set, that index maintenance on add/remove stays consistent,
and that autosimplify's narrowed run reaches the same normal form as a
full-scan reference loop.
"""

from cas.math.loader import parse_rule_line
from cas.math.rules import RuleSet, apply_rule
from cas.math.simplify import autosimplify, cost, rebuild
from cas.syntax import term as T
from cas.syntax.match import matches
from cas.syntax.parse import parse

_LINES = (
    "rule h = ?x -> ?x auto",              # hole root: matches any term
    "rule p = Plus(?a, ?b) -> ?a auto",     # identity head: matches any root
    "rule t = Times(?a, ?b) -> ?a auto",    # identity head: matches any root
    "rule f = f(?x) -> ?x auto",            # head f only
    "rule g = g(?x, ?y) -> ?x auto",        # head g only
    "rule lit = 0 -> 0 auto",               # literal root
)

_TERMS = ("f(x)", "x + 1", "x", "0", "h(x)", "f(f(x))", "x*f(x)",
          "g(x, y)", "x + f(x)", "k(x)")


def _ctx():
    from cas.runtime import get_runtime
    return get_runtime().math


def _ruleset():
    rs = RuleSet()
    for line in _LINES:
        rs.add(parse_rule_line(line))
    return rs


def _matchable(rule, tgt):
    # a substitution dict may be empty (a literal-only match), so matchability
    # is "the generator yielded something", never the truthiness of a binding.
    return bool(list(matches(rule.pattern, tgt)))


def test_candidates_equal_a_full_scan_for_every_term_and_path():
    rs = _ruleset()
    for src in _TERMS:
        t = parse(src)
        for path in T.all_paths(t):
            sub = T.term_at(t, path)
            full = [r.id for r in rs.rules.values() if _matchable(r, sub)]
            narrow = [r.id for r in rs.candidates(sub)]
            assert narrow == full, (src, path, full, narrow)


def test_candidates_preserve_insertion_order_across_the_two_buckets():
    """A universal rule added first stays first among equal priorities."""
    rs = RuleSet()
    rs.add(parse_rule_line("rule u = Plus(?a, ?b) -> ?a auto"))
    rs.add(parse_rule_line("rule s = f(?x) -> ?x auto"))
    assert [r.id for r in rs.candidates(parse("f(x)"))] == ["u", "s"]


def test_index_follows_add_and_remove():
    rs = _ruleset()
    assert [r.id for r in rs.candidates(parse("f(x)"))] == ["h", "p", "t", "f"]
    rs.remove("f")
    assert [r.id for r in rs.candidates(parse("f(x)"))] == ["h", "p", "t"]
    rs.add(parse_rule_line("rule f2 = f(?x) -> ?x auto"))
    assert [r.id for r in rs.candidates(parse("f(x)"))] == ["h", "p", "t", "f2"]
    rs.remove("never-added")                 # removing an unknown id is a no-op
    assert [r.id for r in rs.candidates(parse("x"))] == ["h", "p", "t"]
    assert rs.ids() == ["h", "p", "t", "g", "lit", "f2"]


def _full_scan_autosimplify(t, rs, budget=100000):
    """The fixed-point loop before the index: every auto rule at every path."""
    auto = [r for r in rs.rules.values() if r.auto and r.guard is None]
    cur = rebuild(t, budget)
    while True:
        base = cost(cur)
        nxt = None
        for path in T.all_paths(cur):
            for rule in sorted(auto, key=lambda r: r.priority):
                res = apply_rule(rule, cur, path, budget=budget)
                if res.ok and cost(res.term) < base:
                    nxt = res.term
                    break
            if nxt is not None:
                break
        if nxt is None:
            return cur
        cur = rebuild(nxt, budget)


def test_autosimplify_matches_the_full_scan_reference(monkeypatch):
    rs = _ruleset()
    monkeypatch.setattr("cas.math.rules.declared_ruleset", lambda ctx: rs)
    for src in _TERMS:
        t = parse(src)
        assert autosimplify(_ctx(), t) is _full_scan_autosimplify(t, rs), src
