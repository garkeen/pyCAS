# -*- coding: utf-8 -*-
"""Rule-line DSL parsing: the keyword scanner and the errors it reports.

A rule line is `rule <id> = <pattern> -> <template> [guard <pattern...>]
[prio <int>] [auto]`. Keyword recognition is structural: only a whole token at
bracket depth 0 is a keyword, a guard value may run over many tokens, and every
malformed line reports a ParseError naming what is wrong.
"""

import pytest

from cas.errors import ParseError
from cas.math.loader import parse_rule_line
from cas.syntax import term as T

# ---------------------------------------------------------------------------
# Keywords are depth-0 whole tokens
# ---------------------------------------------------------------------------

def test_identifier_in_an_argument_list_is_not_a_keyword():
    """`auto` inside a call is template text, because it is not a depth-0 token."""
    r = parse_rule_line("rule r = ?x -> f(?x, auto)")
    assert not r.auto and r.guard is None and r.priority == 100
    assert any(isinstance(a, T.Sym) and a.name == "auto" for a in r.template.args)
    r2 = parse_rule_line("rule r = ?x -> f(auto, ?x)")
    assert not r2.auto and r2.guard is None and r2.priority == 100
    assert any(isinstance(a, T.Sym) and a.name == "auto" for a in r2.template.args)


def test_trailing_keyword_sections_parse():
    auto = parse_rule_line("rule r = ?x -> f(?x) auto")
    assert auto.auto and auto.guard is None and auto.priority == 100
    guard = parse_rule_line("rule r = ?x -> f(?x) guard ?x > 0")
    assert not guard.auto and guard.guard is not None
    assert guard.guard.head.name == "Gt"
    prio = parse_rule_line("rule r = ?x -> f(?x) prio 5")
    assert prio.priority == 5 and not prio.auto and prio.guard is None


def test_guard_value_may_span_many_tokens():
    r = parse_rule_line("rule r = ?x -> f(?x) guard a > 0 && b < 1 prio 7")
    assert not r.auto and r.priority == 7
    assert r.guard is not None and r.guard.head.name == "And"


def test_auto_rule_cannot_carry_a_guard():
    with pytest.raises(ParseError):
        parse_rule_line("rule r = ?x -> f(?x) guard ?x > 0 auto")


# ---------------------------------------------------------------------------
# Honest errors
# ---------------------------------------------------------------------------

def test_bare_keyword_where_template_required_names_the_keyword():
    with pytest.raises(ParseError) as e:
        parse_rule_line("rule r = ?x -> auto")
    msg = str(e.value)
    assert "auto" in msg and "template" in msg


def test_guard_without_a_value_is_a_parse_error():
    with pytest.raises(ParseError):
        parse_rule_line("rule r = ?x -> f(?x) guard")


def test_prio_without_an_integer_is_a_parse_error():
    """A malformed priority is an admission-channel ParseError, not a ValueError."""
    with pytest.raises(ParseError) as e:
        parse_rule_line("rule r4 = ?x -> f(?x) prio x")
    assert "x" in str(e.value)
    with pytest.raises(ParseError):
        parse_rule_line("rule r4 = ?x -> f(?x) prio")


def test_trailing_garbage_after_a_guard_is_never_silently_dropped():
    with pytest.raises(ParseError):
        parse_rule_line("rule r = ?x -> f(?x) guard ?x > 0 zzz")
