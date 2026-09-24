"""Definition expansion is the only automatic substitution channel."""

import pytest

from cas.errors import BudgetExceeded
from cas.frontend.parser import parse
from cas.math.definitions import expand
from cas.runtime import Runtime
from cas.syntax.term import S


def _lookup(runtime: Runtime):
    return {
        S("u"): parse(runtime, "x^2"),
        S("v"): parse(runtime, "u + 1"),
    }.get


def test_nested_aliases_expand_in_one_pass(runtime: Runtime) -> None:
    assert expand(_lookup(runtime), parse(runtime, "v")) is parse(runtime, "x^2 + 1")


def test_expansion_is_idempotent(runtime: Runtime) -> None:
    once = expand(_lookup(runtime), parse(runtime, "v^2"))
    assert expand(_lookup(runtime), once) is once


def test_symbol_without_a_definition_is_untouched(runtime: Runtime) -> None:
    term = parse(runtime, "z + 1")
    assert expand(_lookup(runtime), term) is term


def test_budget_is_reported_not_silently_truncated(runtime: Runtime) -> None:
    with pytest.raises(BudgetExceeded):
        expand(_lookup(runtime), parse(runtime, "v*2"), budget=1)


def test_quoted_content_is_held_and_not_expanded(runtime: Runtime) -> None:
    quoted = parse(runtime, "'u")
    assert expand(_lookup(runtime), quoted) is quoted
