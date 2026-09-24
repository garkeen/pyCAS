# -*- coding: utf-8 -*-
"""Definition expansion: the only automatic substitution channel.

A definition is a predicative alias (`u := x^2`): its body does not refer to the
symbol being defined, so the alias graph is acyclic and expansion terminates
without a depth cap. An equation is an assumption and is never expanded. These
tests pin termination, idempotence, the budget report and quote handling.
"""

import pytest

from cas.runtime import bootstrap
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.errors import BudgetExceeded
from cas.math.definitions import expand
from cas.syntax.term import S

install(bootstrap())


def _lookup():
    return {S("u"): parse("x^2"), S("v"): parse("u + 1")}.get


def test_nested_aliases_expand_in_one_pass():
    assert expand(_lookup(), parse("v")) is parse("x^2 + 1")


def test_expansion_is_idempotent():
    once = expand(_lookup(), parse("v^2"))
    assert expand(_lookup(), once) is once


def test_symbol_without_a_definition_is_untouched():
    assert expand(_lookup(), parse("z + 1")) is parse("z + 1")


def test_budget_is_reported_not_silently_truncated():
    with pytest.raises(BudgetExceeded):
        expand(_lookup(), parse("v*2"), budget=1)


def test_quoted_content_is_held_and_not_expanded():
    quoted = parse("'u")
    assert expand(_lookup(), quoted) is quoted
