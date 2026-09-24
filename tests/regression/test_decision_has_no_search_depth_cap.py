# -*- coding: utf-8 -*-
"""Nail tests for the search-depth cap in the decision layer.

The verdict of a decision is a mathematical answer and must not depend on how
deep the query entered the pipeline: a hardcoded depth cap made the same
question come out YES or NO depending on the entry depth, which is a wrong
decision procedure, not a budget. Termination is guaranteed by a cycle guard on
visited facts, never by truncating the search. These nails pin that shape.
"""

import inspect

from cas.runtime import bootstrap, get_runtime, new_workflow
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.kernel.scope import Assumptions
from cas.math import decide as D
from cas.syntax import term as T
from cas.workflow.command import Claim

install(bootstrap())


def _ctx():
    return get_runtime().math


def _frame(*facts):
    wf = new_workflow()
    for src in facts:
        wf.add(parse(src), Claim())
    return Assumptions.of(wf.store.scopes, wf.scope)


def test_no_hardcoded_search_depth_cap():
    assert not hasattr(D, "_MAX_DEPTH"), \
        "a hardcoded search-depth cap came back into the decision layer"


def test_decide_has_no_depth_parameter():
    params = inspect.signature(D.decide).parameters
    assert not any("depth" in name for name in params), \
        f"the decision entry takes a search-depth parameter again: {tuple(params)}"


def test_verdict_is_the_same_from_every_entry_path():
    ctx = _ctx()
    frame = _frame("A = 1")
    for src in ("1 + 1 == 2", "A + A == 2", "A == 1", "x + x == 2"):
        fact = parse(src)
        direct = D.decide(ctx, fact, frame)
        nested = D.decide(ctx, T.mk(T.S("And"), (fact, T.TRUE)), frame)
        assert direct is nested, \
            f"{src}: entry path changed the verdict ({direct} vs {nested})"
