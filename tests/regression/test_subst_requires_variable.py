# -*- coding: utf-8 -*-
"""Nail tests for the substitution command's key.

The substitution channel replaces a variable by a value. A compound key (the
frontend used to wrap the whole left-hand text into a symbol, so `subst B + C =
A` silently substituted nothing yet committed a step) and a variable that does
not occur must both be refused: a step whose name claims a substitution has to
actually be one.
"""

from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.syntax.term import S
from cas.workflow.command import Claim, Subst

install(bootstrap())


def _claimed(src):
    wf = new_workflow()
    return wf, wf.add(parse(src), Claim())


def test_compound_key_is_refused():
    wf, s0 = _claimed("A == B + C")
    s1 = wf.add(s0.content, Subst(pred=s0.id, var=S("B + C"), value=parse("A")))
    assert s1.status == "refused", f"status={s1.status}"


def test_absent_variable_is_refused():
    wf, s0 = _claimed("A == B + C")
    s1 = wf.add(s0.content, Subst(pred=s0.id, var=parse("z"), value=parse("7")))
    assert s1.status == "refused", f"status={s1.status}"
