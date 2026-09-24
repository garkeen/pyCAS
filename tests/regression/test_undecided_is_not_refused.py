# -*- coding: utf-8 -*-
"""Nail tests for "undecided is not a refutation".

`equal()` folded "outside the projection" into False, so a candidate the system
cannot re-check was reported as refuted with a mismatch message. Refutation
requires evidence; a capability gap is `undecided` and must not enter trusted
reasoning, but it must not be dressed up as a refutation either.
"""

from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.frontend.parser import parse
from cas.workflow.command import Claim, Rewrite

install(bootstrap())


def test_unprovable_identity_is_undecided_not_refused():
    wf = new_workflow()
    s0 = wf.add(parse("sin(x) + sin(x)"), Claim())
    # 2*sin(x) is equal, but the current fragment has no trigonometric
    # collection channel: the checker must report undecided, not refuted.
    s1 = wf.add(parse("2*sin(x)"), Rewrite(pred=s0.id))
    assert s1.status == "undecided", f"status={s1.status} note={s1.note}"
