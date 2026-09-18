# -*- coding: utf-8 -*-
"""The back-substitution judge: the atom of the verification system, with a single
implementation in the whole system.

Nails: the judge was once split between a private
`workflow._piecewise_aware_zero` and an inline copy in the REPL, and the two had
already diverged in channel order (the REPL tried eval_exact first, the workflow only
used zero_of). After converging, the adjudication authority is zero_of (the domain
normal form) alone.
"""

import pytest

from cas.syntax import term as T
from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.math.piecewise import piecewise
from cas.kernel.verdict import YES, NO
from cas.math.judge import (back_substitute, is_zero, guard_report,
                       verify_solution, has_piecewise, has_undef)


def Int(n):
    return T.Int(n)


def eq_of(src):
    return parse(src)


# ---------------------------------------------------------------------------
# True solutions / spurious solutions
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("src,val,want", [
    ("2*x + 3 == 7", 2, True),        # true solution
    ("2*x + 3 == 7", 3, False),       # spurious solution
    ("x^2 - 4 == 0", 2, True),
    ("x^2 - 4 == 0", 3, False),
    ("x/2 - 1 == 0", 2, True),
    ("x - x == 0", 5, True),
])
def test_back_substitution_zero_test(src, val, want):
    bs = back_substitute(eq_of(src), T.S("x"), Int(val))
    assert bs.zero is want


def test_spurious_solution_reports_exact_value():
    bs = back_substitute(eq_of("x^2 - 4 == 0"), T.S("x"), Int(3))
    assert bs.zero is False
    assert bs.exact == 5                      # a display value, not part of adjudication


def test_zero_test_authority_is_domain_normal_form():
    """eval_exact only produces a display value; the decision comes from zero_of, which
    covers strictly more."""
    bs = back_substitute(eq_of("2*x + 3 == 7"), T.S("x"), Int(2))
    assert bs.zero is True
    assert bs.exact == 0                      # both are exact arithmetic and must agree


# ---------------------------------------------------------------------------
# Piecewise: zero test after point collapse
# ---------------------------------------------------------------------------

def _piecewise_equation():
    x = T.S("x")
    # f(x) = x-1 (x>0), x+1 (x<=0)  =>  f(x)=0 has solutions x=1 and x=-1
    pw = piecewise([(T.plus(x, T.neg(Int(1))), parse("x > 0")),
                    (T.plus(x, Int(1)), parse("x <= 0"))])
    return T.mk(S("Eq"), (pw, T.ZERO)), x


@pytest.mark.parametrize("val,want", [(1, True), (-1, True),
                                      (2, False), (-3, False), (0, False)])
def test_piecewise_equation_pointwise_collapse(val, want):
    eq, x = _piecewise_equation()
    assert back_substitute(eq, x, Int(val)).zero is want


def test_piecewise_uses_collapse_channel():
    eq, x = _piecewise_equation()
    bs = back_substitute(eq, x, Int(1))
    assert has_piecewise(bs.diff) is True
    assert bs.exact is None                   # ring-layer evaluation cannot handle a piecewise term


# ---------------------------------------------------------------------------
# Undecided and outside the domain
# ---------------------------------------------------------------------------

def test_undecided_is_not_reported_as_pass():
    """A term containing transcendentals misses the projection: None is undecided, not
    "not a solution"."""
    eq = T.mk(S("Eq"), (parse("sin(x)"), T.ZERO))
    bs = back_substitute(eq, T.S("x"), Int(0))
    assert bs.zero is None                      # cannot be decided
    assert verify_solution(eq, T.S("x"), Int(0)).is_unknown()


def test_nonzero_solution_does_not_pass():
    """The three exits of verify_solution: NO / Unknown / YES."""
    ok = verify_solution(eq_of("2*x + 3 == 7"), T.S("x"), Int(2))
    assert ok is YES
    bad = verify_solution(eq_of("2*x + 3 == 7"), T.S("x"), Int(3))
    assert bad is NO


# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------

def test_guard_failure_and_refutation():
    eq = eq_of("2*x + 3 == 7")
    # true solution x=2 with a false guard x>5 attached: the zero test passes, the guard does not
    guards = [parse("x > 5")]
    v = verify_solution(eq, T.S("x"), Int(2), guards=guards)
    assert v is NO


def test_guard_report_gives_per_item_verdicts():
    guards = [parse("x > 0"), parse("x < 10")]
    rep = guard_report(guards, T.S("x"), Int(2))
    assert len(rep) == 2
    assert all(c.verdict is YES for c in rep)
    assert all(c.subst is not None for c in rep)


# ---------------------------------------------------------------------------
# Single implementation
# ---------------------------------------------------------------------------

def test_zero_judge_implemented_only_in_judge():
    """The workflow must no longer hold a zero-test copy, and the REPL must not steal
    private functions."""
    import cas.workflow.workflow as W
    import cas.math.judge as J
    for name in ("_piecewise_aware_zero", "_has_piecewise", "_has_undef"):
        assert not hasattr(W, name), f"workflow still holds a judge copy: {name}"
    assert J.is_zero is not None


def test_repl_does_not_steal_workflow_privates():
    import pathlib
    src = pathlib.Path("cas/frontend/repl.py").read_text(encoding="utf-8")
    assert "_piecewise_aware_zero" not in src
