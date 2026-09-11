# -*- coding: utf-8 -*-
"""Constraint solving and three-valued antiderivative verification.

Two disciplines meet here:
* the solver sits on the **untrusted side**: it produces a candidate and the checker
  re-verifies it;
* when the decision channels cannot cover an input, the result must be **honestly
  undecided** -- "cannot decide" is never reported as "not an antiderivative".
"""

from cas.frontend.parser import parse
from cas.syntax.term import S, N
from cas.syntax import term as T
from cas.math.constraints import solve_linear_constraints, is_linear
from cas.math.calculus.integration.verify import verify_antideriv
from cas.runtime import new_workflow
from cas.workflow.command import Claim, Integrate


# --- linear-form analysis (syntactic, not relying on the simplifier) ---

def test_linear_form_decomposition_holds_for_transcendental_coeffs():
    u = S("_u")
    e = T.plus(T.plus(parse("exp(x)*sin(x)"), T.neg(u)), T.times(N(3), u))
    assert is_linear(e, (u,))
    assert not is_linear(T.times(u, u), (u,))
    assert not is_linear(T.pw(u, N(-1)), (u,))
    assert not is_linear(parse("sin(_u)"), (u,))


def test_coefficient_sign_kept_with_constant_factor():
    """The coefficient of `-1*v` must be -1 (this once broke because the Times
    decomposition missed the constant factor)."""
    u, v = S("_u"), S("_v")
    res = solve_linear_constraints([T.eq(u, T.neg(v)), T.eq(u, N(2))], (u, v))
    assert res is not None
    val, complete = res
    assert complete
    assert val[u] is N(2)
    assert val[v] is N(-2)


def test_solver_honestly_refuses_nonlinear_and_inconsistent():
    u, X = S("_u"), S("x")
    assert solve_linear_constraints([T.eq(T.times(u, u), X)], (u,)) is None
    assert solve_linear_constraints([T.eq(u, N(1)), T.eq(u, N(2))], (u,)) is None


# --- antiderivative zero test: three-valued ---

def test_antiderivative_verification_three_valued():
    X = S("x")
    # proved zero: polynomial
    assert verify_antideriv(parse("1/3*x^3"), parse("x^2"), X) is True
    # proved nonzero: a genuine refutation
    assert verify_antideriv(parse("x^2"), parse("x^2"), X) is False
    # undecided: correct, but the zero channel (trigonometric-basis zeroing) has not
    # been rebuilt -- must be None, not False
    assert verify_antideriv(parse("(exp(x)*(sin(x) - cos(x)))/2"),
                            parse("exp(x)*sin(x)"), X) is None


# --- loop-integral end to end ---

def test_loop_integral_end_to_end_solved_but_verification_undecided():
    wf = new_workflow()
    u, v, X = S("_u"), S("_v"), S("x")
    a, b = parse("exp(x)*sin(x)"), parse("exp(x)*cos(x)")
    wf.add_constraint(T.eq(u, T.plus(a, T.neg(v))))          # u = a - v
    wf.add_constraint(T.eq(v, T.plus(T.plus(b, N(-1)), u)))  # v = b - 1 + u

    val, steps, complete = wf.solve_constraints((u, v))
    assert val is not None and complete, "the cyclic system should have a unique solution"
    # the solution has the expected form, but the zero channel cannot cover it: undecided
    assert verify_antideriv(val[u], a, X) is None

    # the workflow therefore reports unverified, **never dead** (dead would be a forged
    # refutation)
    s0 = wf.add(a, Claim())
    content = T.eq(T.mk(S("Integrate"), (T.mk_bound(X, a),)), val[u])
    s1 = wf.add(content, Integrate(pred=s0.id, var=X, antideriv=val[u]))
    assert s1.status == "undecided", (s1.status, s1.note)
    assert s1.judgment is None
