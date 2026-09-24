"""Constraint solving and three-valued antiderivative verification."""

from cas.frontend.parser import parse
from cas.math.calculus.integration.verify import verify_antideriv
from cas.math.constraints import solve_linear_constraints
from cas.math.linearform import is_linear
from cas.runtime import Runtime, new_workflow
from cas.syntax import term as T
from cas.syntax.term import N, S
from cas.workflow.command import Claim, Integrate


def test_linear_form_decomposition_holds_for_transcendental_coeffs(
    runtime: Runtime,
) -> None:
    u = S("_u")
    expression = T.plus(
        T.plus(parse(runtime, "exp(x)*sin(x)"), T.neg(u)),
        T.times(N(3), u),
    )
    assert is_linear(expression, (u,))
    assert not is_linear(T.times(u, u), (u,))
    assert not is_linear(T.pw(u, N(-1)), (u,))
    assert not is_linear(parse(runtime, "sin(_u)"), (u,))


def test_coefficient_sign_kept_with_constant_factor(runtime: Runtime) -> None:
    u, v = S("_u"), S("_v")
    result = solve_linear_constraints(
        runtime.math,
        [T.eq(u, T.neg(v)), T.eq(u, N(2))],
        (u, v),
    )
    assert result is not None
    valuation, complete = result
    assert complete
    assert valuation[u] is N(2)
    assert valuation[v] is N(-2)


def test_solver_honestly_refuses_nonlinear_and_inconsistent(
    runtime: Runtime,
) -> None:
    u, x = S("_u"), S("x")
    assert solve_linear_constraints(
        runtime.math, [T.eq(T.times(u, u), x)], (u,)
    ) is None
    assert solve_linear_constraints(
        runtime.math, [T.eq(u, N(1)), T.eq(u, N(2))], (u,)
    ) is None


def test_antiderivative_verification_three_valued(runtime: Runtime) -> None:
    x = S("x")
    proved = verify_antideriv(
        runtime.math,
        parse(runtime, "1/3*x^3"),
        parse(runtime, "x^2"),
        x,
    )
    assert proved.is_yes()
    refuted = verify_antideriv(
        runtime.math,
        parse(runtime, "x^2"),
        parse(runtime, "x^2"),
        x,
    )
    assert refuted.is_no()
    assert refuted.evidence.proposition == T.eq(
        parse(runtime, "2*x"), parse(runtime, "x^2")
    )
    undecided = verify_antideriv(
        runtime.math,
        parse(runtime, "(exp(x)*(sin(x) - cos(x)))/2"),
        parse(runtime, "exp(x)*sin(x)"),
        x,
    )
    assert undecided.is_unknown()


def test_loop_integral_remains_undecided(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    u, v, x = S("_u"), S("_v"), S("x")
    first = parse(runtime, "exp(x)*sin(x)")
    second = parse(runtime, "exp(x)*cos(x)")
    workflow.add_constraint(T.eq(u, T.plus(first, T.neg(v))))
    workflow.add_constraint(T.eq(v, T.plus(T.plus(second, N(-1)), u)))
    valuation, _steps, complete = workflow.solve_constraints((u, v))
    assert valuation is not None and complete
    assert verify_antideriv(runtime.math, valuation[u], first, x).is_unknown()
    source = workflow.add(first, Claim())
    content = T.eq(T.mk(S("Integrate"), (T.mk_bound(x, first),)), valuation[u])
    result = workflow.add(
        content,
        Integrate(pred=source.id, var=x, antideriv=valuation[u]),
    )
    assert result.status == "undecided"
    assert result.judgment is None
