from cas.api import solve_linear_with_condition
from cas.frontend.parser import parse
from cas.runtime import Runtime, new_workflow
from cas.syntax import term as T
from cas.syntax.term import S
from cas.workflow.command import Claim, Solve


def test_linear_parameter_symbols_are_not_refused(runtime: Runtime) -> None:
    solution, condition = solve_linear_with_condition(
        runtime, parse(runtime, "a*x + b == 0"), S("x")
    )
    assert condition == parse(runtime, "a != 0")
    assert T.is_eq(T.eq(S("x"), solution))


def test_parametric_solution_is_independently_committed_with_guard(
    runtime: Runtime,
) -> None:
    workflow = new_workflow(runtime)
    equation = parse(runtime, "a*x + b == 0")
    source = workflow.add(equation, Claim())
    solution, condition = solve_linear_with_condition(runtime, equation, S("x"))
    result = workflow.add(
        T.eq(S("x"), solution),
        Solve(
            pred=source.id,
            var=S("x"),
            solution=solution,
            condition=condition,
        ),
    )
    assert result.status == "committed"
    assert result.guards == (condition,)


def test_nonlinear_target_is_not_claimed_as_a_solution(runtime: Runtime) -> None:
    try:
        solve_linear_with_condition(
            runtime, parse(runtime, "x^2 + b == 0"), S("x")
        )
    except Exception as error:
        assert "degree" in str(error)
    else:
        raise AssertionError("nonlinear solve must refuse")
