"""Back-substitution judge acceptance."""

import pytest

from cas.frontend.parser import parse
from cas.kernel.verdict import YES
from cas.math.judge import back_substitute, guard_report, has_piecewise, verify_solution
from cas.math.piecewise import piecewise
from cas.runtime import Runtime
from cas.syntax import term as T
from cas.syntax.term import S


def _int(value: int) -> T.Int:
    return T.Int(value)


def _equation(runtime: Runtime, source: str) -> T.Expr:
    return parse(runtime, source)


@pytest.mark.parametrize(
    "source,value,want",
    [
        ("2*x + 3 == 7", 2, True),
        ("2*x + 3 == 7", 3, False),
        ("x^2 - 4 == 0", 2, True),
        ("x^2 - 4 == 0", 3, False),
        ("x/2 - 1 == 0", 2, True),
        ("x - x == 0", 5, True),
    ],
)
def test_back_substitution_zero_test(
    runtime: Runtime,
    source: str,
    value: int,
    want: bool,
) -> None:
    result = back_substitute(
        runtime.math,
        _equation(runtime, source),
        S("x"),
        _int(value),
    )
    assert result.verdict.is_yes() is want


def test_spurious_solution_reports_exact_value(runtime: Runtime) -> None:
    result = back_substitute(
        runtime.math,
        _equation(runtime, "x^2 - 4 == 0"),
        S("x"),
        _int(3),
    )
    assert result.verdict.is_no()
    assert result.exact == 5


def test_zero_test_authority_is_domain_normal_form(runtime: Runtime) -> None:
    result = back_substitute(
        runtime.math,
        _equation(runtime, "2*x + 3 == 7"),
        S("x"),
        _int(2),
    )
    assert result.verdict.is_yes()
    assert result.exact == 0


def _piecewise_equation(runtime: Runtime) -> tuple[T.Expr, S]:
    x = S("x")
    value = piecewise(
        [
            (T.plus(x, T.neg(_int(1))), parse(runtime, "x > 0")),
            (T.plus(x, _int(1)), parse(runtime, "x <= 0")),
        ]
    )
    return T.mk(S("Eq"), (value, T.ZERO)), x


@pytest.mark.parametrize(
    "value,want",
    [(1, True), (-1, True), (2, False), (-3, False), (0, False)],
)
def test_piecewise_equation_pointwise_collapse(
    runtime: Runtime,
    value: int,
    want: bool,
) -> None:
    equation, x = _piecewise_equation(runtime)
    verdict = back_substitute(runtime.math, equation, x, _int(value)).verdict
    assert verdict.is_yes() is want


def test_piecewise_uses_collapse_channel(runtime: Runtime) -> None:
    equation, x = _piecewise_equation(runtime)
    result = back_substitute(runtime.math, equation, x, _int(1))
    assert has_piecewise(result.diff) is True
    assert result.exact is None


def test_undecided_is_not_reported_as_pass(runtime: Runtime) -> None:
    equation = T.mk(S("Eq"), (parse(runtime, "sin(x)"), T.ZERO))
    result = back_substitute(runtime.math, equation, S("x"), _int(0))
    assert result.verdict.is_unknown()
    assert verify_solution(runtime.math, equation, S("x"), _int(0)).is_unknown()


def test_nonzero_solution_does_not_pass(runtime: Runtime) -> None:
    equation = _equation(runtime, "2*x + 3 == 7")
    assert verify_solution(runtime.math, equation, S("x"), _int(2)) is YES
    assert verify_solution(runtime.math, equation, S("x"), _int(3)).is_no()


def test_guard_failure_and_refutation(runtime: Runtime) -> None:
    equation = _equation(runtime, "2*x + 3 == 7")
    verdict = verify_solution(
        runtime.math,
        equation,
        S("x"),
        _int(2),
        guards=[parse(runtime, "x > 5")],
    )
    assert verdict.is_no()


def test_guard_report_gives_per_item_verdicts(runtime: Runtime) -> None:
    guards = [parse(runtime, "x > 0"), parse(runtime, "x < 10")]
    report = guard_report(runtime.math, guards, S("x"), _int(2))
    assert len(report) == 2
    assert all(check.verdict is YES for check in report)
    assert all(check.substituted is not None for check in report)


def test_zero_judge_implemented_only_in_judge() -> None:
    import cas.math.judge as judge
    import cas.workflow.workflow as workflow

    for name in ("_piecewise_aware_zero", "_has_piecewise", "_has_undef"):
        assert not hasattr(workflow, name)
    assert judge.is_zero is not None


def test_repl_does_not_steal_workflow_privates() -> None:
    from pathlib import Path

    source = Path("cas/frontend/repl.py").read_text(encoding="utf-8")
    assert "_piecewise_aware_zero" not in source
