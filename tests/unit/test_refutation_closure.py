import pytest

from cas.frontend.parser import parse
from cas.kernel.verdict import (
    No,
    Refutation,
    RefutationChannel,
    and3,
    or3,
    refute,
)
from cas.math.decide import decide
from cas.math.judge import back_substitute, verify_solution
from cas.math.piecewise import piecewise
from cas.math.rules import ApplyFailed, GuardedRule, apply_rule
from cas.math.tactics import solve_piecewise
from cas.runtime import Runtime, new_workflow
from cas.syntax import term as T
from cas.syntax.term import N, S
from cas.workflow.command import Claim, Solve



def test_refutation_requires_proposition_and_evidence(runtime: Runtime) -> None:
    proposition = parse(runtime, "1 == 2")
    with pytest.raises(ValueError):
        Refutation(
            RefutationChannel.EXACT_COMPARISON,
            None,
            (proposition,),
            (),
            "bad",
        )
    with pytest.raises(ValueError):
        Refutation(
            RefutationChannel.EXACT_COMPARISON,
            proposition,
            (),
            (),
            "empty",
        )


def test_logical_refutations_keep_outer_proposition_and_causes(runtime: Runtime) -> None:
    ctx = runtime.math
    first = decide(ctx, parse(runtime, "1 == 2"), ())
    second = decide(ctx, parse(runtime, "3 == 4"), ())
    outer_and = parse(runtime, "(1 == 2) && (3 == 4)")
    combined_and = and3(first, second, outer_and)
    assert isinstance(combined_and, No)
    assert combined_and.evidence.proposition is outer_and
    assert combined_and.evidence.causes[0].proposition is first.evidence.proposition

    outer_or = parse(runtime, "(1 == 2) || (3 == 4)")
    combined_or = or3(first, second, outer_or)
    assert isinstance(combined_or, No)
    assert combined_or.evidence.proposition is outer_or
    assert len(combined_or.evidence.causes) == 2
    assert {cause.proposition for cause in combined_or.evidence.causes} == {
        first.evidence.proposition,
        second.evidence.proposition,
    }


def test_closure_refutation_keeps_the_original_claim_and_child_evidence(
    runtime: Runtime,
) -> None:
    claim = parse(runtime, "x == 2")
    verdict = decide(runtime.math, claim, (parse(runtime, "x == 1"),))
    assert isinstance(verdict, No)
    assert verdict.evidence.proposition is claim
    assert verdict.evidence.causes
    assert verdict.evidence.causes[0].proposition == parse(runtime, "1 == 2")


def test_checker_commit_workflow_keeps_refutation_evidence(runtime: Runtime) -> None:
    wf = new_workflow(runtime)
    equation_step = wf.add(parse(runtime, "2*x + 3 == 7"), Claim())
    wrong = wf.add(
        T.eq(S("x"), N(3)),
        Solve(pred=equation_step.id, var=S("x"), solution=N(3)),
    )
    assert wrong.status == "refused"
    assert isinstance(wrong.refutation, Refutation)
    assert wrong.refutation.proposition == parse(runtime, "2*x + 3 == 7")
    assert wrong.refutation.witnesses
    assert wrong.refutation.detail in wrong.note


def test_undefined_is_a_domain_refutation_not_normal_form_nonzero(
    runtime: Runtime,
) -> None:
    x = S("x")
    value = piecewise([(T.SP("Undefined"), parse(runtime, "x > 0"))])
    equation = T.eq(value, N(0))
    result = back_substitute(runtime.math, equation, x, N(1))
    assert result.verdict.is_no()
    assert result.verdict.evidence.channel is RefutationChannel.DOMAIN
    assert result.verdict.evidence.proposition is equation


def test_exact_nonzero_keeps_its_own_channel(
    runtime: Runtime,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import cas.math.judge as judge

    monkeypatch.setattr(judge, "zero_of", lambda _ctx, _term: None)
    result = judge.back_substitute(
        runtime.math, parse(runtime, "2 == 3"), S("x"), N(0)
    )
    assert result.verdict.is_no()
    assert result.verdict.evidence.channel is RefutationChannel.EXACT_COMPARISON
    assert "exact evaluation is nonzero" in result.verdict.evidence.detail


def test_unknown_remains_unknown_and_guard_no_keeps_its_own_evidence(
    runtime: Runtime,
) -> None:
    unknown_bs = back_substitute(
        runtime.math, T.eq(parse(runtime, "sin(x)"), N(0)), S("x"), N(0)
    )
    assert unknown_bs.verdict.is_unknown()
    assert not unknown_bs.verdict.is_no()

    guard_verdict = verify_solution(
        runtime.math,
        parse(runtime, "2*x + 3 == 7"),
        S("x"),
        N(2),
        guards=(parse(runtime, "x > 5"),),
    )
    assert guard_verdict.is_no()
    assert guard_verdict.evidence.proposition == parse(runtime, "2 > 5")


def test_rules_and_piecewise_tactics_retain_negative_branch_evidence(
    runtime: Runtime,
) -> None:
    guarded = GuardedRule(
        "guarded",
        parse(runtime, "?x", pattern=True),
        parse(runtime, "?x", pattern=True),
        parse(runtime, "false", pattern=True),
    )
    negative = refute(
        RefutationChannel.ORDER,
        parse(runtime, "false"),
        parse(runtime, "false"),
        detail="guard is false",
    )
    result = apply_rule(
        guarded,
        parse(runtime, "x"),
        (),
        guard_eval=lambda _condition, _substitution: negative,
    )
    assert isinstance(result, ApplyFailed)
    assert result.refutations == (negative.evidence,)

    x = S("x")
    function = piecewise(
        [
            (x, parse(runtime, "x > 5")),
            (T.plus(x, N(1)), parse(runtime, "x <= 5")),
        ]
    )
    solutions = solve_piecewise(runtime.math, function, x, N(0))
    assert solutions.points == [N(-1)]
    assert solutions.refutations
    assert all(evidence.proposition is not None for evidence in solutions.refutations)
