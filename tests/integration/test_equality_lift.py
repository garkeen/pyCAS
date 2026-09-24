from cas.frontend.parser import parse
from cas.runtime import Runtime, new_workflow
from cas.workflow.command import Claim, Trans, Use


def test_transitivity_requires_two_matching_equality_premises(
    runtime: Runtime,
) -> None:
    workflow = new_workflow(runtime)
    first = workflow.add(parse(runtime, "A == B"), Claim())
    second = workflow.add(parse(runtime, "B == C"), Claim())
    result = workflow.add(
        parse(runtime, "A == C"),
        Trans(
            premises=(first.id, second.id),
            value=(first.content.args[0], first.content.args[1], second.content.args[1]),
        ),
    )
    assert result.status == "committed"
    assert result.content == parse(runtime, "A == C")


def test_lift_uses_declared_policy_and_piecewise_condition(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    source = workflow.add(parse(runtime, "A == B"), Claim())
    target = workflow.add(parse(runtime, "Piecewise(A, x > 0, D, TRUE) == C"), Claim())
    result = workflow.add(
        parse(runtime, "Piecewise(B, x > 0, D, TRUE) == C"),
        Use(
            source=source.id,
            direction="->",
            path=(0, 0),
            target=target.id,
            premises=(source.id, target.id),
        ),
    )
    assert result.status == "committed"
    assert result.guards == (parse(runtime, "x > 0"),)


def test_lift_rejects_derivative_and_noninteger_power_base(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    source = workflow.add(parse(runtime, "A == B"), Claim())
    derivative = workflow.add(parse(runtime, "Derivative(A, x) == C"), Claim())
    rejected = workflow.add(
        parse(runtime, "Derivative(B, x) == C"),
        Use(
            source=source.id,
            direction="->",
            path=(0, 0),
            target=derivative.id,
            premises=(source.id, derivative.id),
        ),
    )
    assert rejected.status == "refused"
    power = workflow.add(parse(runtime, "A^(1/2) == C"), Claim())
    rejected_power = workflow.add(
        parse(runtime, "B^(1/2) == C"),
        Use(
            source=source.id,
            direction="->",
            path=(0, 0),
            target=power.id,
            premises=(source.id, power.id),
        ),
    )
    assert rejected_power.status == "refused"


def test_lift_reabstracts_bound_integrand(runtime: Runtime) -> None:
    workflow = new_workflow(runtime)
    source = workflow.add(parse(runtime, "A == B"), Claim())
    target = workflow.add(parse(runtime, "integrate(A, x) == C"), Claim())
    result = workflow.add(
        parse(runtime, "integrate(B, x) == C"),
        Use(
            source=source.id,
            direction="->",
            path=(0, 0, 0),
            target=target.id,
            premises=(source.id, target.id),
        ),
    )
    assert result.status == "committed"
    assert result.content == parse(runtime, "integrate(B, x) == C")
