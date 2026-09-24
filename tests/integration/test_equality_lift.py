"""Manual equality transitivity and congruence lifting."""

from cas.frontend.parser import parse
from cas.runtime import new_workflow
from cas.syntax import term as T
from cas.workflow.command import Claim, Trans, Use


def test_transitivity_requires_two_matching_equality_premises():
    wf = new_workflow()
    first = wf.add(parse("A == B"), Claim())
    second = wf.add(parse("B == C"), Claim())
    result = wf.add(parse("A == C"), Trans(
        premises=(first.id, second.id),
        value=(first.content.args[0], first.content.args[1], second.content.args[1])))
    assert result.status == "committed"
    assert result.content == parse("A == C")


def test_lift_uses_declared_function_policy_and_piecewise_condition():
    wf = new_workflow()
    source = wf.add(parse("A == B"), Claim())
    target = wf.add(parse("Piecewise(A, x > 0, D, TRUE) == C"), Claim())
    result = wf.add(parse("Piecewise(B, x > 0, D, TRUE) == C"), Use(
        source=source.id, direction="->", path=(0, 0), target=target.id,
        premises=(source.id, target.id)))
    assert result.status == "committed"
    assert result.guards == (parse("x > 0"),)


def test_lift_rejects_derivative_and_noninteger_power_base():
    wf = new_workflow()
    source = wf.add(parse("A == B"), Claim())
    derivative = wf.add(parse("Derivative(A, x) == C"), Claim())
    rejected = wf.add(parse("Derivative(B, x) == C"), Use(
        source=source.id, direction="->", path=(0, 0), target=derivative.id,
        premises=(source.id, derivative.id)))
    assert rejected.status == "refused"

    power = wf.add(parse("A^(1/2) == C"), Claim())
    rejected_power = wf.add(parse("B^(1/2) == C"), Use(
        source=source.id, direction="->", path=(0, 0), target=power.id,
        premises=(source.id, power.id)))
    assert rejected_power.status == "refused"


def test_lift_reabstracts_a_bound_integrand():
    wf = new_workflow()
    source = wf.add(parse("A == B"), Claim())
    target = wf.add(parse("integrate(A, x) == C"), Claim())
    result = wf.add(parse("integrate(B, x) == C"), Use(
        source=source.id, direction="->", path=(0, 0, 0), target=target.id,
        premises=(source.id, target.id)))
    assert result.status == "committed"
    assert result.content == parse("integrate(B, x) == C")
