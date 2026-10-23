"""Parameterized coefficients through the frontend, workflow and kernel."""

from cas.frontend.session import Session
from cas.language.problems import ParameterMode
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime import bootstrap_parameterized
from cas.workflow.records import OperationStatus


def test_a_is_a_coefficient_parameter_and_x_is_the_target():
    runtime = bootstrap_parameterized()
    assert runtime.ring.generators == (runtime.variable,)
    assert set(runtime.request.parameters).isdisjoint(runtime.ring.generators)
    assert runtime.request.parameter_mode is ParameterMode.GENERIC_PARAMETERS

    session = Session(runtime)
    assert session.execute("expr F := a*x^2") == "@F: a*x^2"
    assert session.execute("diff @F") == "verified @E0: 2*a*x"

    link = session.workspace.links()[0]
    assert link.status is OperationStatus.VERIFIED
    assert link.judgment is not None
    judgment = runtime.store.get_judgment(link.judgment)
    assert runtime.store.applicability(
        judgment.id, runtime.frame.id
    ).is_applicable()

    claim = parse_has_derivative(
        runtime.vocabulary, link.specification.term
    )
    assert claim is not None
    assert claim.source == session.object("F").term
    assert claim.candidate == session.object("E0").term
    assert claim.variable.symbol_id == runtime.variable

    source_value = runtime.bridge.to_value(session.object("F").term)
    result_value = runtime.bridge.to_value(session.object("E0").term)
    assert source_value is not None
    assert result_value is not None
    assert runtime.ring.equal(
        result_value, runtime.differential.deriv(source_value)
    )

    candidate = session.workspace.candidate(link.candidate)
    assert candidate.problem.parameter_mode is ParameterMode.GENERIC_PARAMETERS
    assert candidate.problem.target == runtime.variable


def test_the_parameter_is_not_a_differentiation_target():
    runtime = bootstrap_parameterized()
    session = Session(runtime)
    session.execute("a*x")
    source = session.object("E0")
    parameter = runtime.request.parameters[0]
    result = session.workspace.differentiate(source, parameter)
    assert result.status is OperationStatus.UNSUPPORTED
    assert runtime.store.stats()["judgments"] == 0


def test_a_constant_parameter_differentiates_to_zero():
    runtime = bootstrap_parameterized()
    session = Session(runtime)
    assert session.execute("a") == "@E0: a"
    assert session.execute("diff") == "verified @E1: 0"
    assert runtime.store.stats()["judgments"] == 1


def test_reciprocal_parameters_are_refused_without_writing():
    runtime = bootstrap_parameterized()
    session = Session(runtime)
    session.execute("1/a")
    before = runtime.store.stats()
    assert session.execute("diff").startswith("unsupported:")
    assert runtime.store.stats() == before
    assert session.workspace.links() == ()
