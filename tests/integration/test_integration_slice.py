"""Polynomial integration goes through the same derivative trust boundary."""

from support import head_app, variable

from cas.frontend.session import Session
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime import bootstrap, bootstrap_parameterized, new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus


def polynomial(runtime):
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            T.number(3),
            head_app(runtime.signature, StructuralHead.POWER, x, T.number(2)),
        ),
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            head_app(
                runtime.signature, StructuralHead.TIMES, T.number(2), x
            ),
            T.number(1),
        ),
    )


def test_a_polynomial_antiderivative_is_verified_by_the_derivative_checker():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime), "f")
    result = workspace.integrate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    claim = parse_has_derivative(
        runtime.vocabulary, result.verifications[0].specification.term
    )
    assert claim is not None
    assert claim.source == result.result.term
    assert claim.candidate == source.term
    assert claim.variable.symbol_id == runtime.variable
    assert runtime.store.stats()["judgments"] == 1


def test_the_session_exposes_the_integrate_command():
    session = Session(bootstrap())
    assert session.execute("3*x^2 + 2*x + 1").startswith("@E0:")
    output = session.execute("integrate")
    assert output.startswith("verified @E1:")
    assert session.focus is not None
    assert session.label_of(session.focus) == "E1"


def test_parameterized_integration_keeps_the_target_role():
    runtime = bootstrap_parameterized()
    workspace = new_workspace(runtime)
    parameter = runtime.request.parameters[0]
    x = variable(runtime)
    source_term = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.symbol(parameter, "a"),
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(2)),
    )
    source = workspace.intake(source_term, "a*x^2")
    result = workspace.integrate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    claim = parse_has_derivative(
        runtime.vocabulary, result.verifications[0].specification.term
    )
    assert claim is not None
    assert claim.variable.symbol_id == runtime.variable
    assert claim.source == result.result.term
    assert claim.candidate == source.term


def test_a_parameter_can_be_the_integration_target():
    runtime = bootstrap_parameterized()
    workspace = new_workspace(runtime)
    parameter = runtime.request.parameters[0]
    x = variable(runtime)
    source_term = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        T.symbol(parameter, "a"),
        x,
    )
    source = workspace.intake(source_term, "a*x")
    result = workspace.integrate(source, parameter)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    claim = parse_has_derivative(
        runtime.vocabulary, result.verifications[0].specification.term
    )
    assert claim is not None
    assert claim.variable.symbol_id == parameter
    assert claim.source == result.result.term
    assert claim.candidate == source.term


def test_a_reciprocal_is_outside_the_polynomial_integration_fragment():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    x = variable(runtime)
    source = workspace.intake(
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(-1)),
        "1/x",
    )
    before = runtime.store.stats()
    result = workspace.integrate(source, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.candidate is None
    assert runtime.store.stats() == before
    assert workspace.links() == ()
