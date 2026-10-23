"""The derivative checker over a parameterized coefficient ring."""

from support import head_app, runtime_proposition, variable

from cas.kernel.evidence import CheckRequest, Refuted, Unverified, Verified
from cas.language.decisions import Reason
from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.checker import DerivativeCertificate
from cas.math.calculus.differentiation.specification import has_derivative
from cas.runtime import bootstrap_parameterized
from cas.syntax import term as T


def setup():
    runtime = bootstrap_parameterized()
    parameter = T.symbol(runtime.request.parameters[0], "a")
    x = variable(runtime)
    source = head_app(
        runtime.signature,
        StructuralHead.TIMES,
        parameter,
        head_app(runtime.signature, StructuralHead.POWER, x, T.number(2)),
    )
    value = runtime.bridge.to_value(source)
    assert value is not None
    candidate = runtime.bridge.to_term(runtime.differential.deriv(value))
    assert candidate is not None
    return runtime, parameter, x, source, candidate


def claim(runtime, source, candidate, variable_term=None):
    return runtime_proposition(
        runtime,
        has_derivative(
            runtime.vocabulary,
            T.TRUE,
            source,
            variable(runtime) if variable_term is None else variable_term,
            candidate,
        ),
    )


def check(runtime, proposition, source, candidate, variable_id=None):
    certificate = DerivativeCertificate(
        T.TRUE,
        source,
        runtime.variable if variable_id is None else variable_id,
        candidate,
    )
    return runtime.checker.check(
        CheckRequest(runtime.frame.id, (proposition,), (), certificate)
    )


def test_parameterized_candidates_are_verified():
    runtime, parameter, x, source, candidate = setup()
    outcome = check(runtime, claim(runtime, source, candidate), source, candidate)
    assert isinstance(outcome, Verified)


def test_a_perturbed_parameterized_candidate_is_refuted():
    runtime, parameter, x, source, candidate = setup()
    wrong = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        candidate,
        T.number(1),
    )
    outcome = check(runtime, claim(runtime, source, wrong), source, wrong)
    assert isinstance(outcome, Refuted)
    assert outcome.witnesses == (source, wrong)


def test_the_parameter_is_not_the_target():
    runtime, parameter, x, source, candidate = setup()
    proposition = runtime_proposition(
        runtime,
        has_derivative(
            runtime.vocabulary, T.TRUE, source, parameter, candidate
        ),
    )
    outcome = check(
        runtime,
        proposition,
        source,
        candidate,
        variable_id=runtime.request.parameters[0],
    )
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT


def test_reciprocals_of_a_parameter_are_outside_the_fragment():
    runtime, parameter, x, _, _ = setup()
    source = head_app(
        runtime.signature,
        StructuralHead.POWER,
        parameter,
        T.number(-1),
    )
    candidate = T.number(0)
    outcome = check(runtime, claim(runtime, source, candidate), source, candidate)
    assert isinstance(outcome, Unverified)
    assert outcome.reason is Reason.FRAGMENT
