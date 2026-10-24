"""Parameterized coefficients through the frontend, workflow and kernel."""

import pytest

from cas.frontend.errors import SessionError
from cas.frontend.session import Session
from cas.language.problems import ParameterMode
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime import bootstrap, bootstrap_parameterized
from cas.semantics.specialization import CoverageClaim
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.workflow.records import OperationStatus


def test_a_is_a_coefficient_parameter_and_x_is_the_target():
    runtime = bootstrap_parameterized()
    assert runtime.ring.generators == (runtime.variable,)
    assert set(runtime.request.parameters).isdisjoint(runtime.ring.generators)
    assert runtime.request.parameter_mode is ParameterMode.ALL_PARAMETER_VALUES

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
    assert candidate.problem.parameter_mode is ParameterMode.ALL_PARAMETER_VALUES
    assert candidate.problem.target == runtime.variable

    generic = session.workspace.generic_result(session.object("F"))
    assert generic is not None
    assert generic.coverage_claim is CoverageClaim.ALL_VALUES
    assert generic.is_unconditional
    assert generic.excluded_cases == ()
    assert generic.valid_on.term == T.TRUE
    assert generic.result == session.object("E0").term
    assert generic.correctness_specification == link.specification


def test_a_generic_request_claims_only_the_formal_family():
    runtime = bootstrap_parameterized(
        parameter_mode=ParameterMode.GENERIC_PARAMETERS
    )
    session = Session(runtime)
    session.execute("expr F := a*x^2")
    result = session.differentiate(session.object("F"))
    assert result.status is OperationStatus.VERIFIED
    assert result.generic is not None
    assert result.generic.coverage_claim is CoverageClaim.GENERIC
    assert result.candidate is not None
    assert (
        result.candidate.problem.parameter_mode
        is ParameterMode.GENERIC_PARAMETERS
    )


def test_exact_parameter_points_are_specialized_and_reverified():
    runtime = bootstrap_parameterized()
    session = Session(runtime)
    session.execute("expr F := a*x^2")
    assert session.execute("diff @F") == "verified @E0: 2*a*x"

    assert session.execute("specialize @F a=3") == "verified @E1: 6*x"
    assert session.execute("specialize @F a=0") == "verified @E2: 0"
    assert session.execute("specialize @F a=1/2") == "verified @E3: x"

    assert runtime.store.stats()["judgments"] == 4
    links = session.workspace.links()
    assert len(links) == 4
    for link in links[1:]:
        assert link.status is OperationStatus.VERIFIED
        assert link.judgment is not None
        claim = parse_has_derivative(
            runtime.vocabulary, link.specification.term
        )
        assert claim is not None
        assert not B.free_symbols(claim.source) & set(runtime.request.parameters)
        assert not B.free_symbols(claim.candidate) & set(runtime.request.parameters)
        inference = runtime.store.inference_of(link.judgment)
        assert inference.checker_id == "calculus.derivative.specialized"

    assert not B.free_symbols(session.object("E1").term) & set(
        runtime.request.parameters
    )
    assert runtime.variable in B.free_symbols(session.object("E1").term)
    assert session.object("E2").term == T.number(0)


def test_specialization_refusals_write_nothing():
    runtime = bootstrap_parameterized()
    session = Session(runtime)
    session.execute("expr F := a*x^2")
    before = runtime.store.stats()
    assert session.execute("specialize @F a=1").startswith("unsupported:")
    assert runtime.store.stats() == before

    session.execute("diff @F")
    links_before = session.workspace.links()
    with pytest.raises(SessionError):
        session.execute("specialize @F a=1/0")
    assert runtime.store.stats()["judgments"] == 1
    assert session.workspace.links() == links_before


def test_specialization_usage_is_refused_by_the_frontend():
    runtime = bootstrap_parameterized(("a", "b"))
    session = Session(runtime)
    session.execute("expr F := (a + b)*x^2")
    session.execute("diff @F")
    with pytest.raises(SessionError):
        session.execute("specialize @F")
    with pytest.raises(SessionError):
        session.execute("specialize @F a=1")
    with pytest.raises(SessionError):
        session.execute("specialize @F a=1 b=x")
    with pytest.raises(SessionError):
        session.execute("specialize @F a=1 a=2 b=3")
    with pytest.raises(SessionError):
        session.execute("specialize @F c=1 b=3")
    assert runtime.store.stats()["judgments"] == 1


def test_a_non_parameterized_runtime_has_no_specialization():
    session = Session(bootstrap())
    assert session.execute("specialize a=1") == (
        "unsupported: this runtime has no formal parameters"
    )


def test_specialization_joins_the_revision_history():
    runtime = bootstrap_parameterized()
    session = Session(runtime)
    session.execute("expr F := a*x^2")
    session.execute("diff @F")
    assert session.execute("specialize @F a=3") == "verified @E1: 6*x"
    assert runtime.store.stats()["judgments"] == 2

    assert session.execute("undo") == "undo: @E0"
    assert runtime.store.stats()["judgments"] == 2
    assert [label for label, _ in session.visible()] == ["F", "E0"]
    assert session.execute("redo") == "redo: @E1"
    assert len(session.workspace.links()) == 2


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
