"""Elementary differentiation through the frontend, workflow and kernel."""

from cas.frontend import Session
from cas.math.calculus.differentiation.elementary_checker import (
    ElementaryDerivativeCertificate,
)
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime import bootstrap_elementary
from cas.workflow.records import OperationStatus


def test_polynomials_remain_in_the_elementary_fragment():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    assert session.execute("x^3 - 3*x") == "@E0: x^3 - 3*x"
    assert session.execute("diff") == "verified @E1: -3 + 3*x^2"
    assert runtime.store.stats()["judgments"] == 1


def test_declared_function_laws_are_used_and_independently_checked():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    assert session.execute("sin(x)") == "@E0: sin(x)"
    assert session.execute("diff") == "verified @E1: cos(x)"

    link = session.workspace.links()[0]
    assert link.status is OperationStatus.VERIFIED
    assert link.judgment is not None
    claim = parse_has_derivative(
        runtime.vocabulary, link.specification.term
    )
    assert claim is not None
    assert claim.source == session.object("E0").term
    assert claim.candidate == session.object("E1").term

    inference = runtime.store.inference_of(link.judgment)
    assert inference.checker_id == "calculus.derivative.elementary"
    assert isinstance(
        inference.certificate, ElementaryDerivativeCertificate
    )
    assert runtime.elementary is not None
    assert inference.basis == (runtime.elementary.basis,)
    assert runtime.store.applicability(
        link.judgment, runtime.frame.id
    ).is_applicable()


def test_chain_rule_and_a_second_derivative():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("sin(x^2)")
    assert session.execute("diff") == "verified @E1: 2*cos(x^2)*x"
    assert session.execute("diff") == (
        "verified @E2: -4*sin(x^2)*x*x + 2*cos(x^2)"
    )
    assert runtime.store.stats()["judgments"] == 2


def test_constants_are_constants_not_undeclared_names():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("pi")
    assert session.execute("diff") == "verified @E1: 0"
    session.execute("exp(pi)")
    assert session.execute("diff") == "verified @E3: 0"


def test_conditional_laws_are_verified_on_their_region():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("sqrt(x)")
    assert session.execute("diff") == (
        "verified on x > 0 @E1: 1/2*sqrt(x)^-1"
    )
    session.execute("log(x)")
    assert session.execute("diff") == "verified on x > 0 @E3: x^-1"

    assert runtime.store.stats()["judgments"] == 2
    assert runtime.store.stats()["obligations"] == 0
    links = session.workspace.links()
    assert len(links) == 2
    for link in links:
        assert link.status is OperationStatus.VERIFIED
        assert link.condition is not None
        assert link.judgment is not None
        claim = parse_has_derivative(
            runtime.vocabulary, link.specification.term
        )
        assert claim is not None
        assert claim.region == link.condition.term
        candidate = session.workspace.candidate(link.candidate)
        assert candidate.problem.region == link.condition
        assert runtime.store.applicability(
            link.judgment, runtime.frame.id
        ).is_applicable()


def test_a_conditional_result_has_a_restricted_problem():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("sqrt(x)")
    result = session.differentiate(session.object("E0"))
    assert result.status is OperationStatus.CONDITIONAL
    assert result.condition is not None
    assert result.verification is not None
    assert result.verification.condition == result.condition
    assert result.candidate is not None
    assert result.candidate.problem.region == result.condition
    assert result.result is not None
    assert runtime.store.stats()["judgments"] == 1


def test_definedness_only_cases_and_empty_regions():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("sqrt(0)")
    assert session.execute("diff") == "verified @E1: 0"
    session.execute("sqrt(-1)")
    before = runtime.store.stats()
    output = session.execute("diff")
    assert output.startswith("unsupported:")
    assert runtime.store.stats() == before
    session.execute("log(0)")
    assert session.execute("diff").startswith("unsupported:")
    assert runtime.store.stats() == before


def test_negative_powers_and_unknown_symbols_are_refused():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("1/x")
    assert session.execute("diff").startswith("unsupported:")
    session.execute("y")
    output = session.execute("diff")
    assert output.startswith("unsupported:")
    assert "dependency contract" in output
    assert runtime.store.stats()["judgments"] == 0


def test_specialization_is_not_available_without_parameters():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    assert session.execute("specialize a=1") == (
        "unsupported: this runtime has no formal parameters"
    )


def test_the_elementary_revision_history_keeps_the_ledger():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("cos(x)")
    session.execute("diff")
    assert runtime.store.stats()["judgments"] == 1
    assert session.execute("undo") == "undo: @E0"
    assert runtime.store.stats()["judgments"] == 1
    assert session.execute("redo") == "redo: @E1"
    assert len(session.workspace.links()) == 1
