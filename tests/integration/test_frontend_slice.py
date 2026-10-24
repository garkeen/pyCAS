"""The frontend slice: text -> term -> candidate -> published judgment."""

from cas.frontend.session import Session
from cas.math.calculus.differentiation.certificate import DerivativeCertificate
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.workflow.records import OperationStatus


def test_text_goes_through_the_whole_trust_boundary(runtime):
    session = Session(runtime)
    assert session.execute("x^3 - 3*x") == "@E0: x^3 - 3*x"
    assert runtime.store.stats()["judgments"] == 0
    assert session.execute("diff") == "verified @E1: -3 + 3*x^2"

    link = session.workspace.links()[0]
    assert link.status is OperationStatus.VERIFIED
    assert link.judgment is not None
    judgment = runtime.store.get_judgment(link.judgment)
    assert judgment.proposition == link.specification
    assert runtime.store.applicability(
        judgment.id, runtime.frame.id
    ).is_applicable()

    claim = parse_has_derivative(
        runtime.vocabulary, link.specification.term
    )
    assert claim is not None
    assert claim.source == session.object("E0").term
    assert claim.candidate == session.object("E1").term
    assert claim.variable.symbol_id == runtime.variable

    inference = runtime.store.inference_of(judgment.id)
    assert inference.checker_id == "calculus.derivative"
    certificate = inference.certificate
    assert isinstance(certificate, DerivativeCertificate)
    assert certificate.source == claim.source
    assert certificate.candidate == claim.candidate


def test_a_text_refusal_leaves_no_trust_behind(runtime):
    session = Session(runtime)
    session.execute("expr R := 1/x")
    before = runtime.store.stats()
    assert session.execute("diff @R").startswith("unsupported:")
    assert runtime.store.stats() == before
    assert session.workspace.links() == ()


def test_undo_through_the_frontend_keeps_the_ledger(runtime):
    session = Session(runtime)
    session.execute("x^2")
    session.execute("diff")
    judgment = session.workspace.links()[0].judgment
    assert session.execute("undo") == "undo: @E0"
    assert runtime.store.get_judgment(judgment) is not None
    assert runtime.store.stats()["judgments"] == 1
    assert session.execute("redo") == "redo: @E1"
    assert len(session.workspace.links()) == 1


def test_a_second_derivative_is_a_fresh_verified_object(runtime):
    session = Session(runtime)
    session.execute("x^3")
    session.execute("diff")
    assert session.execute("diff") == "verified @E2: 6*x"
    assert runtime.store.stats()["judgments"] == 2
    assert len(session.workspace.links()) == 2
