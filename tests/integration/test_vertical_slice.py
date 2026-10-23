"""The first vertical slice, end to end.

Expression object -> derivative candidate -> exact specification -> independent
checker -> kernel publication -> verification link -> undo/redo.
"""

from support import head_app, variable

from cas.language.signatures import StructuralHead
from cas.math.calculus.differentiation.checker import DerivativeCertificate
from cas.math.calculus.differentiation.specification import parse_has_derivative
from cas.runtime.bootstrap import new_workspace
from cas.semantics.bridge import to_polynomial
from cas.syntax import term as T
from cas.workflow.records import OperationStatus


def source_term(runtime) -> T.Apply:
    x = variable(runtime)
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature, StructuralHead.POWER, x, T.number(3)
        ),
        head_app(
            runtime.signature, StructuralHead.TIMES, T.number(-3), x
        ),
    )


def test_intake_stores_data_and_creates_no_judgment(runtime):
    workspace = new_workspace(runtime)
    expression = workspace.intake(source_term(runtime), "source")
    assert runtime.store.stats()["judgments"] == 0
    assert runtime.store.stats()["inferences"] == 0
    assert expression in workspace.expressions()
    assert workspace.links() == ()


def test_the_slice_publishes_exactly_one_checked_judgment(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.candidate is not None
    assert result.verification is not None
    assert result.result is not None
    link = result.verification
    assert link.judgment is not None

    judgment = runtime.store.get_judgment(link.judgment)
    assert judgment.proposition == link.specification
    assert judgment.frame == runtime.frame.id
    assert judgment.obligations == ()
    assert runtime.store.applicability(
        judgment.id, runtime.frame.id
    ).is_applicable()
    assert runtime.store.support(judgment.id) == frozenset()

    inference = runtime.store.inference_of(judgment.id)
    assert inference.checker_id == "calculus.derivative"
    assert inference.checker_version == "1"
    assert inference.premises == ()
    assert inference.conclusions == (judgment.id,)
    certificate = inference.certificate
    assert isinstance(certificate, DerivativeCertificate)
    assert certificate.source == source.term
    assert certificate.candidate == result.result.term
    assert certificate.variable == runtime.variable
    assert certificate.region == T.TRUE

    claim = parse_has_derivative(
        runtime.vocabulary, link.specification.term
    )
    assert claim is not None
    assert claim.source == source.term
    assert claim.candidate == result.result.term
    assert claim.variable.symbol_id == runtime.variable
    assert runtime.store.stats() == {
        "frames": runtime.frames.count(),
        "obligations": 0,
        "judgments": 1,
        "inferences": 1,
        "discharges": 0,
    }


def test_undo_hides_the_view_but_never_rolls_back_the_ledger(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    result = workspace.differentiate(source, runtime.variable)
    judgment = result.verification.judgment
    assert workspace.undo()
    assert workspace.expressions() == (source,)
    assert workspace.links() == ()
    assert runtime.store.stats()["judgments"] == 1
    assert runtime.store.get_judgment(judgment) is not None
    assert workspace.redo()
    assert len(workspace.expressions()) == 2
    assert len(workspace.links()) == 1


def test_outside_the_fragment_nothing_becomes_trusted(runtime):
    workspace = new_workspace(runtime)
    reciprocal = head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(-1),
    )
    source = workspace.intake(reciprocal, "reciprocal")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.candidate is None
    assert result.verification is None
    assert result.result is None
    assert runtime.store.stats()["judgments"] == 0
    assert runtime.store.stats()["inferences"] == 0
    assert workspace.links() == ()
    assert [event.operation for event in workspace.events()] == ["Intake"]


def test_a_second_derivative_is_a_new_judgment(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    first = workspace.differentiate(source, runtime.variable)
    assert first.status is OperationStatus.VERIFIED
    second = workspace.differentiate(first.result, runtime.variable)
    assert second.status is OperationStatus.VERIFIED
    value = to_polynomial(
        runtime.ring, second.result.term, runtime.signature
    )
    assert value is not None
    x_squared = runtime.ring.monomial((1,), 6)
    assert runtime.ring.equal(value, x_squared)
    assert runtime.store.stats()["judgments"] == 2
    assert len(workspace.links()) == 2
