"""Workspace: expression objects, candidates, verification links and history."""

from fractions import Fraction

from support import head_app, variable

from cas.language import sorts as S
from cas.language.signatures import StructuralHead
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


def unsupported_term(runtime) -> T.Apply:
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(-1),
    )


def expected_derivative(runtime):
    ring = runtime.ring
    return ring.sub(
        ring.mul_int(ring.monomial((2,), Fraction(1)), 3),
        ring.constant(Fraction(3)),
    )


def test_the_workspace_starts_with_an_empty_revision(runtime):
    workspace = new_workspace(runtime)
    assert workspace.expressions() == ()
    assert workspace.links() == ()
    assert workspace.events() == ()
    assert not workspace.undo()
    assert not workspace.redo()


def test_intake_records_an_expression_without_a_judgment(runtime):
    workspace = new_workspace(runtime)
    term = source_term(runtime)
    expression = workspace.intake(term, "source")
    assert expression.term is term
    assert expression.frame == runtime.frame.id
    assert expression.label == "source"
    assert workspace.expressions() == (expression,)
    assert workspace.links() == ()
    assert [event.operation for event in workspace.events()] == ["Intake"]
    assert workspace.revision.label == "intake source"
    assert runtime.store.stats()["judgments"] == 0


def test_differentiation_produces_a_verified_candidate_and_result(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.detail == ""
    assert result.candidate is not None
    assert result.verification is not None
    assert result.result is not None
    link = result.verification
    assert link.status is OperationStatus.VERIFIED
    assert link.judgment is not None
    assert link.candidate == result.candidate.id
    assert workspace.candidate(link.candidate) is result.candidate
    assert workspace.applicability(link.judgment).is_applicable()
    assert runtime.store.stats()["judgments"] == 1

    candidate = result.candidate
    assert candidate.problem.operation == "differentiate"
    assert candidate.problem.inputs == (source.term,)
    assert candidate.problem.target == runtime.variable
    assert candidate.problem.target_sort is S.REAL
    assert candidate.problem.coverage.value == "one_verified"
    assert candidate.problem.result_language.value == "expression"
    assert candidate.frame == runtime.frame.id

    claim = parse_has_derivative(
        runtime.vocabulary, link.specification.term
    )
    assert claim is not None
    assert claim.region == T.TRUE
    assert claim.source == source.term
    assert claim.variable.symbol_id == runtime.variable
    assert claim.candidate == result.result.term
    assert link.specification.meaning == runtime.frame.meaning

    value = to_polynomial(
        runtime.ring, result.result.term, runtime.signature
    )
    assert value is not None
    assert runtime.ring.equal(value, expected_derivative(runtime))
    assert [event.operation for event in workspace.events()] == [
        "Intake",
        "Differentiate",
    ]
    assert len(workspace.links()) == 1


def test_outside_the_fragment_the_workspace_refuses_without_writing(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(unsupported_term(runtime), "reciprocal")
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.candidate is None
    assert result.verification is None
    assert result.result is None
    assert "polynomial fragment" in result.detail
    assert runtime.store.stats()["judgments"] == 0
    assert [event.operation for event in workspace.events()] == ["Intake"]
    assert workspace.revision.label == "intake reciprocal"


def test_another_variable_is_refused_without_writing(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    y = runtime.table.intern("y")
    result = workspace.differentiate(source, y)
    assert result.status is OperationStatus.UNSUPPORTED
    assert "x only" in result.detail
    assert result.candidate is None
    assert runtime.store.stats()["judgments"] == 0


def test_undo_and_redo_move_the_view_but_not_the_ledger(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    result = workspace.differentiate(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert len(workspace.expressions()) == 2
    judgment = result.verification.judgment

    assert workspace.undo()
    assert workspace.expressions() == (source,)
    assert workspace.links() == ()
    assert runtime.store.get_judgment(judgment).proposition is not None

    assert workspace.undo()
    assert workspace.expressions() == ()
    assert not workspace.undo()

    assert workspace.redo()
    assert workspace.redo()
    assert len(workspace.expressions()) == 2
    assert len(workspace.links()) == 1
    assert not workspace.redo()
    assert runtime.store.stats()["judgments"] == 1


def test_a_new_operation_after_undo_truncates_the_redo_branch(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime), "source")
    workspace.differentiate(source, runtime.variable)
    assert workspace.undo()
    replacement = workspace.intake(T.number(7), "replacement")
    assert not workspace.redo()
    assert workspace.expressions() == (source, replacement)
    assert workspace.links() == ()
    assert [event.operation for event in workspace.events()] == [
        "Intake",
        "Intake",
    ]
    assert runtime.store.stats()["judgments"] == 1


def test_each_differentiation_gets_its_own_candidate_and_judgment(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(source_term(runtime))
    first = workspace.differentiate(source, runtime.variable)
    second = workspace.differentiate(source, runtime.variable)
    assert first.candidate.id != second.candidate.id
    assert first.verification.judgment != second.verification.judgment
    assert runtime.store.stats()["judgments"] == 2
    assert len(workspace.links()) == 2
    assert len(workspace.expressions()) == 3
