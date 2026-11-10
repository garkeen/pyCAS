"""Resultants: operation, integer-Bareiss checker and refusals."""

from fractions import Fraction

from support import (
    runtime_proposition,
    variable,
    verification_context,
)

from cas.frontend import parse
from cas.frontend.session import Session
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Verified,
)
from cas.language.roles import CandidateRole
from cas.math.algebra.resultant_checker import ResultantChecker
from cas.math.algebra.resultant_specification import (
    ResultantCertificate,
    ResultantVocabulary,
    has_resultant,
)
from cas.runtime.bootstrap import bootstrap, new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus


def polynomial(runtime, expression):
    return parse(expression, runtime.table, runtime.signature)


def test_resultant_operation_computes_the_expected_values(runtime):
    workspace = new_workspace(runtime)
    left = workspace.intake(polynomial(runtime, "x^2 + 1"), "left")
    right = workspace.intake(polynomial(runtime, "x + 1"), "right")
    result = workspace.resultant(left, right, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.result.term == T.number(2)
    zero_left = workspace.intake(polynomial(runtime, "x^2 - 1"), "zero-left")
    zero_right = workspace.intake(polynomial(runtime, "x - 1"), "zero-right")
    zero = workspace.resultant(zero_left, zero_right, runtime.variable)
    assert zero.status is OperationStatus.VERIFIED
    assert zero.result is not None
    assert zero.result.term == T.number(0)


def test_resultant_handles_rational_coefficients(runtime):
    workspace = new_workspace(runtime)
    left = workspace.intake(polynomial(runtime, "1/2*x + 1"), "left")
    right = workspace.intake(polynomial(runtime, "x + 1"), "right")
    result = workspace.resultant(left, right, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.result.term == T.number(Fraction(-1, 2))


def test_resultant_refuses_non_polynomial_inputs(runtime):
    workspace = new_workspace(runtime)
    reciprocal = workspace.intake(polynomial(runtime, "1/x"), "reciprocal")
    other = workspace.intake(polynomial(runtime, "x"), "other")
    result = workspace.resultant(reciprocal, other, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED


def vocabulary_for(runtime):
    symbol = runtime.table.lookup("HasResultant")
    assert symbol is not None
    return ResultantVocabulary(symbol, "HasResultant")


def checker_for(runtime):
    spec = runtime.store.checkers.spec("algebra.resultant")
    assert spec is not None
    checker = spec.checker
    assert isinstance(checker, ResultantChecker)
    return checker


def test_the_checker_refutes_a_wrong_resultant():
    runtime = bootstrap()
    vocabulary = vocabulary_for(runtime)
    left = polynomial(runtime, "x^2 + 1")
    right = polynomial(runtime, "x + 1")
    wrong = T.number(3)
    issued = runtime_proposition(
        runtime,
        has_resultant(
            vocabulary, left, right, variable(runtime), wrong
        ),
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            ResultantCertificate(
                left, right, runtime.variable, wrong
            ),
            candidate=wrong,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Refuted)
    correct = T.number(2)
    issued = runtime_proposition(
        runtime,
        has_resultant(
            vocabulary, left, right, variable(runtime), correct
        ),
    )
    good = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            ResultantCertificate(
                left, right, runtime.variable, correct
            ),
            candidate=correct,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(good, Verified)


def test_the_checker_requires_the_candidate_role():
    runtime = bootstrap()
    vocabulary = vocabulary_for(runtime)
    left = polynomial(runtime, "x^2 + 1")
    right = polynomial(runtime, "x + 1")
    correct = T.number(2)
    issued = runtime_proposition(
        runtime,
        has_resultant(
            vocabulary, left, right, variable(runtime), correct
        ),
    )
    certificate = ResultantCertificate(
        left, right, runtime.variable, correct
    )
    for role in (None, CandidateRole.SOURCE):
        outcome = checker_for(runtime).check(
            CheckRequest(
                runtime.frame.id,
                (issued,),
                (),
                certificate,
                candidate=correct,
                candidate_role=role,
                context=verification_context(runtime, algebra=runtime.request),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate role" in outcome.detail
    for candidate in (None, T.number(3)):
        outcome = checker_for(runtime).check(
            CheckRequest(
                runtime.frame.id,
                (issued,),
                (),
                certificate,
                candidate=candidate,
                candidate_role=CandidateRole.RESULT,
                context=verification_context(runtime, algebra=runtime.request),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate" in outcome.detail


def test_the_session_resultant_command(runtime):
    session = Session(bootstrap())
    session.execute("x^2 + 1")
    session.execute("x + 1")
    answer = session.execute("resultant @E0 @E1")
    assert answer.startswith("verified @")
