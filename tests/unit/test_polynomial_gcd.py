"""Polynomial gcd: operation, independent Bezout checker and refusals."""

from support import (
    head_app,
    render_value,
    runtime_proposition,
    typed_in,
    variable,
    verification_context,
    view_of,
)

from cas.frontend.session import Session
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Verified,
)
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.language.signatures import StructuralHead
from cas.math.algebra.gcd_checker import PolynomialGcdChecker
from cas.math.algebra.gcd_specification import (
    GcdCertificate,
    GcdVocabulary,
    has_gcd,
)
from cas.runtime.bootstrap import bootstrap, new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus


def polynomial(runtime, expression):
    from cas.frontend import parse

    return parse(expression, runtime.table, runtime.signature)


def test_gcd_operation_returns_the_monic_common_divisor(runtime):
    workspace = new_workspace(runtime)
    left = workspace.intake(polynomial(runtime, "x^2 - 1"), "left")
    right = workspace.intake(polynomial(runtime, "x - 1"), "right")
    result = workspace.gcd(left, right, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.candidate is not None
    assert result.verifications[0].judgment is not None


def test_gcd_of_coprime_and_zero_inputs(runtime):
    workspace = new_workspace(runtime)
    left = workspace.intake(polynomial(runtime, "x^2 + 1"), "left")
    right = workspace.intake(polynomial(runtime, "x + 1"), "right")
    result = workspace.gcd(left, right, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.result.term == T.number(1)
    zero = workspace.intake(T.number(0), "zero")
    other = workspace.intake(polynomial(runtime, "x - 1"), "other")
    with_zero = workspace.gcd(zero, other, runtime.variable)
    assert with_zero.status is OperationStatus.VERIFIED
    both_zero = workspace.gcd(zero, zero, runtime.variable)
    assert both_zero.status is OperationStatus.VERIFIED
    assert both_zero.result is not None
    assert both_zero.result.term == T.number(0)


def test_gcd_refuses_non_polynomial_inputs(runtime):
    workspace = new_workspace(runtime)
    reciprocal = workspace.intake(
        head_app(
            runtime.signature,
            StructuralHead.POWER,
            variable(runtime),
            T.number(-1),
        ),
        "reciprocal",
    )
    other = workspace.intake(polynomial(runtime, "x"), "other")
    result = workspace.gcd(reciprocal, other, runtime.variable)
    assert result.status is OperationStatus.UNSUPPORTED


def vocabulary_for(runtime):
    symbol = runtime.table.lookup("HasPolynomialGCD")
    assert symbol is not None
    return GcdVocabulary(symbol, "HasPolynomialGCD")


def checker_for(runtime):
    spec = runtime.store.checkers.spec("algebra.polynomial_gcd")
    assert spec is not None
    checker = spec.checker
    assert isinstance(checker, PolynomialGcdChecker)
    return checker


def test_the_checker_refutes_a_non_divisor_and_rejects_a_bad_bezout():
    runtime = bootstrap()
    vocabulary = vocabulary_for(runtime)
    left = polynomial(runtime, "x^2 - 1")
    right = polynomial(runtime, "x - 1")
    wrong = polynomial(runtime, "x^2 + 1")
    left_value = view_of(runtime, left).value
    right_value = view_of(runtime, right).value
    _, first, second = runtime.ring.xgcd(left_value, right_value)
    first_term = render_value(runtime, first)
    second_term = render_value(runtime, second)
    issued = runtime_proposition(
        runtime,
        has_gcd(
            vocabulary,
            left,
            right,
            variable(runtime),
            wrong,
        ),
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            GcdCertificate(
                left,
                right,
                runtime.variable,
                wrong,
                first_term,
                second_term,
            ),
            candidate=wrong,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Refuted)
    correct = polynomial(runtime, "x - 1")
    issued = runtime_proposition(
        runtime,
        has_gcd(
            vocabulary,
            left,
            right,
            variable(runtime),
            correct,
        ),
    )
    bad = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            GcdCertificate(
                left,
                right,
                runtime.variable,
                correct,
                T.number(0),
                T.number(0),
            ),
            candidate=correct,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(bad, InvalidEvidence)
    good = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            GcdCertificate(
                left,
                right,
                runtime.variable,
                correct,
                first_term,
                second_term,
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
    left = polynomial(runtime, "x^2 - 1")
    right = polynomial(runtime, "x - 1")
    correct = polynomial(runtime, "x - 1")
    left_value = view_of(runtime, left).value
    right_value = view_of(runtime, right).value
    _, first, second = runtime.ring.xgcd(left_value, right_value)
    issued = runtime_proposition(
        runtime,
        has_gcd(
            vocabulary,
            left,
            right,
            variable(runtime),
            correct,
        ),
    )
    certificate = GcdCertificate(
        left,
        right,
        runtime.variable,
        correct,
        render_value(runtime, first),
        render_value(runtime, second),
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
    for candidate in (None, left):
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


def test_the_session_gcd_command(runtime):
    session = Session(bootstrap())
    session.execute("x^2 - 1")
    session.execute("x - 1")
    answer = session.execute("gcd @E0 @E1")
    assert answer.startswith("verified @")


def gcd_fixture(runtime):
    vocabulary = vocabulary_for(runtime)
    left = polynomial(runtime, "x^2 - 1")
    right = polynomial(runtime, "x - 1")
    correct = polynomial(runtime, "x - 1")
    _, first, second = runtime.ring.xgcd(
        view_of(runtime, left).value,
        view_of(runtime, right).value,
    )
    certificate = GcdCertificate(
        left,
        right,
        runtime.variable,
        correct,
        render_value(runtime, first),
        render_value(runtime, second),
    )
    issued = runtime_proposition(
        runtime,
        has_gcd(
            vocabulary, left, right, variable(runtime), correct
        ),
    )
    return vocabulary, left, right, correct, certificate, issued


def gcd_problem(runtime, inputs, roles=None):
    return ProblemSpec(
        "polynomial_gcd",
        tuple(inputs),
        runtime.request.roles if roles is None else roles,
        None,
        ResultLanguage.EXPRESSION,
        Coverage.ONE_VERIFIED,
        interpretation_requirement=(
            runtime.request.interpretation_requirement
        ),
        domain_requirement=DomainRequirement(
            coefficient=runtime.request.coefficient_domain,
            values=runtime.request.value_domain,
        ),
    )


def test_a_math_checker_requires_a_trusted_verification_context():
    runtime = bootstrap()
    _, left, right, correct, certificate, issued = gcd_fixture(runtime)
    problem = gcd_problem(
        runtime,
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                left,
            ),
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                right,
            ),
        ),
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=correct,
            candidate_role=CandidateRole.RESULT,
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "the check request has no trusted verification context"
    )


def test_a_problem_input_from_another_world_is_refused():
    runtime = bootstrap()
    foreign = bootstrap()
    _, left, right, correct, certificate, issued = gcd_fixture(runtime)
    foreign_term = polynomial(foreign, "x^2 - 1")
    problem = gcd_problem(
        runtime,
        (
            typed_in(
                foreign.frames,
                foreign.frame.id,
                foreign.signature,
                foreign_term,
            ),
        ),
        roles=foreign.request.roles,
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=correct,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "a problem input belongs to another meaning world"
    )


def test_a_problem_input_from_an_unrelated_frame_is_refused():
    runtime = bootstrap()
    sibling = runtime.frames.create(runtime.frames.root.id)
    _, left, right, correct, certificate, issued = gcd_fixture(runtime)
    problem = gcd_problem(
        runtime,
        (
            typed_in(
                runtime.frames,
                sibling.id,
                runtime.signature,
                T.number(1),
            ),
        ),
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=correct,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert outcome.detail == (
        "a problem input belongs to a frame outside the verification "
        "context"
    )


def test_a_problem_input_from_the_verification_frame_is_accepted():
    runtime = bootstrap()
    _, left, right, correct, certificate, issued = gcd_fixture(runtime)
    problem = gcd_problem(
        runtime,
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                left,
            ),
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                right,
            ),
        ),
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=correct,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Verified)


def test_a_problem_input_from_a_visible_ancestor_frame_is_accepted():
    runtime = bootstrap()
    child = runtime.frames.create(runtime.frame.id)
    vocabulary, left, right, correct, certificate, _ = gcd_fixture(runtime)
    issued = runtime_proposition(
        runtime,
        has_gcd(
            vocabulary, left, right, variable(runtime), correct
        ),
        child.id,
    )
    problem = gcd_problem(
        runtime,
        (
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                left,
            ),
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                right,
            ),
        ),
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            child.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=correct,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(
                runtime, child.id, algebra=runtime.request
            ),
        )
    )
    assert isinstance(outcome, Verified)
