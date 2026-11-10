"""The registered real-root-isolation operation and its independent checker."""

from fractions import Fraction

import pytest
from support import runtime_proposition, verification_context

from cas.frontend import parse
from cas.frontend.session import Session
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Unverified,
    Verified,
)
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.problems import Coverage
from cas.language.roles import CandidateRole
from cas.language.sets import set_members, set_term
from cas.math.algebra.root_isolation_checker import RootIsolationChecker
from cas.math.algebra.root_isolation_specification import (
    RootIsolationCertificate,
    RootIsolationVocabulary,
    has_root_isolation,
)
from cas.runtime.bootstrap import (
    bootstrap,
    bootstrap_elementary,
    bootstrap_parameterized,
    new_workspace,
)
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState


def polynomial(runtime, expression):
    return parse(expression, runtime.table, runtime.signature)


def q(value, denominator=1):
    return Fraction(value, denominator)


def isolation_vocabulary(runtime):
    symbol = runtime.table.lookup("HasRootIsolation")
    interval_symbol = runtime.table.lookup("Interval")
    assert symbol is not None
    assert interval_symbol is not None
    return RootIsolationVocabulary(
        symbol, "HasRootIsolation", interval_symbol
    )


def checker_for(runtime):
    spec = runtime.store.checkers.spec("algebra.root_isolation")
    assert spec is not None
    checker = spec.checker
    assert isinstance(checker, RootIsolationChecker)
    return checker


def interval_term(runtime, lower, upper):
    return isolation_vocabulary(runtime).interval(
        T.number(lower), T.number(upper)
    )


def interval_set(runtime, pairs):
    return set_term(
        runtime.signature,
        tuple(interval_term(runtime, lower, upper) for lower, upper in pairs),
    )


def isolation_claim(runtime, source, intervals):
    issued = runtime_proposition(
        runtime,
        has_root_isolation(
            isolation_vocabulary(runtime), source, intervals
        ),
    )
    return issued


def isolate_fixture(runtime, source_text):
    workspace = new_workspace(runtime)
    source = workspace.intake(
        polynomial(runtime, source_text), "source"
    )
    result = workspace.isolate_roots(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    return workspace, source, result, candidate


def check(
    runtime,
    issued,
    certificate,
    candidate,
    *,
    problem=None,
    role=CandidateRole.RESULT,
):
    return checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=candidate,
            candidate_role=role,
            context=verification_context(
                runtime, algebra=runtime.request
            ),
        )
    )


def test_isolate_roots_returns_two_intervals_for_x_squared_minus_two():
    runtime = bootstrap()
    _, source, result, candidate = isolate_fixture(runtime, "x^2 - 2")
    members = set_members(result.result.term, runtime.signature)
    assert members is not None
    assert len(members) == 2
    for member in members:
        assert isinstance(member, T.Apply)
        assert isinstance(member.operator, T.SymbolRef)
        assert member.operator.symbol_id == runtime.table.lookup("Interval")
        assert len(member.arguments) == 2
    assert result.result.term == candidate.term
    assert candidate.specifications
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED
    assert result.task.problem.coverage is Coverage.COMPLETE_SET
    assert result.verifications[0].judgment is not None


def test_isolate_roots_returns_the_empty_set_for_no_real_roots():
    runtime = bootstrap()
    _, _, result, _ = isolate_fixture(runtime, "x^2 + 1")
    assert result.result is not None
    assert set_members(result.result.term, runtime.signature) == ()


def test_isolate_roots_returns_one_interval_containing_a_rational_root():
    runtime = bootstrap()
    _, _, result, _ = isolate_fixture(runtime, "x")
    assert result.result is not None
    members = set_members(result.result.term, runtime.signature)
    assert members is not None
    assert len(members) == 1
    member = members[0]
    assert isinstance(member, T.Apply)
    lower, upper = member.arguments
    assert isinstance(lower, T.IntLit) and isinstance(upper, T.IntLit)
    assert lower.value < 0 < upper.value


def test_isolate_roots_returns_the_empty_set_for_a_nonzero_constant():
    runtime = bootstrap()
    _, _, result, _ = isolate_fixture(runtime, "7")
    assert result.result is not None
    assert set_members(result.result.term, runtime.signature) == ()


def test_isolate_roots_refuses_non_squarefree_and_zero_polynomials():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    for text, missing in (
        ("(x - 1)^2", {"squarefree_polynomial"}),
        ("0", {"nonzero_polynomial"}),
    ):
        source = workspace.intake(polynomial(runtime, text), "source")
        before = runtime.store.stats()
        result = workspace.isolate_roots(source, runtime.variable)
        assert result.status is OperationStatus.UNSUPPORTED
        assert result.blocker is not None
        assert result.blocker.missing == frozenset(missing)
        assert result.candidate is None
        assert runtime.store.stats() == before
        assert workspace.candidates() == ()


def test_isolate_roots_refuses_a_restricted_region():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x^2 - 2"), "source")
    region = runtime_proposition(runtime, polynomial(runtime, "x > 0"))
    before = runtime.store.stats()
    result = workspace.apply(
        "isolate_roots",
        (source,),
        target=runtime.variable,
        region=region,
        coverage=Coverage.COMPLETE_SET,
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"restricted_region"})
    assert runtime.store.stats() == before


def test_isolate_roots_reports_budget_exhaustion_without_a_partial_set(
    runtime, monkeypatch
):
    import cas.math.algebra.root_isolation_operation as module

    monkeypatch.setattr(module, "_ROOT_ISOLATION_SPLIT_BUDGET", 0)
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x^2 - 2"), "source")
    before = runtime.store.stats()
    result = workspace.isolate_roots(source, runtime.variable)
    assert result.status is OperationStatus.UNKNOWN
    assert result.blocker is not None
    assert result.blocker.reason.value == "budget"
    assert result.blocker.missing == frozenset({"root_isolation_budget"})
    assert result.result is None
    assert result.candidate is None
    assert runtime.store.stats() == before


def test_isolate_roots_is_not_registered_in_the_parameterized_runtime():
    assert bootstrap_parameterized().operations.get("isolate_roots") is None


def test_isolate_roots_is_registered_in_the_elementary_runtime():
    runtime = bootstrap_elementary()
    _, _, result, _ = isolate_fixture(runtime, "x^2 - 2")
    assert result.result is not None
    members = set_members(result.result.term, runtime.signature)
    assert members is not None and len(members) == 2


@pytest.mark.parametrize(
    ("source_text", "missing"),
    [
        ("(x - 1)^2", frozenset({"squarefree_polynomial"})),
        ("0", frozenset({"nonzero_polynomial"})),
    ],
)
def test_define_problem_blocks_isolate_roots_out_of_fragment(
    runtime, source_text, missing
):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, source_text), "source")
    before = runtime.store.stats()
    task = workspace.define_problem(
        "isolate_roots",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None
    assert task.blocker.missing == missing
    assert runtime.store.stats() == before


def test_run_task_refuses_an_isolation_problem_blocked_at_definition(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "(x - 1)^2"), "source")
    task = workspace.define_problem(
        "isolate_roots",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.BLOCKED
    before = runtime.store.stats()
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.INVALID
    assert result.candidate is None
    assert runtime.store.stats() == before


def test_a_manual_isolation_task_runs(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x^2 - 2"), "source")
    task = workspace.define_problem(
        "isolate_roots",
        (source,),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.READY
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    members = set_members(result.result.term, runtime.signature)
    assert members is not None and len(members) == 2


def test_the_checker_verifies_the_operational_isolation():
    runtime = bootstrap()
    _, _, result, candidate = isolate_fixture(runtime, "x^2 - 2")
    issued = candidate.specifications[0]
    outcome = check(
        runtime,
        issued,
        candidate.certificate,
        candidate.term,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Verified)


def test_the_checker_verifies_an_empty_interval_set():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 + 1")
    outcome = check(
        runtime,
        candidate.specifications[0],
        candidate.certificate,
        candidate.term,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Verified)


def test_the_checker_refutes_an_interval_with_two_roots():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(
        runtime, "(x - 1)*(x - 2)"
    )
    intervals = interval_set(runtime, ((-3, 3),))
    issued = isolation_claim(runtime, candidate.problem.inputs[0].term, intervals)
    outcome = check(
        runtime,
        issued,
        candidate.certificate,
        intervals,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Refuted)
    assert "exactly one" in outcome.detail


def test_the_checker_refutes_an_interval_with_no_root():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    intervals = interval_set(runtime, ((-1, 1),))
    issued = isolation_claim(runtime, candidate.problem.inputs[0].term, intervals)
    outcome = check(
        runtime,
        issued,
        candidate.certificate,
        intervals,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Refuted)


def test_the_checker_refutes_a_missing_root():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(
        runtime, "(x - 1)*(x - 2)"
    )
    intervals = interval_set(runtime, ((0, q(3, 2)),))
    issued = isolation_claim(runtime, candidate.problem.inputs[0].term, intervals)
    outcome = check(
        runtime,
        issued,
        candidate.certificate,
        intervals,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Refuted)
    assert "cover" in outcome.detail


def test_the_checker_refutes_overlapping_intervals():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(
        runtime, "(x - 1)*(x - 2)"
    )
    intervals = interval_set(
        runtime, ((0, q(3, 2)), (q(5, 4), q(5, 2)))
    )
    issued = isolation_claim(runtime, candidate.problem.inputs[0].term, intervals)
    outcome = check(
        runtime,
        issued,
        candidate.certificate,
        intervals,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Refuted)
    assert "overlap" in outcome.detail


def test_the_checker_refutes_an_interval_outside_the_certified_bound():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    intervals = interval_set(runtime, ((6, 7),))
    issued = isolation_claim(runtime, candidate.problem.inputs[0].term, intervals)
    outcome = check(
        runtime,
        issued,
        candidate.certificate,
        intervals,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Refuted)
    assert "outside" in outcome.detail


def test_the_checker_reports_a_nonrational_interval_endpoint_as_a_fragment():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    variable = T.symbol(runtime.variable, "x")
    intervals = set_term(
        runtime.signature,
        (
            T.app(
                T.symbol(
                    runtime.table.lookup("Interval"), "Interval"
                ),
                variable,
                T.number(2),
            ),
        ),
    )
    issued = isolation_claim(runtime, candidate.problem.inputs[0].term, intervals)
    outcome = check(
        runtime,
        issued,
        candidate.certificate,
        intervals,
        problem=candidate.problem,
    )
    assert isinstance(outcome, Unverified)
    assert outcome.missing == frozenset({"rational_endpoint"})


def test_the_checker_rejects_a_bound_below_cauchy():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    certificate = candidate.certificate
    assert isinstance(certificate, RootIsolationCertificate)
    wrong = RootIsolationCertificate(
        certificate.polynomial, T.number(1), certificate.chain
    )
    outcome = check(
        runtime,
        candidate.specifications[0],
        wrong,
        candidate.term,
        problem=candidate.problem,
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "Cauchy" in outcome.detail


def test_the_checker_rejects_a_tampered_chain():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    certificate = candidate.certificate
    assert isinstance(certificate, RootIsolationCertificate)
    tampered = RootIsolationCertificate(
        certificate.polynomial,
        certificate.bound,
        (certificate.chain[0], T.number(7)),
    )
    outcome = check(
        runtime,
        candidate.specifications[0],
        tampered,
        candidate.term,
        problem=candidate.problem,
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "derivative" in outcome.detail


def test_the_checker_rejects_a_certificate_for_another_polynomial():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    _, _, _, other = isolate_fixture(runtime, "x^2 - 3")
    outcome = check(
        runtime,
        candidate.specifications[0],
        other.certificate,
        candidate.term,
        problem=candidate.problem,
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "certificate does not match" in outcome.detail


def test_the_checker_rejects_a_candidate_that_does_not_match_the_claim():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    outcome = check(
        runtime,
        candidate.specifications[0],
        candidate.certificate,
        set_term(runtime.signature, ()),
        problem=candidate.problem,
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "candidate does not match" in outcome.detail


def test_the_checker_rejects_a_mismatched_problem():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    _, _, _, other = isolate_fixture(runtime, "x^2 - 3")
    outcome = check(
        runtime,
        other.specifications[0],
        other.certificate,
        other.term,
        problem=candidate.problem,
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "problem inputs" in outcome.detail


def test_the_checker_reports_a_non_squarefree_complete_chain_as_a_fragment():
    runtime = bootstrap()
    source = polynomial(runtime, "(x - 1)^2")
    derivative = polynomial(runtime, "2*x - 2")
    intervals = set_term(runtime.signature, ())
    issued = isolation_claim(runtime, source, intervals)
    certificate = RootIsolationCertificate(
        source, T.number(4), (source, derivative)
    )
    outcome = check(runtime, issued, certificate, intervals)
    assert isinstance(outcome, Unverified)
    assert outcome.missing == frozenset({"squarefree_polynomial"})


def test_the_checker_reports_the_zero_polynomial_as_a_fragment():
    runtime = bootstrap()
    source = T.number(0)
    intervals = set_term(runtime.signature, ())
    issued = isolation_claim(runtime, source, intervals)
    certificate = RootIsolationCertificate(
        source, T.number(1), (source,)
    )
    outcome = check(runtime, issued, certificate, intervals)
    assert isinstance(outcome, Unverified)
    assert outcome.missing == frozenset({"nonzero_polynomial"})


def test_the_checker_requires_the_result_candidate_role():
    runtime = bootstrap()
    _, _, _, candidate = isolate_fixture(runtime, "x^2 - 2")
    for role in (None, CandidateRole.SOURCE):
        outcome = check(
            runtime,
            candidate.specifications[0],
            candidate.certificate,
            candidate.term,
            problem=candidate.problem,
            role=role,
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate role" in outcome.detail


def test_the_session_isolate_roots_command():
    session = Session(bootstrap())
    assert session.execute("x^2 - 2") == "@E0: x^2 - 2"
    answer = session.execute("isolate_roots @E0")
    assert answer.startswith("verified @")
    assert "Set(Interval(" in answer
    before = session.runtime.store.stats()
    assert session.execute("isolate_roots @E0").startswith("verified @")
    assert session.runtime.store.stats() != before


def test_the_session_isolate_roots_command_returns_the_empty_set():
    session = Session(bootstrap())
    session.execute("x^2 + 1")
    answer = session.execute("isolate_roots")
    assert answer.startswith("verified @")
    assert answer.endswith(": Set()")


def test_the_session_isolate_roots_command_finds_a_rational_root():
    session = Session(bootstrap())
    session.execute("x")
    answer = session.execute("isolate_roots")
    assert answer.startswith("verified @")
    assert "Interval(-2, 2)" in answer


def test_the_session_isolate_roots_command_refuses_non_squarefree():
    session = Session(bootstrap())
    session.execute("(x - 1)^2")
    before = session.runtime.store.stats()
    answer = session.execute("isolate_roots @E0")
    assert answer.startswith("unsupported:")
    assert "squarefree_polynomial" in answer
    assert session.runtime.store.stats() == before
    assert session.workspace.links() == ()


def test_the_session_isolate_roots_command_refuses_non_polynomial_input():
    session = Session(bootstrap_elementary())
    session.execute("sin(x)")
    before = session.runtime.store.stats()
    answer = session.execute("isolate_roots @E0")
    assert answer.startswith("unsupported:")
    assert session.runtime.store.stats() == before
    assert session.workspace.links() == ()


def test_interval_and_interval_set_type_through_the_language(runtime):
    from cas.semantics import elaborate

    interval = interval_term(runtime, -2, -1)
    typed_interval = elaborate.typed(
        interval, runtime.frames, runtime.frame.id, runtime.signature
    )
    assert isinstance(typed_interval, Ty.TypedExpr)
    assert typed_interval.sort == S.IntervalSort()

    empty = set_term(runtime.signature, ())
    typed_empty = elaborate.typed(
        empty, runtime.frames, runtime.frame.id, runtime.signature
    )
    assert isinstance(typed_empty, Ty.TypedExpr)
    assert typed_empty.sort == S.SetSort(S.UNKNOWN_SCALAR, empty=True)

    singleton = interval_set(runtime, ((-2, -1),))
    typed_singleton = elaborate.typed(
        singleton, runtime.frames, runtime.frame.id, runtime.signature
    )
    assert isinstance(typed_singleton, Ty.TypedExpr)
    assert typed_singleton.sort == S.SetSort(S.IntervalSort(), empty=False)


def test_interval_source_round_trips(runtime):
    from cas.frontend.pprint import to_source, to_str

    term = polynomial(runtime, "Interval(-2, -1)")
    assert to_str(term, runtime.signature) == "Interval(-2, -1)"
    assert to_source(term, runtime.signature) == "Interval(-2, -1)"
    assert polynomial(runtime, to_source(term, runtime.signature)) == term
