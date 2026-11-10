"""The registered real-root-count operation and its independent checker."""

import pytest
from support import (
    render_value,
    runtime_proposition,
    typed_in,
    verification_context,
    view_of,
)

from cas.algebra.real_roots import sturm_chain
from cas.frontend import parse
from cas.frontend.session import Session
from cas.kernel.evidence import (
    CheckRequest,
    InvalidEvidence,
    Refuted,
    Unverified,
    Verified,
)
from cas.language.problems import (
    Coverage,
    DomainRequirement,
    ProblemSpec,
    ResultLanguage,
)
from cas.language.roles import CandidateRole
from cas.math.algebra.root_count_checker import RootCountChecker
from cas.math.algebra.root_count_specification import (
    RootCountCertificate,
    RootCountVocabulary,
    has_root_count,
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


def vocabulary_for(runtime):
    symbol = runtime.table.lookup("HasRootCount")
    assert symbol is not None
    return RootCountVocabulary(symbol, "HasRootCount")


def checker_for(runtime):
    spec = runtime.store.checkers.spec("algebra.root_count")
    assert spec is not None
    checker = spec.checker
    assert isinstance(checker, RootCountChecker)
    return checker


def chain_terms(runtime, source):
    view = view_of(runtime, source)
    chain = sturm_chain(runtime.ring, view.value)
    return tuple(
        render_value(runtime, entry, view=view) for entry in chain
    )


def root_count_fixture(
    runtime,
    source_text="x^2 - 2",
    lower_text="-2",
    upper_text="2",
    count=2,
):
    source = polynomial(runtime, source_text)
    lower = polynomial(runtime, lower_text)
    upper = polynomial(runtime, upper_text)
    count_term = T.number(count)
    vocabulary = vocabulary_for(runtime)
    issued = runtime_proposition(
        runtime,
        has_root_count(
            vocabulary, source, lower, upper, count_term
        ),
    )
    certificate = RootCountCertificate(
        source,
        lower,
        upper,
        count_term,
        chain_terms(runtime, source),
    )
    return source, lower, upper, count_term, certificate, issued


def root_count_problem(runtime, inputs, roles=None):
    return ProblemSpec(
        "root_count",
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


def _check(runtime, issued, certificate, candidate, problem=None):
    return checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=candidate,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )


def test_root_count_operation_counts_open_interval_roots(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x^2 - 2"), "source")
    lower = workspace.intake(polynomial(runtime, "-2"), "lower")
    upper = workspace.intake(polynomial(runtime, "2"), "upper")
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.result.term == T.number(2)
    assert result.candidate is not None
    certificate = result.candidate.certificate
    assert isinstance(certificate, RootCountCertificate)
    assert certificate.count == T.number(2)
    assert certificate.polynomial == source.term
    first_entry = view_of(runtime, certificate.chain[0]).value
    assert runtime.ring.equal(first_entry, view_of(runtime, source.term).value)
    assert result.verifications[0].judgment is not None
    assert result.task is not None
    assert result.task.state.value == "completed"


def test_root_count_operation_counts_endpoint_roots_correctly(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x"), "source")
    for lower_text, upper_text, expected in (
        ("-1", "1", 1),
        ("-1", "0", 0),
        ("0", "1", 0),
    ):
        lower = workspace.intake(polynomial(runtime, lower_text))
        upper = workspace.intake(polynomial(runtime, upper_text))
        result = workspace.root_count(
            source, lower, upper, runtime.variable
        )
        assert result.status is OperationStatus.VERIFIED
        assert result.result is not None
        assert result.result.term == T.number(expected)


def test_root_count_operation_counts_a_nonzero_constant_as_zero(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(T.number(7), "constant")
    lower = workspace.intake(T.number(-3))
    upper = workspace.intake(T.number(4))
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.result.term == T.number(0)


def test_root_count_refuses_non_squarefree_polynomial(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(
        polynomial(runtime, "(x - 1)^2"), "repeated"
    )
    lower = workspace.intake(T.number(-2))
    upper = workspace.intake(T.number(2))
    before = runtime.store.stats()
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"squarefree_polynomial"})
    assert result.candidate is None
    assert workspace.candidates() == ()
    assert runtime.store.stats() == before


def test_root_count_refuses_zero_polynomial(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(T.number(0), "zero")
    lower = workspace.intake(T.number(-1))
    upper = workspace.intake(T.number(1))
    before = runtime.store.stats()
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"nonzero_polynomial"})
    assert runtime.store.stats() == before


def test_root_count_refuses_reversed_endpoints(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x^2 - 2"), "source")
    lower = workspace.intake(T.number(2))
    upper = workspace.intake(T.number(-2))
    before = runtime.store.stats()
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"ordered_endpoints"})
    assert runtime.store.stats() == before


def test_root_count_refuses_a_nonconstant_endpoint(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x"), "source")
    lower = workspace.intake(polynomial(runtime, "x"), "lower")
    upper = workspace.intake(T.number(2))
    before = runtime.store.stats()
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"rational_endpoint"})
    assert runtime.store.stats() == before


def test_root_count_refuses_a_non_rational_endpoint_in_the_elementary_runtime():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x"), "source")
    lower = workspace.intake(
        polynomial(runtime, "sqrt(2)"), "irrational"
    )
    upper = workspace.intake(T.number(2))
    before = runtime.store.stats()
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing
    assert result.candidate is None
    assert runtime.store.stats() == before


def test_root_count_refuses_a_restricted_region(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(polynomial(runtime, "x^2 - 2"), "source")
    lower = workspace.intake(T.number(-2))
    upper = workspace.intake(T.number(2))
    region = runtime_proposition(runtime, polynomial(runtime, "x > 0"))
    before = runtime.store.stats()
    result = workspace.apply(
        "root_count",
        (source, lower, upper),
        target=runtime.variable,
        region=region,
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"restricted_region"})
    assert runtime.store.stats() == before


def test_the_checker_verifies_a_correct_count():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    problem = root_count_problem(
        runtime,
        (
            typed_in(runtime.frames, runtime.frame.id, runtime.signature, source),
            typed_in(runtime.frames, runtime.frame.id, runtime.signature, lower),
            typed_in(runtime.frames, runtime.frame.id, runtime.signature, upper),
        ),
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            problem=problem,
            candidate=count,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Verified)


def test_the_checker_refutes_a_wrong_count():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime, count=3
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            candidate=count,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Refuted)
    assert "claimed count" in outcome.detail


def test_the_checker_rejects_a_tampered_chain():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    tampered = RootCountCertificate(
        certificate.polynomial,
        certificate.lower,
        certificate.upper,
        certificate.count,
        (certificate.chain[0], certificate.chain[1], T.number(7)),
    )
    outcome = _check(runtime, issued, tampered, count)
    assert isinstance(outcome, InvalidEvidence)
    assert "Sturm recurrence" in outcome.detail


def test_the_checker_rejects_a_missing_chain_entry():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime, source_text="(x - 1)*(x - 2)*(x - 3)", count=3
    )
    missing = RootCountCertificate(
        certificate.polynomial,
        certificate.lower,
        certificate.upper,
        certificate.count,
        (
            certificate.chain[0],
            certificate.chain[1],
            certificate.chain[3],
        ),
    )
    outcome = _check(runtime, issued, missing, count)
    assert isinstance(outcome, InvalidEvidence)
    assert "Sturm recurrence" in outcome.detail


def test_the_checker_rejects_an_extra_chain_entry():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    extra = RootCountCertificate(
        certificate.polynomial,
        certificate.lower,
        certificate.upper,
        certificate.count,
        certificate.chain + (T.number(1),),
    )
    outcome = _check(runtime, issued, extra, count)
    assert isinstance(outcome, InvalidEvidence)
    assert "zero remainder" in outcome.detail


def test_the_checker_rejects_a_wrong_first_chain_entry():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    wrong = RootCountCertificate(
        certificate.polynomial,
        certificate.lower,
        certificate.upper,
        certificate.count,
        (T.number(1),) + certificate.chain[1:],
    )
    outcome = _check(runtime, issued, wrong, count)
    assert isinstance(outcome, InvalidEvidence)
    assert "first Sturm-chain entry" in outcome.detail


def test_the_checker_rejects_a_chain_from_another_polynomial():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    other_chain = chain_terms(runtime, polynomial(runtime, "x^2 - 3"))
    wrong = RootCountCertificate(
        certificate.polynomial,
        certificate.lower,
        certificate.upper,
        certificate.count,
        other_chain,
    )
    outcome = _check(runtime, issued, wrong, count)
    assert isinstance(outcome, InvalidEvidence)
    assert "first Sturm-chain entry" in outcome.detail


def test_the_checker_rejects_a_nonconstant_last_chain_entry():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    wrong = RootCountCertificate(
        certificate.polynomial,
        certificate.lower,
        certificate.upper,
        certificate.count,
        certificate.chain[:2],
    )
    outcome = _check(runtime, issued, wrong, count)
    assert isinstance(outcome, InvalidEvidence)
    assert "does not end at a constant" in outcome.detail


def test_the_checker_rejects_a_tampered_count_certificate():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    tampered = RootCountCertificate(
        certificate.polynomial,
        certificate.lower,
        certificate.upper,
        T.number(5),
        certificate.chain,
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            tampered,
            candidate=count,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "certificate does not match" in outcome.detail


def test_the_checker_rejects_a_mismatched_problem():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime
    )
    wrong_upper = polynomial(runtime, "3")
    problem = root_count_problem(
        runtime,
        (
            typed_in(runtime.frames, runtime.frame.id, runtime.signature, source),
            typed_in(runtime.frames, runtime.frame.id, runtime.signature, lower),
            typed_in(
                runtime.frames,
                runtime.frame.id,
                runtime.signature,
                wrong_upper,
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
            candidate=count,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, InvalidEvidence)
    assert "problem inputs" in outcome.detail


def test_the_checker_reports_a_complete_non_squarefree_chain_as_a_fragment():
    runtime = bootstrap()
    source = polynomial(runtime, "(x - 1)^2")
    lower = polynomial(runtime, "-2")
    upper = polynomial(runtime, "2")
    count = T.number(0)
    issued = runtime_proposition(
        runtime,
        has_root_count(
            vocabulary_for(runtime), source, lower, upper, count
        ),
    )
    chain = (source, polynomial(runtime, "2*x - 2"))
    certificate = RootCountCertificate(
        source, lower, upper, count, chain
    )
    outcome = _check(runtime, issued, certificate, count)
    assert isinstance(outcome, Unverified)
    assert outcome.missing == frozenset({"squarefree_polynomial"})
    assert "not squarefree" in outcome.detail


def test_the_checker_rejects_a_truncated_squarefree_chain():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime, source_text="(x - 1)*(x - 2)*(x - 3)", count=3
    )
    truncated = certificate.chain[:-1]
    certificate = RootCountCertificate(
        source, lower, upper, count, truncated
    )
    outcome = _check(runtime, issued, certificate, count)
    assert isinstance(outcome, InvalidEvidence)
    assert "does not end at a constant" in outcome.detail


def test_the_checker_reports_a_nonconstant_endpoint_as_a_fragment_gap():
    runtime = bootstrap()
    source, lower, upper, count, certificate, issued = root_count_fixture(
        runtime, source_text="x", lower_text="x", upper_text="2", count=0
    )
    outcome = checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            candidate=count,
            candidate_role=CandidateRole.RESULT,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )
    assert isinstance(outcome, Unverified)
    assert outcome.missing == frozenset({"rational_endpoint"})


def test_the_checker_requires_the_result_candidate_role():
    runtime = bootstrap()
    _, _, _, count, certificate, issued = root_count_fixture(runtime)
    for role in (None, CandidateRole.SOURCE):
        outcome = checker_for(runtime).check(
            CheckRequest(
                runtime.frame.id,
                (issued,),
                (),
                certificate,
                candidate=count,
                candidate_role=role,
                context=verification_context(
                    runtime, algebra=runtime.request
                ),
            )
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate role" in outcome.detail


def test_the_session_root_count_command():
    session = Session(bootstrap())
    assert session.execute("x^2 - 2") == "@E0: x^2 - 2"
    first = session.execute("root_count @E0 -2 2")
    assert first.startswith("verified @")
    assert first.endswith(": 2")
    before = session.runtime.store.stats()
    assert session.execute("root_count @E0 3 -2").startswith("unsupported:")
    assert session.runtime.store.stats() == before
    second = session.execute("root_count @E0 0 2")
    assert second.startswith("verified @")
    assert second.endswith(": 1")
    answer = session.execute("root_count @E0 2 3")
    assert answer.startswith("verified @")
    assert answer.endswith(": 0")


def test_the_session_root_count_command_uses_the_focus():
    session = Session(bootstrap())
    session.execute("x")
    answer = session.execute("root_count -1 1")
    assert answer.startswith("verified @")
    assert answer.endswith(": 1")


def test_the_session_root_count_command_refuses_non_squarefree():
    session = Session(bootstrap())
    session.execute("(x - 1)^2")
    before = session.runtime.store.stats()
    answer = session.execute("root_count @E0 -2 2")
    assert answer.startswith("unsupported:")
    assert "squarefree_polynomial" in answer
    assert session.runtime.store.stats() == before
    assert session.workspace.links() == ()


def test_the_session_root_count_command_refuses_the_elementary_function():
    session = Session(bootstrap_elementary())
    session.execute("sin(x)")
    before = session.runtime.store.stats()
    answer = session.execute("root_count @E0 0 1")
    assert answer.startswith("unsupported:")
    assert session.runtime.store.stats() == before
    assert session.workspace.links() == ()


def test_root_count_is_not_registered_in_the_parameterized_runtime():
    runtime = bootstrap_parameterized()
    assert runtime.operations.get("root_count") is None


def test_root_count_is_registered_in_the_elementary_runtime():
    runtime = bootstrap_elementary()
    assert runtime.operations.get("root_count") is not None
    workspace = new_workspace(runtime)
    source = workspace.intake(
        polynomial(runtime, "x^2 - 2"), "source"
    )
    lower = workspace.intake(T.number(-2))
    upper = workspace.intake(T.number(2))
    result = workspace.root_count(
        source, lower, upper, runtime.variable
    )
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.result.term == T.number(2)


def _manual_root_count_inputs(
    workspace, runtime, source_text, lower_text, upper_text
):
    return (
        workspace.intake(polynomial(runtime, source_text)),
        workspace.intake(polynomial(runtime, lower_text)),
        workspace.intake(polynomial(runtime, upper_text)),
    )


@pytest.mark.parametrize(
    ("source_text", "lower_text", "upper_text", "missing"),
    [
        (
            "(x - 1)^2",
            "-2",
            "2",
            frozenset({"squarefree_polynomial"}),
        ),
        ("0", "-1", "1", frozenset({"nonzero_polynomial"})),
        ("x", "x", "2", frozenset({"rational_endpoint"})),
        (
            "x^2 - 2",
            "2",
            "-2",
            frozenset({"ordered_endpoints"}),
        ),
    ],
)
def test_define_problem_blocks_root_count_out_of_fragment(
    runtime, source_text, lower_text, upper_text, missing
):
    workspace = new_workspace(runtime)
    source, lower, upper = _manual_root_count_inputs(
        workspace, runtime, source_text, lower_text, upper_text
    )
    before = runtime.store.stats()
    task = workspace.define_problem(
        "root_count",
        (source, lower, upper),
        target=runtime.variable,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None
    assert task.blocker.missing == missing
    assert runtime.store.stats() == before


def test_run_task_refuses_a_root_count_blocked_at_definition(runtime):
    workspace = new_workspace(runtime)
    source, lower, upper = _manual_root_count_inputs(
        workspace, runtime, "(x - 1)^2", "-2", "2"
    )
    task = workspace.define_problem(
        "root_count",
        (source, lower, upper),
        target=runtime.variable,
    )
    assert task.state is TaskState.BLOCKED
    before = runtime.store.stats()
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.INVALID
    assert result.candidate is None
    assert runtime.store.stats() == before


def test_a_manual_root_count_task_runs(runtime):
    workspace = new_workspace(runtime)
    source, lower, upper = _manual_root_count_inputs(
        workspace, runtime, "x^2 - 2", "-2", "2"
    )
    task = workspace.define_problem(
        "root_count",
        (source, lower, upper),
        target=runtime.variable,
    )
    assert task.state is TaskState.READY
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert result.result.term == T.number(2)

