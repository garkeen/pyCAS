"""The registered `groebner_basis` operation over the fixed Q[x, y] LEX view."""

from dataclasses import replace

import pytest
from support import runtime_proposition, verification_context, view_of

from cas.algebra.integers import IntegerRing
from cas.algebra.parents import ParentRegistry, ParentSpec
from cas.algebra.polynomial import MonomialOrder, PolynomialRing
from cas.frontend import parse
from cas.frontend.errors import SessionError
from cas.frontend.session import Session
from cas.kernel.evidence import CheckRequest, InvalidEvidence
from cas.kernel.verdict import VerdictYes
from cas.language import sorts as S
from cas.language.decisions import Reason
from cas.language.execution import ConditionPolicy, ExecutionBudget
from cas.language.problems import (
    Coverage,
    ResultLanguage,
    ValueDomain,
)
from cas.language.roles import CandidateRole
from cas.language.sets import set_members, set_term
from cas.math.algebra.groebner_operation import GroebnerOperation
from cas.math.algebra.groebner_specification import (
    GroebnerCertificate,
    parse_groebner,
)
from cas.operations.protocols import (
    ExecutionRequest,
    OperationRequest,
    ProblemBuilt,
    ProblemInvalid,
    ProblemUnsupported,
    ProposalUnsupported,
)
from cas.runtime.bootstrap import (
    bootstrap,
    bootstrap_elementary,
    bootstrap_parameterized,
    new_workspace,
)
from cas.semantics.bridge import MultivariatePolynomialBridge
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState


def term(runtime, text):
    return parse(text, runtime.table, runtime.signature)


def intake(workspace, runtime, text, label):
    return workspace.intake(term(runtime, text), label)


def expected_set(runtime, texts):
    return set_term(
        runtime.signature, tuple(term(runtime, text) for text in texts)
    )


def polynomial(runtime, text):
    found = operation(runtime)
    view = view_of(
        runtime,
        term(runtime, text),
        bridge=found.bridge,
        request=found.request,
    )
    return view.value


def assert_basis(runtime, result, texts):
    """Compare a result set with polynomials by ring equality, not spelling."""
    assert result.result is not None
    members = set_members(result.result.term, runtime.signature)
    assert members is not None
    found = operation(runtime)
    actual = tuple(
        view_of(
            runtime,
            member,
            bridge=found.bridge,
            request=found.request,
        ).value
        for member in members
    )
    remaining = [polynomial(runtime, text) for text in texts]
    assert len(actual) == len(remaining)
    for value in actual:
        match = next(
            (
                index
                for index, expected in enumerate(remaining)
                if found.ring.equal(value, expected)
            ),
            None,
        )
        assert match is not None, "the result set has an unexpected member"
        del remaining[match]


def operation(runtime):
    found = runtime.operations.get("groebner_basis")
    assert isinstance(found, GroebnerOperation)
    return found


def circle_line(workspace, runtime):
    return (
        intake(workspace, runtime, "x^2 + y^2 - 1", "circle"),
        intake(workspace, runtime, "x - y", "line"),
    )


def test_the_circle_and_line_have_the_expected_lex_reduced_basis(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(circle_line(workspace, runtime))
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert_basis(runtime, result, ("y^2 - 1/2", "x - y"))
    assert result.region is None
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED
    assert result.task.problem.coverage is Coverage.COMPLETE_SET
    assert result.task.problem.result_language is ResultLanguage.SET
    assert result.verifications[0].judgment is not None


def test_the_parabola_system_has_the_expected_lex_reduced_basis(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(
        (
            intake(workspace, runtime, "x^2 - y", "first"),
            intake(workspace, runtime, "x - y^2", "second"),
        )
    )
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert_basis(runtime, result, ("x - y^2", "y^4 - y"))


def test_a_zero_generator_has_the_empty_reduced_basis(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(
        (intake(workspace, runtime, "0", "zero"),)
    )
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert set_members(result.result.term, runtime.signature) == ()


def test_the_unit_ideal_has_the_constant_one_basis(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(
        (
            intake(workspace, runtime, "3", "three"),
            intake(workspace, runtime, "x", "x"),
        )
    )
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert_basis(runtime, result, ("1",))


def test_a_nonzero_constant_is_the_unit_ideal(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(
        (intake(workspace, runtime, "3", "three"),)
    )
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert_basis(runtime, result, ("1",))


def test_a_single_generator_is_its_own_reduced_basis(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(
        (intake(workspace, runtime, "x - y", "line"),)
    )
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert_basis(runtime, result, ("x - y",))


def test_duplicate_scaled_and_zero_generators_are_canonicalised(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(
        (
            intake(workspace, runtime, "x - y", "line"),
            intake(workspace, runtime, "y - x", "negated"),
            intake(workspace, runtime, "0", "zero"),
            intake(workspace, runtime, "2*x - 2*y", "scaled"),
        )
    )
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert_basis(runtime, result, ("x - y",))


def test_the_candidate_binds_the_set_role_and_generator_mode_algebra(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(circle_line(workspace, runtime))
    candidate = result.candidate
    assert candidate is not None
    found = operation(runtime)
    assert candidate.candidate_role is CandidateRole.SET
    assert candidate.algebra is found.request
    assert candidate.algebra.roles.target is None
    assert candidate.algebra.roles.variables == found.ring.generators
    assert candidate.problem.coverage is Coverage.COMPLETE_SET
    assert candidate.problem.result_language is ResultLanguage.SET
    claim = parse_groebner(
        found.vocabulary, candidate.specifications[0].term
    )
    assert claim is not None
    assert claim.basis == candidate.term
    assert claim.order == found.vocabulary.order_term()


def test_the_claim_is_a_has_groebner_basis_statement_not_a_solution_set(
    runtime,
):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    result = workspace.groebner_basis(inputs)
    candidate = result.candidate
    assert candidate is not None
    claim = parse_groebner(
        operation(runtime).vocabulary,
        candidate.specifications[0].term,
    )
    assert claim is not None
    assert claim.generators == set_term(
        runtime.signature, tuple(item.term for item in inputs)
    )
    assert claim.basis == result.result.term
    # The result is a finite set of polynomials, not a solution set: no point,
    # equation root or explicit real/complex value is claimed.
    assert set_members(result.result.term, runtime.signature) is not None


def test_define_problem_and_run_task_execute_the_complete_problem(runtime):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    task = workspace.define_problem(
        "groebner_basis",
        inputs,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.READY
    assert task.problem.operation == "groebner_basis"
    assert task.problem.coverage is Coverage.COMPLETE_SET
    assert task.problem.result_language is ResultLanguage.SET
    assert task.problem.region is None
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert_basis(runtime, result, ("y^2 - 1/2", "x - y"))
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED


def test_defining_without_the_requested_coverage_is_blocked(runtime):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    before = runtime.store.stats()
    task = workspace.define_problem("groebner_basis", inputs)
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None
    assert task.blocker.missing == frozenset({"coverage:one_verified"})
    assert task.problem.coverage is Coverage.ONE_VERIFIED
    assert runtime.store.stats() == before


def test_applying_without_the_requested_coverage_is_refused(runtime):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    before = runtime.store.stats()
    result = workspace.apply("groebner_basis", inputs)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.candidate is None
    assert result.result is None
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"coverage:one_verified"})
    assert runtime.store.stats() == before


def test_a_restricted_region_is_refused_at_definition(runtime):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    region = runtime_proposition(
        runtime, term(runtime, "x > 0")
    )
    before = runtime.store.stats()
    task = workspace.define_problem(
        "groebner_basis",
        inputs,
        region=region,
        coverage=Coverage.COMPLETE_SET,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None
    assert task.blocker.missing == frozenset({"restricted_region"})
    assert task.problem.region is region
    assert runtime.store.stats() == before


def test_a_restricted_region_is_refused_by_apply(runtime):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    region = runtime_proposition(
        runtime, term(runtime, "x > 0")
    )
    before = runtime.store.stats()
    result = workspace.apply(
        "groebner_basis",
        inputs,
        region=region,
        coverage=Coverage.COMPLETE_SET,
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.blocker is not None
    assert result.blocker.missing == frozenset({"restricted_region"})
    assert result.candidate is None
    assert runtime.store.stats() == before


def test_an_unbound_region_is_translated_to_an_invalid_request(runtime):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    declared = workspace.declare("z", S.REAL)
    assert declared.status is OperationStatus.VERIFIED, declared.detail
    region = runtime_proposition(
        runtime, term(runtime, "z > 0"), frame=declared.frame
    )
    before = runtime.store.stats()
    result = workspace.apply(
        "groebner_basis",
        inputs,
        region=region,
        coverage=Coverage.COMPLETE_SET,
    )
    assert result.status is OperationStatus.INVALID
    assert "problem region free symbol is not bound" in result.detail
    assert result.candidate is None
    assert result.result is None
    assert result.task is None
    assert workspace.candidates() == ()
    assert runtime.store.stats() == before


@pytest.mark.parametrize("with_region", (False, True))
def test_a_complete_set_request_cannot_externalize_premises(
    runtime, with_region
):
    workspace = new_workspace(runtime)
    inputs = circle_line(workspace, runtime)
    premise = runtime_proposition(runtime, term(runtime, "x > 0"))
    before = runtime.store.stats()
    result = workspace.apply(
        "groebner_basis",
        inputs,
        region=premise if with_region else None,
        coverage=Coverage.COMPLETE_SET,
        externalizable=(premise,),
    )
    assert result.status is OperationStatus.INVALID
    assert "a complete-set request cannot externalize" in result.detail
    assert result.candidate is None
    assert result.result is None
    assert result.task is None
    assert workspace.candidates() == ()
    assert runtime.store.stats() == before


def test_a_non_polynomial_generator_is_refused_without_kernel_writes(runtime):
    workspace = new_workspace(runtime)
    inputs = (
        intake(workspace, runtime, "1/x", "inverse"),
        intake(workspace, runtime, "x - y", "line"),
    )
    before = runtime.store.stats()
    result = workspace.groebner_basis(inputs)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.candidate is None
    assert result.result is None
    assert result.blocker is not None
    assert "multivariate_polynomial_representation" in result.blocker.missing
    assert runtime.store.stats() == before
    assert workspace.candidates() == ()


def test_an_explicit_target_is_an_invalid_request(runtime):
    request = OperationRequest(
        runtime.frame.id,
        (term(runtime, "x - y"),),
        target=runtime.variable,
        coverage=Coverage.COMPLETE_SET,
    )
    outcome = operation(runtime).build_problem(request)
    assert isinstance(outcome, ProblemInvalid)
    assert "target" in outcome.detail


def test_a_non_field_coefficient_structure_is_refused(runtime):
    found = operation(runtime)
    integers = IntegerRing()
    ring = PolynomialRing(
        found.ring.generators, integers, MonomialOrder.LEX
    )
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Z"), integers)
    parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=ParentSpec("Z"),
            generators=found.ring.generators,
            options=(("monomial_order", "lex"),),
        ),
        ring,
    )
    bridge = MultivariatePolynomialBridge(
        ring,
        parent,
        runtime.world.id,
        runtime.signature,
        runtime.table.name_of,
        T.number,
    )
    request = AlgebraRequest(
        coefficient,
        ValueDomain.INTEGER,
        None,
        found.request.roles,
        found.request.interpretation,
    )
    integer_operation = replace(
        found,
        ring=ring,
        bridge=bridge,
        request=request,
    )
    outcome = integer_operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (term(runtime, "x - y"),),
            coverage=Coverage.COMPLETE_SET,
        )
    )
    assert isinstance(outcome, ProblemUnsupported)
    assert outcome.reason is Reason.FRAGMENT
    assert outcome.missing == frozenset({"coefficient_field"})


def test_a_budget_exhausted_search_proposes_no_partial_basis(runtime):
    found = operation(runtime)
    request = OperationRequest(
        runtime.frame.id,
        (term(runtime, "x^2 + y^2 - 1"), term(runtime, "x - y")),
        coverage=Coverage.COMPLETE_SET,
    )
    built = found.build_problem(request)
    assert isinstance(built, ProblemBuilt)
    execution = ExecutionRequest(
        request,
        built.problem,
        built.algebra,
        request.frame,
        ConditionPolicy.REQUIRE_PROVED,
        ExecutionBudget(),
    )
    starved = replace(found, budget=0)
    outcome = starved.propose(execution)
    assert isinstance(outcome, ProposalUnsupported)
    assert outcome.reason is Reason.BUDGET
    assert outcome.missing == frozenset({"buchberger_budget"})


def test_the_operation_rejects_an_inconsistent_assembly(runtime):
    found = operation(runtime)
    with pytest.raises(TypeError):
        replace(found, budget=True)
    with pytest.raises(ValueError):
        replace(found, budget=-1)
    with pytest.raises(ValueError):
        replace(found, ring=runtime.ring)
    with pytest.raises(ValueError):
        replace(found, request=runtime.request)
    vocabulary = replace(
        found.vocabulary,
        order=MonomialOrder.GRLEX,
    )
    with pytest.raises(ValueError):
        replace(found, vocabulary=vocabulary)


def test_check_and_decide_reverify_the_recorded_candidate(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(circle_line(workspace, runtime))
    candidate = result.candidate
    assert candidate is not None
    checked = workspace.check_candidate(candidate.id)
    assert checked.status is OperationStatus.VERIFIED, checked.detail
    assert checked.candidate is not None
    assert checked.result is not None
    verdict = workspace.decide_candidate(candidate.id)
    assert isinstance(verdict, VerdictYes)
    assert verdict.receipt.checker_id == "algebra.groebner"


def test_a_tampered_cofactor_certificate_is_invalid_evidence(runtime):
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(circle_line(workspace, runtime))
    candidate = result.candidate
    assert candidate is not None
    certificate = candidate.certificate
    assert isinstance(certificate, GroebnerCertificate)
    wrong = GroebnerCertificate(
        tuple(
            tuple(T.number(0) for _ in row)
            for row in certificate.cofactors
        )
    )
    checker = runtime.store.checkers.get("algebra.groebner")
    assert checker is not None
    for supplied in (wrong, GroebnerCertificate(())):
        outcome = checker.check(
            _check_request(runtime, candidate, supplied)
        )
        assert isinstance(outcome, InvalidEvidence), outcome


def _check_request(runtime, candidate, certificate):
    return CheckRequest(
        candidate.frame,
        candidate.specifications,
        (),
        certificate,
        problem=candidate.problem,
        candidate=candidate.term,
        candidate_role=CandidateRole.SET,
        context=verification_context(
            runtime,
            candidate.frame,
            algebra=candidate.algebra,
        ),
    )


def test_the_parameterized_runtime_has_no_groebner_operation():
    runtime = bootstrap_parameterized()
    assert runtime.operations.get("groebner_basis") is None
    assert runtime.table.lookup("y") is None


def test_the_elementary_runtime_registers_the_groebner_operation():
    runtime = bootstrap_elementary()
    found = operation(runtime)
    y = runtime.table.lookup("y")
    assert y is not None
    assert found.ring.generators == (runtime.variable, y)
    workspace = new_workspace(runtime)
    result = workspace.groebner_basis(circle_line(workspace, runtime))
    assert result.status is OperationStatus.VERIFIED, result.detail


def test_elementary_differentiation_still_uses_the_elementary_checker():
    runtime = bootstrap_elementary()
    session = Session(runtime)
    session.execute("sqrt(0)")
    assert session.execute("diff") == "verified @E1: 0"
    session.execute("cos(x)")
    output = session.execute("diff")
    assert output.startswith("verified ")
    assert "-sin(x)" in output


def test_the_session_groebner_command_uses_the_visible_objects():
    session = Session(bootstrap())
    assert session.execute("x^2 + y^2 - 1") == "@E0: x^2 + y^2 - 1"
    assert session.execute("x - y") == "@E1: x - y"
    answer = session.execute("groebner_basis @E0 @E1")
    assert answer.startswith("verified @E2: Set(")
    assert "-1/2 + y^2" in answer
    assert "-y + x" in answer
    with pytest.raises(SessionError) as caught:
        session.execute("groebner_basis x")
    assert "usage" in str(caught.value)


def test_the_session_groebner_command_uses_the_focused_expression():
    session = Session(bootstrap())
    session.execute("x - y")
    answer = session.execute("groebner_basis")
    assert answer.startswith("verified @E1: Set(")
    assert "-y + x" in answer
