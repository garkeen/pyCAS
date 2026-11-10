"""Finite set results: typing, linear solving, soundness and completeness."""

from support import (
    FrameSorts,
    head_app,
    runtime_proposition,
    variable,
    verification_context,
)

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
from cas.language.signatures import StructuralHead
from cas.math.solving.linear_checker import LinearSolutionChecker
from cas.math.solving.linear_specification import (
    LinearSolutionCertificate,
    SolutionSetVocabulary,
    has_solution_set,
    has_solution_subset,
)
from cas.runtime.bootstrap import bootstrap, new_workspace
from cas.syntax import term as T
from cas.workflow.records import OperationStatus


def linear(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.TIMES,
            T.number(2),
            variable(runtime),
        ),
        T.number(4),
    )


def quadratic(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        head_app(
            runtime.signature,
            StructuralHead.POWER,
            variable(runtime),
            T.number(2),
        ),
        T.number(-1),
    )


def test_set_terms_are_canonical_and_typed(runtime):
    term = set_term(runtime.signature, (T.number(1), T.number(2), T.number(1)))
    assert term.arguments == (T.number(1), T.number(2))
    assert set_members(term, runtime.signature) == (T.number(1), T.number(2))
    typed = Ty.infer(
        term,
        runtime.signature,
        FrameSorts(runtime.frames, runtime.frame.id),
    )
    assert isinstance(typed, Ty.Typed)
    assert typed.sort.embeds_into(S.SetSort(S.REAL))
    empty = set_term(runtime.signature, ())
    typed_empty = Ty.infer(
        empty,
        runtime.signature,
        FrameSorts(runtime.frames, runtime.frame.id),
    )
    assert isinstance(typed_empty, Ty.Typed)
    assert typed_empty.sort == S.SetSort(S.UNKNOWN_SCALAR, empty=True)
    assert typed_empty.sort.embeds_into(S.SetSort(S.REAL))


def test_set_terms_are_permutation_invariant(runtime):
    left = set_term(
        runtime.signature, (T.number(1), T.number(2))
    )
    right = set_term(
        runtime.signature, (T.number(2), T.number(1))
    )
    assert left == right


def test_solve_linear_returns_a_complete_singleton(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(linear(runtime), "linear")
    result = workspace.solve_linear(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert set_members(result.result.term, runtime.signature) == (T.number(-2),)
    assert result.candidate is not None
    assert result.candidate.problem.coverage is Coverage.COMPLETE_SET
    assert result.candidate.problem.result_language.value == "set"
    assert result.task is not None
    assert result.task.state.value == "completed"


def test_solve_linear_returns_the_empty_set_for_a_nonzero_constant(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(T.number(3), "constant")
    result = workspace.solve_linear(source, runtime.variable)
    assert result.status is OperationStatus.VERIFIED
    assert result.result is not None
    assert set_members(result.result.term, runtime.signature) == ()


def test_solve_linear_refuses_incomplete_higher_degree_sets(runtime):
    workspace = new_workspace(runtime)
    source = workspace.intake(quadratic(runtime), "quadratic")
    complete = workspace.solve_linear(source, runtime.variable)
    assert complete.status is OperationStatus.UNSUPPORTED
    assert complete.task is not None
    assert complete.task.state.value == "blocked"
    sound = workspace.solve_linear(
        source, runtime.variable, Coverage.SOUND_SET
    )
    assert sound.status is OperationStatus.VERIFIED
    assert sound.result is not None
    assert set_members(sound.result.term, runtime.signature) == ()
    assert sound.candidate is not None
    assert sound.candidate.problem.coverage is Coverage.SOUND_SET


def test_solve_linear_refuses_the_zero_polynomial_complete_set(runtime):
    workspace = new_workspace(runtime)
    zero = workspace.intake(T.number(0), "zero")
    complete = workspace.solve_linear(zero, runtime.variable)
    assert complete.status is OperationStatus.UNSUPPORTED
    sound = workspace.solve_linear(
        zero, runtime.variable, Coverage.SOUND_SET
    )
    assert sound.status is OperationStatus.VERIFIED
    assert sound.result is not None
    assert set_members(sound.result.term, runtime.signature) == ()


def checker_for(runtime):
    spec = runtime.store.checkers.spec("solving.linear")
    assert spec is not None
    checker = spec.checker
    assert isinstance(checker, LinearSolutionChecker)
    return checker


def vocabulary_for(runtime):
    complete = runtime.table.lookup("HasSolutionSet")
    sound = runtime.table.lookup("HasSolutionSubset")
    assert complete is not None and sound is not None
    return SolutionSetVocabulary(
        complete, "HasSolutionSet", sound, "HasSolutionSubset"
    )


def check_claim(runtime, source, members, complete, candidate, role=CandidateRole.SET):
    vocabulary = vocabulary_for(runtime)
    result = set_term(runtime.signature, members)
    builder = has_solution_set if complete else has_solution_subset
    issued = runtime_proposition(
        runtime,
        builder(
            vocabulary, source, variable(runtime), result
        ),
    )
    coverage = Coverage.COMPLETE_SET if complete else Coverage.SOUND_SET
    certificate = LinearSolutionCertificate(
        source, runtime.variable, result, coverage
    )
    return checker_for(runtime).check(
        CheckRequest(
            runtime.frame.id,
            (issued,),
            (),
            certificate,
            candidate=candidate,
            candidate_role=role,
            context=verification_context(runtime, algebra=runtime.request),
        )
    )


def test_the_checker_refutes_a_wrong_member_and_a_missing_root(runtime):
    source = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        variable(runtime),
        T.number(-1),
    )
    wrong = check_claim(
        runtime,
        source,
        (T.number(2),),
        True,
        set_term(runtime.signature, (T.number(2),)),
    )
    assert isinstance(wrong, Refuted)
    missing = check_claim(
        runtime, source, (), True, set_term(runtime.signature, ())
    )
    assert isinstance(missing, Refuted)
    sound = check_claim(
        runtime, source, (), False, set_term(runtime.signature, ())
    )
    assert isinstance(sound, Verified)


def test_the_checker_does_not_claim_higher_degree_completeness(runtime):
    source = quadratic(runtime)
    empty = set_term(runtime.signature, ())
    complete = check_claim(runtime, source, (), True, empty)
    assert isinstance(complete, Unverified)
    sound = check_claim(runtime, source, (), False, empty)
    assert isinstance(sound, Verified)


def test_the_checker_requires_the_candidate_role(runtime):
    source = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        variable(runtime),
        T.number(-1),
    )
    members = (T.number(1),)
    for role in (None, CandidateRole.RESULT):
        outcome = check_claim(
            runtime, source, members, True, T.number(1), role=role
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate role" in outcome.detail
    for candidate in (None, set_term(runtime.signature, ())):
        outcome = check_claim(
            runtime,
            source,
            members,
            True,
            candidate,
            role=CandidateRole.SET,
        )
        assert isinstance(outcome, InvalidEvidence)
        assert "candidate" in outcome.detail


def test_the_session_solve_command_reports_the_set(runtime):
    session = Session(bootstrap())
    session.execute("2*x + 4")
    assert session.execute("solve").startswith("verified @")
    assert "Set(-2)" in session.execute("show")
