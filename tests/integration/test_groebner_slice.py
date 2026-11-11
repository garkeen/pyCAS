"""The Groebner-basis vertical slice through the session and the kernel."""

from cas.frontend import parse
from cas.frontend.session import Session
from cas.language.problems import Coverage, ResultLanguage
from cas.language.roles import CandidateRole
from cas.language.sets import set_members
from cas.math.algebra.groebner_operation import GroebnerOperation
from cas.math.algebra.groebner_specification import parse_groebner
from cas.runtime.bootstrap import bootstrap, new_workspace
from cas.syntax import binding as B
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState


def session_with_circle_and_line():
    session = Session(bootstrap())
    assert session.execute("x^2 + y^2 - 1") == "@E0: x^2 + y^2 - 1"
    assert session.execute("x - y") == "@E1: x - y"
    return session


def test_the_session_command_builds_the_reduced_basis():
    session = session_with_circle_and_line()
    answer = session.execute("groebner_basis @E0 @E1")
    assert answer.startswith("verified @E2: Set(")
    assert "-1/2 + y^2" in answer
    assert "-y + x" in answer
    shown = session.execute("show @E2")
    assert shown.startswith("@E2: Set(")
    assert answer == "verified " + shown
    listing = session.execute("list")
    assert "> @E2: Set(" in listing
    candidates = session.execute("candidates")
    assert candidates.startswith("C0: Set(")
    assert "state=verified" in candidates
    assert "coverage=complete" in candidates
    assert "language=satisfies" in candidates


def test_the_session_history_records_the_generator_inputs_and_no_parameters():
    session = session_with_circle_and_line()
    session.execute("groebner_basis @E0 @E1")
    lines = [
        line
        for line in session.history()
        if line.split()[1].startswith("groebner_basis")
    ]
    assert len(lines) == 1
    line = lines[0]
    assert "groebner_basis@1" in line
    assert "inputs=[@E0, @E1]" in line
    assert "parameters=[]" in line
    assert "status=verified" in line
    assert "actor=user" in line


def test_undo_and_redo_move_the_reduced_basis_revision():
    session = session_with_circle_and_line()
    session.execute("groebner_basis @E0 @E1")
    assert session.execute("undo").startswith("undo: @E1 ")
    assert session.focus is not None
    assert session.label_of(session.focus) == "E1"
    assert session.execute("redo").startswith("redo: @E2 ")
    assert session.focus is not None
    assert session.label_of(session.focus) == "E2"


def test_the_session_check_and_decide_reverify_the_candidate():
    session = session_with_circle_and_line()
    session.execute("groebner_basis @E0 @E1")
    checked = session.execute("check C0")
    assert checked.startswith("verified @E3: Set(")
    verdict = session.execute("decide C0")
    assert verdict.startswith("yes: HasGroebnerBasis(")
    assert "checker: algebra.groebner@1" in verdict


def test_the_result_is_a_polynomial_set_not_a_solution_set():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    first = workspace.intake(
        parse("x^2 + y^2 - 1", runtime.table, runtime.signature), "circle"
    )
    second = workspace.intake(
        parse("x - y", runtime.table, runtime.signature), "line"
    )
    result = workspace.groebner_basis((first, second))
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    members = set_members(result.result.term, runtime.signature)
    assert members is not None and len(members) == 2
    allowed = {runtime.variable, runtime.table.lookup("y")}
    for member in members:
        assert B.variable_symbols(member) <= allowed
        if isinstance(member, T.Apply) and isinstance(
            member.operator, T.SymbolRef
        ):
            name = runtime.table.name_of(member.operator.symbol_id)
            assert name not in {"Eq", "Interval", "RootOf", "Piecewise"}
    candidate = result.candidate
    assert candidate is not None
    assert candidate.candidate_role is CandidateRole.SET
    assert candidate.problem.result_language is ResultLanguage.SET
    assert candidate.problem.coverage is Coverage.COMPLETE_SET
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED
    found = runtime.operations.get("groebner_basis")
    assert isinstance(found, GroebnerOperation)
    claim = parse_groebner(
        found.vocabulary, candidate.specifications[0].term
    )
    assert claim is not None
    assert claim.basis == candidate.term
    assert claim.order == found.vocabulary.order_term()
    # The claim names an ideal presentation: no point, root, interval or
    # explicit solution value is part of the result.
    assert result.structured is None
    assert result.generic is None
    assert result.region is None
