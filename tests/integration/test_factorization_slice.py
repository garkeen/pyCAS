"""The Q[x] factorization vertical slice through the workspace and session."""

from cas.frontend import parse
from cas.frontend.session import Session
from cas.kernel.verdict import VerdictYes
from cas.language.problems import Coverage
from cas.math.algebra.factorization_checker import FactorizationChecker
from cas.math.algebra.factorization_operation import (
    FactorizationOperation,
)
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
    parse_factorization,
)
from cas.runtime.bootstrap import (
    bootstrap,
    bootstrap_elementary,
    new_workspace,
)
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState


def term(runtime, text):
    return parse(text, runtime.table, runtime.signature)


def operation(runtime):
    found = runtime.operations.get("factor_polynomial")
    assert isinstance(found, FactorizationOperation)
    return found


def source(workspace, runtime, text):
    return workspace.intake(term(runtime, text), "source")


def test_bootstrap_registers_the_operation_and_checker(runtime):
    found = operation(runtime)
    assert found.id == "factor_polynomial"
    assert found.checker_id == "algebra.factorization"
    spec = runtime.store.checkers.spec(found.checker_id)
    assert spec is not None
    assert isinstance(spec.checker, FactorizationChecker)
    assert spec.accepted_problem_kinds == frozenset(
        {"factor_polynomial"}
    )
    assert spec.accepted_specification_kinds == frozenset(
        {"HasFactorization"}
    )
    assert spec.requires_problem
    assert spec.certificate_schema.name == "factorization"
    assert spec.certificate_schema.version == "1"
    assert spec.certificate_schema.certificate_type is (
        FactorizationCertificate
    )
    assert runtime.table.lookup("HasFactorization") is not None
    assert (
        runtime.signature.operator_of(found.vocabulary.symbol)
        is not None
    )


def test_elementary_bootstrap_registers_the_same_operation_and_checker():
    runtime = bootstrap_elementary()
    found = operation(runtime)
    assert runtime.store.checkers.get(found.checker_id) is not None
    workspace = new_workspace(runtime)
    result = workspace.factor_polynomial(
        source(workspace, runtime, "x^2 - 1"), runtime.variable
    )
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None


def test_the_workspace_records_the_structured_factorization(runtime):
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "x^2 - 1")
    result = workspace.factor_polynomial(first, runtime.variable)
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert result.structured is not None
    assert result.structured.kind == "factorization"
    assert tuple(name for name, _ in result.structured.components) == (
        "unit",
        "factors",
    )
    recorded = workspace.structured_result(result.result)
    assert recorded is result.structured
    candidate = result.candidate
    assert candidate is not None
    found = operation(runtime)
    claim = parse_factorization(
        found.vocabulary, candidate.specifications[0].term
    )
    assert claim is not None
    assert claim.unit == T.number(1)
    assert result.task is not None
    assert result.task.state is TaskState.COMPLETED


def test_a_manual_factorization_problem_runs_to_completion(runtime):
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "x^4 + 1")
    task = workspace.define_problem(
        "factor_polynomial",
        (first,),
        target=runtime.variable,
        coverage=Coverage.ONE_VERIFIED,
    )
    assert task.state is TaskState.READY
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert result.structured is not None
    assert workspace.structured_result(result.result) is (
        result.structured
    )
    assert workspace.tasks()[-1].state is TaskState.COMPLETED


def test_a_zero_manual_problem_is_blocked_and_cannot_run(runtime):
    workspace = new_workspace(runtime)
    zero = source(workspace, runtime, "0")
    task = workspace.define_problem(
        "factor_polynomial",
        (zero,),
        target=runtime.variable,
        coverage=Coverage.ONE_VERIFIED,
    )
    assert task.state is TaskState.BLOCKED
    assert task.blocker is not None
    assert task.blocker.missing == frozenset({"nonzero_polynomial"})
    before = runtime.store.stats()
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.INVALID
    assert result.candidate is None
    assert runtime.store.stats() == before


def test_check_and_decide_reverify_the_recorded_candidate(runtime):
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "6*x^2 + 5*x + 1")
    result = workspace.factor_polynomial(first, runtime.variable)
    assert result.status is OperationStatus.VERIFIED, result.detail
    candidate = result.candidate
    assert candidate is not None
    checked = workspace.check_candidate(candidate.id)
    assert checked.status is OperationStatus.VERIFIED, checked.detail
    assert checked.result is not None
    assert checked.result.term == candidate.term
    verdict = workspace.decide_candidate(candidate.id)
    assert isinstance(verdict, VerdictYes)
    assert verdict.receipt.checker_id == "algebra.factorization"
    assert runtime.store.stats()["judgments"] >= 2


def test_the_session_factor_command_publishes_the_visible_product():
    session = Session(bootstrap())
    assert session.execute("x^2 - 1") == "@E0: x^2 - 1"
    answer = session.execute("factor @E0")
    assert answer == "verified @E1: (-1 + x)*(1 + x)"
    assert session.execute("show @E1") == "@E1: (-1 + x)*(1 + x)"
    assert session.execute("factor") == "verified @E2: (-1 + x)*(1 + x)"
    session.execute("x^4 + 1")
    nonlinear = session.execute("factor @E3")
    assert nonlinear == "verified @E4: 1 + x^4"


def test_the_session_history_and_time_travel_keep_the_factorization(runtime):
    session = Session(runtime)
    session.execute("x^2 - 1")
    session.execute("factor @E0")
    lines = [
        line
        for line in session.history()
        if line.split()[1].startswith("factor_polynomial")
    ]
    assert len(lines) == 1
    line = lines[0]
    assert "factor_polynomial@1" in line
    assert "inputs=[@E0]" in line
    assert "parameters=[]" in line
    assert "status=verified" in line
    assert "actor=user" in line
    assert session.execute("undo").startswith("undo: @E0 ")
    result = session.workspace.expressions()[-1]
    assert session.workspace.structured_result(result) is None
    assert session.execute("redo").startswith("redo: @E1 ")
    result = session.workspace.expressions()[-1]
    structured = session.workspace.structured_result(result)
    assert structured is not None
    assert tuple(name for name, _ in structured.components) == (
        "unit",
        "factors",
    )


def test_refusals_write_nothing_to_the_kernel(runtime):
    workspace = new_workspace(runtime)
    for text in ("0", "x^-1"):
        before = runtime.store.stats()
        result = workspace.factor_polynomial(
            source(workspace, runtime, text), runtime.variable
        )
        assert result.status is OperationStatus.UNSUPPORTED
        assert result.candidate is None
        assert result.result is None
        assert result.task is not None
        assert result.task.state is TaskState.BLOCKED
        assert runtime.store.stats() == before


def test_object_show_and_list_display_the_factorization(runtime):
    session = Session(runtime)
    session.execute("x^2 - 1")
    session.execute("factor @E0")
    assert session.execute("object @E1") == (
        "@E1: (-1 + x)*(1 + x) "
        "[artifact=term; operation=factor_polynomial]"
    )
    listing = session.execute("list")
    assert "@E1: (-1 + x)*(1 + x)" in listing
    candidates = session.execute("candidates")
    assert candidates.startswith("C0: (-1 + x)*(1 + x)")
    assert "state=verified" in candidates
