"""The rational-logarithmic integration vertical slice.

The low-level residual search, specification and independent checker are
exercised by their unit slices.  This file follows one request through the
elementary bootstrap, the workspace, the kernel and the session: the operation
must be registered only there, every accepted claim must be re-proved by the
checker, and every refusal must leave the ledger untouched.
"""

from support import head_app, runtime_proposition, variable

from cas.frontend import parse
from cas.frontend.session import Session
from cas.kernel.verdict import VerdictYes
from cas.language.decisions import Reason
from cas.language.problems import Coverage
from cas.language.signatures import StructuralHead
from cas.math.calculus.integration.logarithmic_checker import (
    LogarithmicIntegrationChecker,
)
from cas.math.calculus.integration.logarithmic_operation import (
    LogarithmicIntegrationOperation,
)
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogAntiderivativeCertificate,
    certificate_matches_claim,
    parse_rational_log_antiderivative,
)
from cas.runtime.bootstrap import (
    bootstrap,
    bootstrap_elementary,
    bootstrap_parameterized,
    new_workspace,
)
from cas.syntax import term as T
from cas.workflow.records import OperationStatus, TaskState


def source(workspace, runtime, text):
    return workspace.intake(parse(text, runtime.table, runtime.signature), text)


def operation(runtime) -> LogarithmicIntegrationOperation:
    found = runtime.operations.get("integrate_rational_logarithmic")
    assert isinstance(found, LogarithmicIntegrationOperation)
    return found


def test_only_the_elementary_assembly_registers_the_fragment():
    for runtime in (bootstrap(), bootstrap_parameterized()):
        assert (
            runtime.operations.get("integrate_rational_logarithmic") is None
        )
        assert runtime.table.lookup("HasRationalLogAntiderivative") is None
        assert runtime.table.lookup("log") is None

    runtime = bootstrap_elementary()
    found = operation(runtime)
    assert found.id == "integrate_rational_logarithmic"
    assert found.version == "1"
    assert found.problem_kind == "integrate_rational_logarithmic"
    assert found.specification_kind == "HasRationalLogAntiderivative"
    assert runtime.table.lookup("HasRationalLogAntiderivative") is not None
    assert runtime.table.lookup("log") is not None
    checker_id = found.checker_bindings[0].checker_id
    spec = runtime.store.checkers.spec(checker_id)
    assert spec is not None
    assert isinstance(spec.checker, LogarithmicIntegrationChecker)
    assert spec.requires_problem


def test_the_workspace_verifies_the_declared_fragment():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    for text in ("1/x", "1/(x^2-1)", "2*x/(x^2+1)"):
        first = source(workspace, runtime, text)
        before = runtime.store.stats()["judgments"]
        result = workspace.integrate_rational_logarithmic(
            first, runtime.variable
        )
        assert result.status in (
            OperationStatus.VERIFIED,
            OperationStatus.CONDITIONAL,
        ), (text, result.detail)
        assert result.result is not None
        assert result.candidate is not None
        assert result.verifications
        assert (
            result.verifications[0].status is OperationStatus.VERIFIED
        )
        assert runtime.store.stats()["judgments"] == before + 1
        assert result.structured is not None
        assert tuple(name for name, _ in result.structured.components) == (
            "polynomial_part",
            "log_terms",
        )
        assert workspace.structured_result(result.result) is (
            result.structured
        )


def test_the_result_claim_and_certificate_agree():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "1/(x^2-1)")
    result = workspace.integrate_rational_logarithmic(
        first, runtime.variable
    )
    assert result.status is OperationStatus.CONDITIONAL, result.detail
    candidate = result.candidate
    assert candidate is not None
    assert result.structured is not None
    assert result.result is not None

    found = operation(runtime)
    claim = parse_rational_log_antiderivative(
        found.vocabulary, candidate.specifications[0].term
    )
    assert claim is not None
    assert claim.source == first.term
    assert claim.variable.symbol_id == runtime.variable
    certificate = candidate.certificate
    assert isinstance(certificate, RationalLogAntiderivativeCertificate)
    assert certificate_matches_claim(certificate, claim)
    components = dict(result.structured.components)
    assert components["polynomial_part"] == claim.polynomial_part
    assert components["log_terms"] == claim.log_terms
    assert claim.result == result.result.term == candidate.term
    assert (
        result.verifications[0].specification
        == candidate.specifications[0]
    )


def test_non_rational_residues_are_refused_without_kernel_writes():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "1/(x^2+1)")
    before = runtime.store.stats()
    result = workspace.integrate_rational_logarithmic(
        first, runtime.variable
    )
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.result is None
    assert result.candidate is None
    assert result.structured is None
    assert result.blocker is not None
    assert result.blocker.reason is Reason.FRAGMENT
    assert result.blocker.missing == frozenset(
        {"rational_residues", "algebraic_logarithmic_part"}
    )
    assert result.task is not None
    assert result.task.state is TaskState.BLOCKED
    assert runtime.store.stats() == before


def test_a_manual_problem_runs_to_completion():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "x^2")
    task = workspace.define_problem(
        "integrate_rational_logarithmic",
        (first,),
        target=runtime.variable,
        coverage=Coverage.ONE_VERIFIED,
    )
    assert task.state is TaskState.READY
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.VERIFIED, result.detail
    assert result.result is not None
    assert result.region is None
    assert workspace.tasks()[-1].state is TaskState.COMPLETED


def test_a_non_rational_residue_is_ready_then_unsupported():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "1/(x^2+1)")
    task = workspace.define_problem(
        "integrate_rational_logarithmic",
        (first,),
        target=runtime.variable,
        coverage=Coverage.ONE_VERIFIED,
    )
    assert task.state is TaskState.READY
    before = runtime.store.stats()
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.UNSUPPORTED
    assert result.result is None
    assert result.candidate is None
    assert result.blocker is not None
    assert result.blocker.missing == frozenset(
        {"rational_residues", "algebraic_logarithmic_part"}
    )
    assert workspace.tasks()[-1].state is TaskState.BLOCKED
    assert runtime.store.stats() == before


def test_externalizable_conditions_complete_a_logarithmic_task():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "1/x")
    condition = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(0),
        ),
    )
    task = workspace.define_problem(
        "integrate_rational_logarithmic",
        (first,),
        target=runtime.variable,
        coverage=Coverage.ONE_VERIFIED,
        externalizable=(condition,),
    )
    assert task.state is TaskState.READY
    result = workspace.run_task(task.id)
    assert result.status is OperationStatus.CONDITIONAL, result.detail
    assert result.region is not None
    assert result.region == condition
    assert workspace.tasks()[-1].state is TaskState.COMPLETED_CONDITIONAL


def test_check_and_decide_reverify_the_recorded_candidate():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "1/x")
    result = workspace.integrate_rational_logarithmic(
        first, runtime.variable
    )
    candidate = result.candidate
    assert candidate is not None
    checked = workspace.check_candidate(candidate.id)
    assert checked.status in (
        OperationStatus.VERIFIED,
        OperationStatus.CONDITIONAL,
    ), checked.detail
    assert checked.result is not None
    assert checked.result.term == candidate.term
    verdict = workspace.decide_candidate(candidate.id)
    assert isinstance(verdict, VerdictYes)
    assert verdict.receipt.checker_id == (
        "calculus.integration.rational_logarithmic"
    )


def test_a_requested_region_outside_the_proved_region_is_guarded():
    runtime = bootstrap_elementary()
    workspace = new_workspace(runtime)
    first = source(workspace, runtime, "1/x")
    outside = runtime_proposition(
        runtime,
        head_app(
            runtime.signature,
            StructuralHead.GT,
            variable(runtime),
            T.number(-1),
        ),
    )
    before = runtime.store.stats()
    result = workspace.apply(
        "integrate_rational_logarithmic",
        (first,),
        target=runtime.variable,
        region=outside,
    )
    assert result.status is OperationStatus.UNKNOWN
    assert result.result is None
    assert result.candidate is None
    assert result.blocker is not None
    assert result.blocker.reason is Reason.GUARDED
    assert "region_coverage" in result.blocker.missing
    assert result.blocker.conditions == (outside,)
    assert runtime.store.stats() == before


def test_the_session_integrate_log_command_publishes_the_visible_result():
    session = Session(bootstrap_elementary())
    assert session.execute("1/x") == "@E0: x^-1"
    answer = session.execute("integrate_log @E0")
    assert answer.startswith("verified on ")
    assert "@E1: log(x)" in answer
    assert "condition:" in answer
    assert "integrate_log" in session.execute("help")


def test_the_session_history_and_time_travel_keep_the_decomposition():
    session = Session(bootstrap_elementary())
    session.execute("1/x")
    session.execute("integrate_log @E0")
    lines = [
        line
        for line in session.history()
        if line.split()[1].startswith("integrate_rational_logarithmic")
    ]
    assert len(lines) == 1
    line = lines[0]
    assert "integrate_rational_logarithmic@1" in line
    assert "inputs=[@E0]" in line
    assert "parameters=[]" in line
    assert "status=conditional" in line
    assert "actor=user" in line
    result = session.workspace.expressions()[-1]
    structured = session.workspace.structured_result(result)
    assert structured is not None
    assert tuple(name for name, _ in structured.components) == (
        "polynomial_part",
        "log_terms",
    )
    assert session.execute("undo").startswith("undo: @E0 ")
    assert (
        session.workspace.structured_result(result) is None
    )
    assert session.execute("redo").startswith("redo: @E1 ")
    restored = session.workspace.structured_result(result)
    assert restored is structured
