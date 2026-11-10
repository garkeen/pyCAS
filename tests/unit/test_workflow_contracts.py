"""Workflow state/result invariants that are not closed yet."""

import pytest
from support import runtime_proposition, variable

from cas.foundation.ids import (
    CandidateId,
    EventId,
    FrameId,
    JudgmentId,
    ObjectVersionId,
    RevisionId,
    TaskId,
    WorldId,
)
from cas.language.decisions import Blocker, Reason
from cas.language.problems import Coverage
from cas.syntax import term as T
from cas.syntax.occurrences import Occurrence
from cas.workflow.records import (
    Candidate,
    CandidateFocus,
    CandidateState,
    Event,
    ObjectFocus,
    OccurrenceFocus,
    OperationResult,
    OperationStatus,
    Revision,
    TaskFocus,
    TaskRecord,
    TaskState,
    VerificationLink,
)
from cas.workflow.workspace import Workspace


def _defined_task(runtime):
    workspace = Workspace(runtime)
    source = workspace.intake(variable(runtime))
    return workspace.define_problem(
        "differentiate",
        (source,),
        target=runtime.variable,
    )


def test_task_record_rejects_completed_without_candidates(runtime):
    task = _defined_task(runtime)
    with pytest.raises(ValueError):
        TaskRecord(
            TaskId(999),
            task.problem,
            task.frame,
            state=TaskState.COMPLETED,
        )


def test_task_record_rejects_blocked_without_blocker(runtime):
    task = _defined_task(runtime)
    with pytest.raises(ValueError):
        TaskRecord(
            TaskId(999),
            task.problem,
            task.frame,
            state=TaskState.BLOCKED,
        )


def test_operation_result_rejects_verified_without_candidate():
    with pytest.raises(ValueError):
        OperationResult(
            "differentiate",
            OperationStatus.VERIFIED,
            None,
            (),
            None,
        )


def test_event_records_its_input_output_and_execution_report():
    event = Event(
        EventId(1),
        "differentiate",
        input_revision=RevisionId(2),
        frame=FrameId(3),
        inputs=(ObjectVersionId(4),),
        parameters=(("mode", "fast"),),
        output_revision=RevisionId(5),
        execution_report=OperationStatus.VERIFIED,
    )
    assert event.input_revision == RevisionId(2)
    assert event.frame == FrameId(3)
    assert event.inputs == (ObjectVersionId(4),)
    assert event.parameters == (("mode", "fast"),)
    assert event.output_revision == RevisionId(5)
    assert event.execution_report is OperationStatus.VERIFIED


def test_event_rejects_an_invalid_input_revision():
    with pytest.raises(TypeError):
        Event(EventId(1), "Test", input_revision="r1")


def test_event_rejects_an_invalid_frame():
    with pytest.raises(TypeError):
        Event(EventId(1), "Test", frame="f1")


def test_event_rejects_an_invalid_output_revision():
    with pytest.raises(TypeError):
        Event(EventId(1), "Test", output_revision="r1")


def test_event_rejects_an_invalid_execution_report():
    with pytest.raises(TypeError):
        Event(EventId(1), "Test", execution_report="verified")


def test_event_rejects_a_non_version_input():
    with pytest.raises(TypeError):
        Event(EventId(1), "Test", inputs=("v1",))


def test_event_rejects_an_empty_parameter_name():
    with pytest.raises(ValueError):
        Event(EventId(1), "Test", parameters=(("", 1),))


def test_revision_records_its_world_and_producing_event():
    revision = Revision(
        RevisionId(1),
        FrameId(2),
        (),
        (),
        (),
        "start",
        world=WorldId(3),
        producing_event=EventId(4),
    )
    assert revision.world == WorldId(3)
    assert revision.producing_event == EventId(4)


def test_revision_defaults_its_producing_event_to_none():
    revision = Revision(
        RevisionId(1),
        FrameId(2),
        (),
        (),
        (),
        "start",
        world=WorldId(3),
    )
    assert revision.world == WorldId(3)
    assert revision.producing_event is None


def test_revision_rejects_an_invalid_world():
    with pytest.raises(TypeError):
        Revision(
            RevisionId(1),
            FrameId(2),
            (),
            (),
            (),
            "start",
            world="w1",
        )


def test_revision_rejects_an_invalid_producing_event():
    with pytest.raises(TypeError):
        Revision(
            RevisionId(1),
            FrameId(2),
            (),
            (),
            (),
            "start",
            world=WorldId(3),
            producing_event="e1",
        )


def test_focus_variants_record_their_target():
    occurrence = Occurrence((1, 2))
    assert ObjectFocus(ObjectVersionId(3)).version == ObjectVersionId(3)
    assert TaskFocus(TaskId(4)).task == TaskId(4)
    assert CandidateFocus(CandidateId(5)).candidate == CandidateId(5)
    focus = OccurrenceFocus(ObjectVersionId(6), occurrence)
    assert focus.version == ObjectVersionId(6)
    assert focus.occurrence == occurrence


@pytest.mark.parametrize(
    "factory",
    [ObjectFocus, TaskFocus, CandidateFocus],
)
def test_focus_variants_reject_a_non_identifier(factory):
    with pytest.raises(TypeError):
        factory("not-an-id")


def test_occurrence_focus_rejects_a_non_occurrence():
    with pytest.raises(TypeError):
        OccurrenceFocus(ObjectVersionId(1), "0.1")


def test_revision_records_its_focus():
    revision = Revision(
        RevisionId(1),
        FrameId(2),
        (),
        (),
        (),
        "start",
        world=WorldId(3),
        focus=TaskFocus(TaskId(4)),
    )
    assert revision.focus == TaskFocus(TaskId(4))


def test_revision_defaults_its_focus_to_none():
    revision = Revision(
        RevisionId(1),
        FrameId(2),
        (),
        (),
        (),
        "start",
        world=WorldId(3),
    )
    assert revision.focus is None


def test_revision_rejects_an_invalid_focus():
    with pytest.raises(TypeError):
        Revision(
            RevisionId(1),
            FrameId(2),
            (),
            (),
            (),
            "start",
            world=WorldId(3),
            focus="object:v1",
        )


def _specification(runtime):
    return runtime_proposition(runtime, T.TRUE)


def test_a_verified_link_needs_a_judgment(runtime):
    with pytest.raises(ValueError, match="needs a judgment"):
        VerificationLink(
            CandidateId(1),
            _specification(runtime),
            None,
            OperationStatus.VERIFIED,
            "HasDerivative",
            FrameId(2),
            Coverage.ONE_VERIFIED,
        )
    with pytest.raises(ValueError, match="needs a judgment"):
        VerificationLink(
            CandidateId(1),
            _specification(runtime),
            None,
            OperationStatus.CONDITIONAL,
            "HasDerivative",
            FrameId(2),
            Coverage.ONE_VERIFIED,
        )
    link = VerificationLink(
        CandidateId(1),
        _specification(runtime),
        JudgmentId(3),
        OperationStatus.VERIFIED,
        "HasDerivative",
        FrameId(2),
        Coverage.ONE_VERIFIED,
    )
    assert link.judgment == JudgmentId(3)


def test_a_verified_candidate_needs_specifications_checker_and_certificate(
    runtime,
):
    task = _defined_task(runtime)
    with pytest.raises(ValueError, match="specification"):
        Candidate(
            CandidateId(1),
            task.id,
            task.problem,
            T.TRUE,
            task.frame,
            CandidateState.VERIFIED,
        )
    with pytest.raises(ValueError, match="checker"):
        Candidate(
            CandidateId(1),
            task.id,
            task.problem,
            T.TRUE,
            task.frame,
            CandidateState.VERIFIED,
            specifications=(_specification(runtime),),
            certificate=object(),
        )
    with pytest.raises(ValueError, match="certificate"):
        Candidate(
            CandidateId(1),
            task.id,
            task.problem,
            T.TRUE,
            task.frame,
            CandidateState.VERIFIED,
            specifications=(_specification(runtime),),
            checker_id="test.checker",
        )


def test_a_completed_task_cannot_carry_a_blocker(runtime):
    task = _defined_task(runtime)
    with pytest.raises(ValueError, match="blocker"):
        TaskRecord(
            TaskId(999),
            task.problem,
            task.frame,
            state=TaskState.COMPLETED,
            candidates=(CandidateId(1),),
            blocker=Blocker(Reason.FRAGMENT, "stale blocker"),
        )
    with pytest.raises(ValueError, match="blocker"):
        TaskRecord(
            TaskId(999),
            task.problem,
            task.frame,
            state=TaskState.COMPLETED_CONDITIONAL,
            candidates=(CandidateId(1),),
            blocker=Blocker(Reason.GUARDED, "stale blocker"),
        )


def test_a_refuted_link_does_not_need_a_judgment(runtime):
    link = VerificationLink(
        CandidateId(1),
        _specification(runtime),
        None,
        OperationStatus.REFUTED,
        "HasDerivative",
        FrameId(2),
        Coverage.ONE_VERIFIED,
    )
    assert link.judgment is None


def test_an_occurrence_expectation_must_be_a_term():
    with pytest.raises(TypeError):
        Occurrence((0,), "x")
