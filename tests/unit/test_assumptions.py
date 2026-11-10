"""Frame-scoped assumptions in the workspace and session."""

import pytest
from support import head_app, variable

from cas.foundation.ids import FrameId, SymbolId
from cas.frontend.errors import SessionError
from cas.frontend.session import Session
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.signatures import StructuralHead
from cas.runtime import bootstrap
from cas.semantics import elaborate
from cas.semantics.frames import Declaration, Definition
from cas.syntax import term as T
from cas.workflow.records import (
    DeclarationResult,
    DefinitionResult,
    OperationStatus,
)
from cas.workflow.workspace import Workspace


def gt_zero(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.GT,
        variable(runtime),
        T.number(0),
    )


def square(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.POWER,
        variable(runtime),
        T.number(2),
    )


def test_assume_creates_a_child_frame_and_a_hypothesis_judgment():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    result = workspace.assume(gt_zero(runtime))
    assert result.status is OperationStatus.VERIFIED
    assert result.judgment is not None
    assert result.frame != runtime.frame.id
    assert workspace.frame == result.frame
    assert result.proposition is not None
    assert result.proposition in runtime.frames.assumptions(workspace.frame)
    judgment = runtime.store.get_judgment(result.judgment)
    assert judgment.proposition == result.proposition
    inference = runtime.store.inference_of(result.judgment)
    assert inference.checker_id == "kernel.hypothesis"
    assert [event.operation for event in workspace.events()] == ["Assume"]


def test_operations_use_the_current_assumption_frame():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    source = workspace.intake(square(runtime), "source")
    result = workspace.assume(gt_zero(runtime))
    differentiated = workspace.differentiate(source, runtime.variable)
    assert differentiated.status is OperationStatus.VERIFIED
    assert differentiated.candidate is not None
    assert differentiated.candidate.frame == result.frame
    assert differentiated.verifications
    assert (
        differentiated.verifications[0].specification.meaning.frame
        == result.frame
    )
    assert differentiated.result is not None
    assert differentiated.result.frame == result.frame


def test_assume_rejects_non_propositions_and_keeps_the_frame():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    invalid = workspace.assume(T.number(1))
    assert invalid.status is OperationStatus.INVALID
    assert workspace.frame == runtime.frame.id

    first = workspace.assume(gt_zero(runtime))
    assert first.status is OperationStatus.VERIFIED
    assert workspace.frame == first.frame


def test_undo_and_redo_move_the_frame_but_keep_the_ledger():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    initial = workspace.frame
    result = workspace.assume(gt_zero(runtime))
    judgment = result.judgment
    assert workspace.undo()
    assert workspace.frame == initial
    assert runtime.store.get_judgment(judgment) is not None
    assert workspace.redo()
    assert workspace.frame == result.frame


def test_the_session_accepts_assumptions():
    runtime = bootstrap()
    session = Session(runtime)
    assert session.execute("assume x > 0") == "assumed: x > 0"
    frame = session.workspace.frame
    assert frame != runtime.frame.id
    assert session.execute("x^2") == "@E0: x^2"
    assert session.workspace.expressions()[0].frame == frame
    assert session.execute("diff") == "verified @E1: 2*x"

    with pytest.raises(SessionError):
        session.execute("assume")
    assert session.execute("assume x + 1") == (
        "invalid: the hypothesis is not a proposition"
    )
    # The same text in a child frame is a proposition with another meaning;
    # scope rules do not merge it by spelling.
    assert session.execute("assume x > 0") == "assumed: x > 0"
    assert session.workspace.frame != frame


def test_contradictory_assumptions_stop_the_session():
    runtime = bootstrap()
    session = Session(runtime)
    assert session.execute("assume x > 0") == "assumed: x > 0"
    consistent_frame = session.workspace.frame

    output = session.execute("assume not x > 0")
    assert output.startswith("invalid:")
    assert "contradiction" in output
    inconsistent_frame = session.workspace.frame
    assert runtime.store.consistency(
        inconsistent_frame
    ).is_inconsistent()
    assert session.execute("assume x > 0").startswith("invalid:")

    assert session.execute("x^2") == "@E0: x^2"
    before = runtime.store.stats()
    assert session.execute("diff").startswith("invalid:")
    assert runtime.store.stats() == before

    assert session.execute("undo") == (
        "undo: empty view (assume Not(Gt(x, 0)))"
    )
    assert session.workspace.frame == inconsistent_frame
    assert session.execute("undo") == "undo: empty view (assume Gt(x, 0))"
    assert session.workspace.frame == consistent_frame
    assert not runtime.store.consistency(
        consistent_frame
    ).is_inconsistent()


def plus_one(runtime):
    return head_app(
        runtime.signature,
        StructuralHead.PLUS,
        variable(runtime),
        T.number(1),
    )


def test_declare_creates_a_child_frame_with_a_declaration():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    result = workspace.declare("a", S.REAL)
    assert isinstance(result, DeclarationResult)
    assert result.status is OperationStatus.VERIFIED
    assert result.detail == ""
    assert result.declaration is not None
    assert result.declaration.name == "a"
    assert result.declaration.sort is S.REAL
    assert result.frame != runtime.frame.id
    assert workspace.frame == result.frame
    child = runtime.frames.get(result.frame)
    assert child.declarations == (result.declaration,)
    assert (
        runtime.frames.sort_of(
            result.frame, result.declaration.symbol_id
        )
        is S.REAL
    )
    assert [event.operation for event in workspace.events()] == ["Declare"]
    assert workspace.revision.frame == result.frame
    assert runtime.store.stats()["judgments"] == 0

    symbol = runtime.table.lookup("a")
    assert symbol is not None
    expression = workspace.intake(T.symbol(symbol, "a"), "a")
    assert expression.frame == result.frame
    typed = elaborate.typed(
        expression.term,
        runtime.frames,
        workspace.frame,
        runtime.signature,
    )
    assert isinstance(typed, Ty.TypedExpr)
    assert typed.sort is S.REAL


def test_a_duplicate_declaration_is_refused_without_a_new_revision():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    first = workspace.declare("a", S.REAL)
    assert first.status is OperationStatus.VERIFIED
    revision = workspace.revision.id
    frames = runtime.frames.count()

    duplicate = workspace.declare("a", S.INTEGER)
    assert duplicate.status is OperationStatus.INVALID
    assert duplicate.frame == workspace.frame == first.frame
    assert duplicate.declaration is None
    assert duplicate.detail
    assert workspace.revision.id == revision
    assert runtime.frames.count() == frames
    assert [event.operation for event in workspace.events()] == ["Declare"]


def test_define_creates_a_child_frame_and_expands_the_alias():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    body = plus_one(runtime)
    result = workspace.define("f", body)
    assert isinstance(result, DefinitionResult)
    assert result.status is OperationStatus.VERIFIED
    assert result.detail == ""
    assert result.definition is not None
    assert result.definition.name == "f"
    assert result.definition.body == body
    assert result.frame != runtime.frame.id
    assert workspace.frame == result.frame
    child = runtime.frames.get(result.frame)
    assert child.definitions == (result.definition,)
    assert [event.operation for event in workspace.events()] == ["Define"]
    assert workspace.revision.frame == result.frame
    assert runtime.store.stats()["judgments"] == 0

    symbol = runtime.table.lookup("f")
    assert symbol is not None
    expression = workspace.intake(T.symbol(symbol, "f"), "f")
    typed = elaborate.typed(
        expression.term,
        runtime.frames,
        workspace.frame,
        runtime.signature,
    )
    assert isinstance(typed, Ty.TypedExpr)
    assert typed.term == body

    differentiated = workspace.differentiate(expression, runtime.variable)
    assert differentiated.status is OperationStatus.VERIFIED
    assert differentiated.result is not None
    assert differentiated.result.term == T.number(1)


def test_self_reference_and_forward_aliases_are_refused():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    revision = workspace.revision.id
    frames = runtime.frames.count()

    self_symbol = runtime.table.intern("f")
    self_body = head_app(
        runtime.signature,
        StructuralHead.PLUS,
        T.symbol(self_symbol, "f"),
        T.number(1),
    )
    refused = workspace.define("f", self_body)
    assert refused.status is OperationStatus.INVALID
    assert refused.frame == workspace.frame == runtime.frame.id
    assert refused.definition is None
    assert refused.detail

    later = runtime.table.intern("h")
    forward = workspace.define("g", T.symbol(later, "h"))
    assert forward.status is OperationStatus.INVALID
    assert forward.frame == runtime.frame.id
    assert forward.definition is None
    assert workspace.revision.id == revision
    assert runtime.frames.count() == frames
    assert workspace.events() == ()

    later_definition = workspace.define("h", T.number(1))
    assert later_definition.status is OperationStatus.VERIFIED
    assert later_definition.definition is not None
def test_ill_scoped_and_ill_typed_definition_bodies_are_refused():
    runtime = bootstrap()
    workspace = Workspace(runtime)
    revision = workspace.revision.id
    frames = runtime.frames.count()

    scoped = workspace.define("f", T.BoundVar(0))
    assert scoped.status is OperationStatus.INVALID
    assert scoped.definition is None
    assert scoped.frame == runtime.frame.id

    ill_typed = workspace.define(
        "f",
        head_app(
            runtime.signature,
            StructuralHead.PLUS,
            T.number(1),
            T.TRUE,
        ),
    )
    assert ill_typed.status is OperationStatus.INVALID
    assert ill_typed.definition is None
    assert workspace.revision.id == revision
    assert runtime.frames.count() == frames
    assert workspace.events() == ()


def test_declare_and_define_roll_back_partial_records(runtime, monkeypatch):
    workspace = Workspace(runtime)
    revision = workspace.revision.id
    frames = runtime.frames.count()

    def fail(*args, **kwargs):
        raise RuntimeError("recording failed")

    monkeypatch.setattr(workspace, "_append_revision", fail)
    with pytest.raises(RuntimeError):
        workspace.declare("a", S.REAL)
    assert runtime.frames.count() == frames
    assert workspace.revision.id == revision
    assert workspace.events() == ()

    monkeypatch.undo()
    workspace = Workspace(runtime)
    revision = workspace.revision.id
    frames = runtime.frames.count()
    monkeypatch.setattr(workspace, "_append_revision", fail)
    with pytest.raises(RuntimeError):
        workspace.define("f", plus_one(runtime))
    assert runtime.frames.count() == frames
    assert workspace.revision.id == revision
    assert workspace.events() == ()


def test_context_extension_results_enforce_status_and_payload():
    declaration = Declaration(SymbolId(1), "a", S.REAL)
    definition = Definition(SymbolId(2), "f", T.number(1))
    with pytest.raises(ValueError):
        DeclarationResult(OperationStatus.VERIFIED, FrameId(2), None)
    with pytest.raises(ValueError):
        DeclarationResult(OperationStatus.INVALID, FrameId(2), declaration)
    with pytest.raises(TypeError):
        DeclarationResult(OperationStatus.VERIFIED, FrameId(2), "a")
    with pytest.raises(ValueError):
        DefinitionResult(OperationStatus.VERIFIED, FrameId(2), None)
    with pytest.raises(ValueError):
        DefinitionResult(OperationStatus.INVALID, FrameId(2), definition)
    with pytest.raises(TypeError):
        DefinitionResult(OperationStatus.VERIFIED, FrameId(2), "f")
