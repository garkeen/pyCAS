"""Constructors shared by the v5 tests.

These helpers only assemble already-public pieces; they never bypass a seal or a
validation that production code performs.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING

from cas.foundation.ids import FrameId, SymbolId, WorldId
from cas.kernel.commit import (
    ValidatedCommitBatch,
    publish_commit,
    validate_commit,
)
from cas.kernel.evidence import AlgebraService, VerificationContext
from cas.kernel.trust import BasisKind, BasisRef
from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.declarations import DeclarationSet
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics import elaborate
from cas.semantics.bridge import Rendered, ViewBuilt
from cas.semantics.frames import FrameSorts, FrameStore
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


class MapEnvironment:
    """An explicit symbol-to-sort table for typing tests."""

    def __init__(self, sorts: Mapping[SymbolId, S.Sort] | None = None) -> None:
        self._sorts: dict[SymbolId, S.Sort] = dict(sorts or {})

    def declare(self, symbol_id: SymbolId, sort: S.Sort) -> SymbolId:
        self._sorts[symbol_id] = sort
        return symbol_id

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        return self._sorts.get(symbol_id)

    def bound_sort(self, index: int) -> S.Sort | None:
        del index
        return None


def structural(signature: LanguageSignature, head: StructuralHead) -> T.SymbolRef:
    """The term-level symbol this world uses for a structural head."""
    identifier = signature.symbol_of(head)
    assert identifier is not None, f"the language has no symbol for {head}"
    return T.symbol(identifier, head.value)


def head_app(
    signature: LanguageSignature,
    head: StructuralHead,
    *arguments: T.Term,
) -> T.Apply:
    return T.app(structural(signature, head), *arguments)


def check_in(
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    term: T.Term,
) -> Pr.PropositionOutcome:
    return Pr.check(
        term,
        signature,
        FrameSorts(frames, frame),
        frames.get(frame).meaning,
    )


def typed_in(
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    term: T.Term,
) -> Ty.TypedExpr:
    """Issue the typed view of one test input without bypassing the seal."""
    outcome = elaborate.typed(term, frames, frame, signature)
    assert isinstance(outcome, Ty.TypedExpr), outcome
    return outcome


def admitted(runtime, term, *, frame=None, bridge=None, request=None):
    """Admit one test term through the production algebra bridge.

    The term is elaborated in `frame` and converted under `request`; a typing
    failure stays distinct from a bridge refusal.  `bridge` and `request` let a
    test use a runtime's non-default view (for example its specialization
    bridge) without copying any conversion logic.
    """
    identifier = runtime.frame.id if frame is None else frame
    typed = elaborate.typed(term, runtime.frames, identifier, runtime.signature)
    if not isinstance(typed, Ty.TypedExpr):
        return typed
    actual_bridge = runtime.bridge if bridge is None else bridge
    actual_request = runtime.request if request is None else request
    return actual_bridge.to_view(typed, actual_request)


def view_of(runtime, term, *, frame=None, bridge=None, request=None):
    """The algebra view `admitted` issues for one accepted test term."""
    outcome = admitted(
        runtime, term, frame=frame, bridge=bridge, request=request
    )
    assert isinstance(outcome, ViewBuilt), outcome
    return outcome.view


def render_value(runtime, value, *, view=None, bridge=None) -> T.Term:
    """Render one parent element through the production bridge."""
    actual_bridge = runtime.bridge if bridge is None else bridge
    if view is None:
        view = view_of(runtime, T.number(1), bridge=actual_bridge)
    outcome = actual_bridge.render(view, value)
    assert isinstance(outcome, Rendered), outcome
    return outcome.term


def require_proposition(outcome: Pr.PropositionOutcome) -> Pr.Proposition:
    assert isinstance(outcome, Pr.Proposition), outcome
    return outcome


def proposition_in(
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    term: T.Term,
) -> Pr.Proposition:
    return require_proposition(check_in(frames, frame, signature, term))


def elementary_basis(
    source: DeclarationSet,
    world: WorldId = WorldId(0),
) -> BasisRef:
    """The admission record a basis-loaded elementary source must carry."""
    assert source.digest, "a loaded source carries its content digest"
    return BasisRef(
        source.name,
        BasisKind.DECLARATION_FILE,
        "1",
        source.digest,
        world,
    )


def variable(runtime: Runtime) -> T.SymbolRef:
    """The runtime's differentiation variable as a term."""
    return T.symbol(runtime.variable, runtime.table.name_of(runtime.variable))


def runtime_proposition(
    runtime: Runtime,
    term: T.Term,
    frame: FrameId | None = None,
) -> Pr.Proposition:
    identifier = runtime.frame.id if frame is None else frame
    return proposition_in(runtime.frames, identifier, runtime.signature, term)


def verification_context(
    runtime: Runtime,
    frame: FrameId | None = None,
    *,
    algebra: AlgebraRequest | None = None,
) -> VerificationContext:
    """The trusted context the kernel builds for `runtime`'s frame.

    `algebra` is the fixed request the kernel would derive from a mathematical
    proposal.  A function problem carries none, so the default stays `None`.
    """
    identifier = runtime.frame.id if frame is None else frame
    return VerificationContext(
        runtime.world.id,
        identifier,
        runtime.frames,
        algebra=None if algebra is None else AlgebraService(algebra),
    )


def equation(
    runtime: Runtime,
    left: T.Term,
    right: T.Term,
    frame: FrameId | None = None,
) -> Pr.Proposition:
    term = head_app(runtime.signature, StructuralHead.EQ, left, right)
    return runtime_proposition(runtime, term, frame)


def commit_now(store, proposal):
    """Validate and immediately publish one proposal for a test."""
    outcome = validate_commit(store, proposal)
    if isinstance(outcome, ValidatedCommitBatch):
        return publish_commit(store, outcome)
    return outcome
