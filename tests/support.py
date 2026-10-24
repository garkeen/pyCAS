"""Constructors shared by the v5 tests.

These helpers only assemble already-public pieces; they never bypass a seal or a
validation that production code performs.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING

from cas.foundation.ids import FrameId, SymbolId
from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics.frames import FrameSorts, FrameStore
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


def equation(
    runtime: Runtime,
    left: T.Term,
    right: T.Term,
    frame: FrameId | None = None,
) -> Pr.Proposition:
    term = head_app(runtime.signature, StructuralHead.EQ, left, right)
    return runtime_proposition(runtime, term, frame)
