"""Alias expansion: the only automatic substitution channel.

A definition is an alias, not an equation. Expansion follows aliases only, is
capture-safe under binders, and terminates because the frame store rejects every
definition that refers to itself or to a later alias.

Equations are never expanded here. Using an assumption as a rewrite rule is a
different, explicit act that carries a proof.
"""

from __future__ import annotations

from cas.foundation.ids import FrameId, SymbolId
from cas.semantics.frames import FrameStore
from cas.syntax import binding as B
from cas.syntax import term as T

_EXPANSION_LIMIT = 1000


class DefinitionError(Exception):
    """Alias expansion did not terminate, which marks a broken invariant."""


def _visible_definitions(
    frames: FrameStore,
    frame: FrameId,
    term: T.Term,
) -> dict[SymbolId, T.Term]:
    mapping: dict[SymbolId, T.Term] = {}
    for symbol_id in B.free_symbols(term):
        definition = frames.lookup_definition(frame, symbol_id)
        if definition is not None:
            mapping[symbol_id] = definition.body
    return mapping


def expand(
    frames: FrameStore,
    frame: FrameId,
    term: T.Term,
    limit: int = _EXPANSION_LIMIT,
) -> T.Term:
    """Replace every visible alias by its body, to a fixed point."""
    current = term
    for _ in range(limit):
        mapping = _visible_definitions(frames, frame, current)
        if not mapping:
            return current
        current = B.substitute_free(current, mapping)
    # The last rewrite may have been the one that finished the job.
    if not _visible_definitions(frames, frame, current):
        return current
    raise DefinitionError("alias expansion did not reach a fixed point")


__all__ = ["DefinitionError", "expand"]
