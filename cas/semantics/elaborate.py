"""Elaboration: expand aliases, then type or issue a proposition.

Expansion happens before typing, so a defined symbol is seen through its body.
The issued `Proposition` therefore carries an alias-free term: a deliberate
simplification of the first vertical slice, which keeps stored conclusions
independent of later definition edits.
"""

from __future__ import annotations

from cas.foundation.ids import FrameId
from cas.language import propositions as Pr
from cas.language import typing as Ty
from cas.language.signatures import LanguageSignature
from cas.semantics.definitions import expand
from cas.semantics.frames import FrameSorts, FrameStore
from cas.syntax import term as T


def typing(
    term: T.Term,
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
) -> Ty.Typing:
    """The sort of a term in `frame`, after alias expansion."""
    expanded = expand(frames, frame, term)
    return Ty.infer(expanded, signature, FrameSorts(frames, frame))


def proposition(
    term: T.Term,
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
) -> Pr.PropositionOutcome:
    """Issue a proposition read in `frame`, after alias expansion."""
    expanded = expand(frames, frame, term)
    return Pr.check(
        expanded,
        signature,
        FrameSorts(frames, frame),
        frames.get(frame).meaning,
    )


__all__ = ["proposition", "typing"]
