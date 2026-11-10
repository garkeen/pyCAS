"""Elaboration: expand aliases, then type or issue a proposition.

Expansion happens before typing, so a defined symbol is seen through its body.
The issued `Proposition` or `TypedExpr` therefore carries an alias-free term: a
deliberate simplification of the first vertical slice, which keeps stored
conclusions independent of later definition edits.

`typed` is the only elaboration entry that produces a `TypedExpr`; operations
call `typed_inputs` to fix a whole problem input tuple without ever passing a
bare term into `ProblemSpec`.
"""

from __future__ import annotations

from cas.foundation.ids import FrameId
from cas.language import propositions as Pr
from cas.language import typing as Ty
from cas.language.signatures import LanguageSignature
from cas.semantics.definitions import expand
from cas.semantics.frames import FrameSorts, FrameStore
from cas.syntax import term as T


def typed(
    term: T.Term,
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
) -> Ty.TypedExprOutcome:
    """Type a term in `frame`, after alias expansion."""
    expanded = expand(frames, frame, term)
    return Ty.typed(
        expanded,
        signature,
        FrameSorts(frames, frame),
        frames.get(frame).meaning,
    )


def typed_inputs(
    terms: tuple[T.Term, ...],
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
) -> tuple[Ty.TypedExpr, ...] | Ty.TypedExprFailure:
    """Type every problem input, or return the first failure unchanged."""
    typed_terms: list[Ty.TypedExpr] = []
    for term in terms:
        outcome = typed(term, frames, frame, signature)
        if not isinstance(outcome, Ty.TypedExpr):
            return outcome
        typed_terms.append(outcome)
    return tuple(typed_terms)


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


__all__ = ["proposition", "typed", "typed_inputs"]
