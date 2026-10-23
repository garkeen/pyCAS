"""Propositions: a formula that has been typed and tied to a meaning frame.

A `Proposition` is not "any term with a label". It exists only through
`check`, which requires that the term

- is well scoped (no bound index escapes its binder),
- has proposition sort under the language signature,
- carries the identity of the world and frame it was read in.

Definedness premises and declared-predicate laws are established later by
elaboration; this layer refuses a formula it cannot type, and never guesses.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TypeAlias

from cas.foundation.ids import FrameId, WorldId
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.signatures import LanguageSignature
from cas.syntax import binding as B
from cas.syntax import term as T

_SEAL = object()


@dataclass(frozen=True, slots=True)
class MeaningKey:
    """The meaning environment a formula was read in.

    Two formulas with the same text but different keys are different
    propositions: names may resolve to different declarations.
    """

    world: WorldId
    frame: FrameId


@dataclass(frozen=True, slots=True)
class Proposition:
    """A typed formula with an explicit meaning environment.

    Construction requires the module seal; use `check`.
    """

    term: T.Term
    meaning: MeaningKey
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError("a proposition is issued only by propositions.check")


@dataclass(frozen=True, slots=True)
class IllScoped:
    """The term contains a bound index with no enclosing binder."""

    detail: str


PropositionOutcome: TypeAlias = Proposition | Ty.Typing | IllScoped


def check(
    term: T.Term,
    signature: LanguageSignature,
    environment: Ty.SortEnvironment,
    meaning: MeaningKey,
) -> PropositionOutcome:
    """Issue a `Proposition`, or explain why the term is not one.

    A wrong sort is reported as `IllTyped`: calling `x + 1` a proposition is a
    type error, not a false statement.
    """
    if not B.well_scoped(term):
        return IllScoped("a formula has a bound index outside its binder")
    typing = Ty.infer(term, signature, environment)
    if isinstance(typing, Ty.Typed):
        if typing.sort != S.PROPOSITION:
            return Ty.IllTyped(
                f"a proposition needs proposition sort, got {typing.sort!r}"
            )
        return Proposition(term, meaning, _SEAL)
    return typing


__all__ = [
    "IllScoped",
    "MeaningKey",
    "Proposition",
    "PropositionOutcome",
    "check",
]
