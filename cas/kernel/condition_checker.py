"""The condition checker: prove an obligation from supplied premises.

This is one half of §14.6. `resolve_applicability` is the resolver; it decides
which obligations to attempt and which premises to offer. The checker itself
only verifies that the supplied premises entail the requested conclusion and
reports the premises it actually used.
"""

from __future__ import annotations

from collections.abc import Iterable

from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    InvalidEvidence,
    Unverified,
    Verified,
)
from cas.language.decisions import Reason
from cas.language.propositions import Proposition
from cas.language.signatures import LanguageSignature
from cas.semantics.conditions import and_all, implies
from cas.semantics.frames import FrameSorts, FrameStore


class ConditionChecker:
    """Prove a condition from premise judgments by restricted implication."""

    id = "logic.condition"
    version = "1"

    def __init__(
        self, frames: FrameStore, signature: LanguageSignature
    ) -> None:
        self._frames = frames
        self._signature = signature

    def check(self, request: CheckRequest) -> CheckOutcome:
        for proposition in request.premises + request.conclusions:
            if not self._frames.readable(proposition, request.frame):
                return InvalidEvidence(
                    "a premise or conclusion is not readable in the "
                    "request frame"
                )
        used: set[int] = set()
        environment = FrameSorts(self._frames, request.frame)
        for conclusion in request.conclusions:
            indices = self._needed(
                request.premises, conclusion, environment
            )
            if indices is None:
                return Unverified(
                    Reason.GUARDED,
                    "the condition is not entailed by the supplied premises",
                )
            used.update(indices)
        return Verified(
            tuple(request.conclusions),
            used_premises=tuple(sorted(used)),
        )

    def _needed(
        self,
        premises: tuple[Proposition, ...],
        conclusion: Proposition,
        environment: FrameSorts,
    ) -> list[int] | None:
        if not self._entails(
            premises, range(len(premises)), conclusion, environment
        ):
            return None
        kept = list(range(len(premises)))
        for index in list(kept):
            trial = [position for position in kept if position != index]
            if self._entails(
                premises, trial, conclusion, environment
            ):
                kept = trial
        return kept

    def _entails(
        self,
        premises: tuple[Proposition, ...],
        indices: Iterable[int],
        conclusion: Proposition,
        environment: FrameSorts,
    ) -> bool:
        assumption = and_all(
            self._signature,
            *(premises[index].term for index in indices),
            environment=environment,
        )
        return implies(
            assumption,
            conclusion.term,
            self._signature,
            environment,
        ) is True


__all__ = ["ConditionChecker"]
