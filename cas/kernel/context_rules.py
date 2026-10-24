"""Core scope rules exposed as checkers.

The hypothesis rule is intentionally tiny: a conclusion is verified when it is
exactly one of the hypotheses visible in the submission frame. It does not treat
a hypothesis as a theorem and it does not inspect certificates.
"""

from __future__ import annotations

from cas.kernel.evidence import (
    CheckOutcome,
    CheckRequest,
    Unverified,
    Verified,
)
from cas.language.decisions import Reason
from cas.semantics.frames import FrameStore


class HypothesisChecker:
    """`Gamma, H |- H` for a hypothesis introduced by a frame."""

    id = "kernel.hypothesis"
    version = "1"

    def __init__(self, frames: FrameStore) -> None:
        self._frames = frames

    def check(self, request: CheckRequest) -> CheckOutcome:
        assumptions = self._frames.assumptions(request.frame)
        for conclusion in request.conclusions:
            if conclusion not in assumptions:
                return Unverified(
                    Reason.GUARDED,
                    "the proposition is not an assumption in this frame",
                )
        return Verified(tuple(request.conclusions))


__all__ = ["HypothesisChecker"]
