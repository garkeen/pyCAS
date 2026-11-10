"""Meaning environments: the world and frame a formula was read in.

A `MeaningKey` is the identity of the name environment, not of the formula.
Two formulas with the same text but different keys are different propositions
or typed expressions: names may resolve to different declarations.

This module owns the value alone so that typing, propositions and frames can
share it without importing each other in a cycle.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import FrameId, WorldId


@dataclass(frozen=True, slots=True)
class MeaningKey:
    """The meaning environment a formula was read in."""

    world: WorldId
    frame: FrameId


__all__ = ["MeaningKey"]
