"""Closed workflow presentation states."""

from enum import StrEnum


class StepStatus(StrEnum):
    COMMITTED = "committed"
    REFUSED = "refused"
    UNDECIDED = "undecided"
    NEEDS_SPLIT = "needs_split"


class CandidateState(StrEnum):
    UNVERIFIED = "unverified"
    CONDITIONAL = "conditional"
    VALIDATED = "validated"
