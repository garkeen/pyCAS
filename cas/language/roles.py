"""The role a published candidate plays inside its verification specification.

A claim has several terms: a derivative claim names a source and a result, a
Hermite claim names a polynomial part and a remainder, and a function-equality
claim names two representations.  The operation declares once which term it
publishes; the checker reads that declaration instead of inferring the side
from the operation name.  The role travels through the checker binding, the
kernel request and the recorded candidate, so a manual re-check selects the
same term as the original proposal.
"""

from enum import StrEnum


class CandidateRole(StrEnum):
    """Which part of a claim a published candidate names."""

    RESULT = "result"
    SOURCE = "source"
    REMAINDER = "remainder"
    SET = "set"
    CONCLUSION = "conclusion"
    RIGHT = "right"


__all__ = ["CandidateRole"]
