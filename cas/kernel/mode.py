"""Execution modes.

The three modes are soundness-equivalent; they differ only in traceability:

    mode          read deps        discharge        applicability cache  history
    interactive   off              deferred to      on                   truncate N
                                   first query
    derivation    per Step         at commit        on                   full
    audit         per read         at commit        on                   full

A switch may only change bookkeeping granularity, never the correctness of a
returned value. Therefore:

· condition *decision* always runs, in every mode; otherwise a refuted guard
  would be silently ignored, which is a correctness problem. Only discharge
  *registration* (recording a proved condition as a Discharge) may be deferred.
· a checker code path must never read a mode flag; this module is consumed only
  by bookkeeping statements in commit.

Not yet implemented: the applicability cache and history truncation. Neither
affects soundness; both belong to the traceability layer and will arrive with
the event history.
"""

from enum import Enum


class ExecutionMode(Enum):
    INTERACTIVE = "interactive"   # default
    DERIVATION = "derivation"
    AUDIT = "audit"

    def records_reads(self) -> bool:
        """Whether context reads are recorded into Step.reads."""
        return self is not ExecutionMode.INTERACTIVE

    def defers_discharge(self) -> bool:
        """Whether discharge registration is deferred (conditions are still
        decided, only the Discharge record is postponed)."""
        return self is ExecutionMode.INTERACTIVE

    def raw_reads(self) -> bool:
        """Whether every read occurrence is kept (read granularity) instead of
        deduplicating (Step granularity)."""
        return self is ExecutionMode.AUDIT


DEFAULT_MODE = ExecutionMode.INTERACTIVE
