"""Capabilities a registered operation requires from its runtime assembly.

A capability names an algebraic or workbook structure the operation's
pre-assembled views, bridges and checkers actually consume.  The registry
compares an operation's requirements with the structures the entry point
provided, so an operation is never registered against an assembly that cannot
serve it.  The vocabulary stays structural: it does not name concrete
mathematical functions, rules or operation ids.
"""

from __future__ import annotations

from enum import StrEnum


class Capability(StrEnum):
    """One structure an operation may require from its assembly."""

    FIELD = "field"
    POLYNOMIAL_RING = "polynomial_ring"
    RATIONAL_FUNCTION_FIELD = "rational_function_field"
    FUNCTION_VALUE = "function_value"
    GENERIC_RESULT = "generic_result"


CapabilityRequirements = frozenset[Capability]


__all__ = ["Capability", "CapabilityRequirements"]
