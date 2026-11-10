"""Shared parameter schemas for registered operations.

An operation whose request carries no auxiliary parameters still declares a
`ParameterSchema`: the registry and the problem builder consume the same
adapter, so a stray parameter is refused structurally instead of being
silently ignored.
"""

from __future__ import annotations

from cas.operations.protocols import (
    InvalidRequest,
    ParameterOutcome,
    ParameterSchema,
    Parsed,
)


def _parse_no_parameters(
    parameters: tuple[tuple[str, object], ...],
) -> ParameterOutcome[None]:
    if parameters:
        return InvalidRequest(("this operation takes no parameters",))
    return Parsed(None)


EMPTY_PARAMETER_SCHEMA: ParameterSchema[None] = ParameterSchema(
    "operation/empty-parameters",
    _parse_no_parameters,
)


__all__ = ["EMPTY_PARAMETER_SCHEMA"]
