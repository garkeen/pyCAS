"""Frozen operation registry assembled at runtime construction."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from types import MappingProxyType

from cas.foundation.ids import SymbolId
from cas.operations.capabilities import Capability
from cas.operations.protocols import (
    CheckerBinding,
    InputSchema,
    OperationSpec,
    ParameterSchema,
    ResultSchema,
)


class OperationError(ValueError):
    """An operation registration is internally inconsistent."""


def _admit_capabilities(
    capabilities: frozenset[Capability],
    *,
    owner: str,
) -> frozenset[Capability]:
    """Check one capability set is exactly a frozenset of `Capability`."""
    if not isinstance(capabilities, frozenset):
        raise OperationError(
            f"{owner} capabilities must be a frozenset of Capability values"
        )
    if any(not isinstance(item, Capability) for item in capabilities):
        raise OperationError(
            f"{owner} capabilities must be a frozenset of Capability values"
        )
    return capabilities


class OperationRegistry:
    """One stable operation per id; no registration after construction."""

    __slots__ = ("_operations",)

    def __init__(
        self,
        operations: Mapping[str, OperationSpec],
        *,
        provided_capabilities: frozenset[Capability],
    ) -> None:
        provided = _admit_capabilities(
            provided_capabilities, owner="provided"
        )
        table = dict(operations)
        for key, operation in table.items():
            if operation.id != key:
                raise OperationError(
                    f"operation registered as {key!r} reports id "
                    f"{operation.id!r}"
                )
            if not operation.version:
                raise OperationError(f"operation {key!r} has no version")
            if not operation.checker_bindings:
                raise OperationError(
                    f"operation {key!r} names no checker binding"
                )
            input_schema = operation.input_schema
            if not isinstance(input_schema, InputSchema):
                raise OperationError(
                    f"operation {key!r} does not declare an input schema"
                )
            result_schema = operation.result_schema
            if not isinstance(result_schema, ResultSchema):
                raise OperationError(
                    f"operation {key!r} does not declare a result schema"
                )
            parameter_schema = operation.parameter_schema
            if not isinstance(parameter_schema, ParameterSchema):
                raise OperationError(
                    f"operation {key!r} does not declare a parameter schema"
                )
            requirements = _admit_capabilities(
                operation.capability_requirements,
                owner=f"operation {key!r}",
            )
            missing = requirements - provided
            if missing:
                names = ", ".join(
                    sorted(capability.value for capability in missing)
                )
                raise OperationError(
                    f"operation {key!r} requires capabilities this "
                    f"assembly does not provide: {names}"
                )
            if any(
                not isinstance(binding, CheckerBinding)
                for binding in operation.checker_bindings
            ):
                raise OperationError(
                    f"operation {key!r} has a malformed checker binding"
                )
            bindings = [
                (binding.specification_kind, binding.target)
                for binding in operation.checker_bindings
            ]
            if len(set(bindings)) != len(bindings):
                raise OperationError(
                    f"operation {key!r} binds one kind twice for one target"
                )
            targets_by_kind: dict[str, set[SymbolId | None]] = {}
            for binding in operation.checker_bindings:
                targets_by_kind.setdefault(
                    binding.specification_kind, set()
                ).add(binding.target)
            for specification_kind, targets in targets_by_kind.items():
                if None in targets and len(targets) > 1:
                    raise OperationError(
                        f"operation {key!r} has an ambiguous generic and "
                        f"target-specific binding for specification kind "
                        f"{specification_kind!r}"
                    )
        self._operations = MappingProxyType(table)

    def get(self, operation_id: str) -> OperationSpec | None:
        return self._operations.get(operation_id)

    def __len__(self) -> int:
        return len(self._operations)

    def __iter__(self) -> Iterator[OperationSpec]:
        return iter(self._operations.values())


__all__ = ["OperationError", "OperationRegistry"]
