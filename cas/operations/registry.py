"""Frozen operation registry assembled at runtime construction."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from types import MappingProxyType

from cas.operations.protocols import CheckerBinding, OperationSpec


class OperationError(ValueError):
    """An operation registration is internally inconsistent."""


class OperationRegistry:
    """One stable operation per id; no registration after construction."""

    __slots__ = ("_operations",)

    def __init__(self, operations: Mapping[str, OperationSpec]) -> None:
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
            if any(
                not isinstance(binding, CheckerBinding)
                for binding in operation.checker_bindings
            ):
                raise OperationError(
                    f"operation {key!r} has a malformed checker binding"
                )
            kinds = [
                binding.specification_kind
                for binding in operation.checker_bindings
            ]
            if len(set(kinds)) != len(kinds):
                raise OperationError(
                    f"operation {key!r} binds one kind twice"
                )
        self._operations = MappingProxyType(table)

    def get(self, operation_id: str) -> OperationSpec | None:
        return self._operations.get(operation_id)

    def __len__(self) -> int:
        return len(self._operations)

    def __iter__(self) -> Iterator[OperationSpec]:
        return iter(self._operations.values())


__all__ = ["OperationError", "OperationRegistry"]
