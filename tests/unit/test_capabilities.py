"""Capability requirements are checked when the operation registry freezes."""

from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

import pytest

from cas.language.problems import ResultLanguage
from cas.operations.capabilities import Capability
from cas.operations.parameters import EMPTY_PARAMETER_SCHEMA
from cas.operations.protocols import (
    Admitted,
    CheckerBinding,
    InputSchema,
    ParameterSchema,
    ResultSchema,
    ResultShape,
)
from cas.operations.registry import OperationError, OperationRegistry
from cas.runtime import (
    Runtime,
    bootstrap,
    bootstrap_elementary,
    bootstrap_parameterized,
)


@pytest.mark.parametrize(
    "factory, operation_id, capability",
    [
        (bootstrap, "differentiate", Capability.POLYNOMIAL_RING),
        (bootstrap, "integrate", Capability.POLYNOMIAL_RING),
        (bootstrap, "hermite_reduce", Capability.RATIONAL_FUNCTION_FIELD),
        (bootstrap, "extend_function", Capability.FUNCTION_VALUE),
        (bootstrap, "compare_functions", Capability.FUNCTION_VALUE),
        (bootstrap, "solve_linear", Capability.FIELD),
        (bootstrap, "polynomial_gcd", Capability.FIELD),
        (bootstrap, "resultant", Capability.POLYNOMIAL_RING),
        (bootstrap, "root_count", Capability.ORDERED_FIELD),
        (bootstrap, "isolate_roots", Capability.ORDERED_FIELD),
        (
            bootstrap_elementary,
            "root_count",
            Capability.ORDERED_FIELD,
        ),
        (
            bootstrap_elementary,
            "isolate_roots",
            Capability.ORDERED_FIELD,
        ),
        (
            bootstrap_parameterized,
            "specialize",
            Capability.GENERIC_RESULT,
        ),
    ],
)
def test_a_registered_operation_needs_the_capability_it_declares(
    factory: Callable[[], Runtime[Any]],
    operation_id: str,
    capability: Capability,
) -> None:
    runtime = factory()
    operation = runtime.operations.get(operation_id)
    assert operation is not None
    provided = frozenset(Capability) - {capability}
    with pytest.raises(OperationError) as raised:
        OperationRegistry(
            {operation.id: operation},
            provided_capabilities=provided,
        )
    assert capability.value in str(raised.value)


def test_an_operation_registers_when_all_its_capabilities_are_provided():
    runtime = bootstrap()
    operation = runtime.operations.get("differentiate")
    assert operation is not None
    registry = OperationRegistry(
        {operation.id: operation},
        provided_capabilities=operation.capability_requirements,
    )
    assert registry.get("differentiate") is operation


@pytest.mark.parametrize(
    "factory",
    [bootstrap, bootstrap_parameterized, bootstrap_elementary],
)
def test_every_bootstrap_operation_declares_capabilities(
    factory: Callable[[], Runtime[Any]],
) -> None:
    runtime = factory()
    for operation in runtime.operations:
        requirements = operation.capability_requirements
        assert isinstance(requirements, frozenset)
        assert all(
            isinstance(capability, Capability)
            for capability in requirements
        )


@dataclass(frozen=True, slots=True)
class BadRequirementOperation:
    """A registry test double whose capability payload is not the vocabulary."""

    requirements: frozenset[object]
    id: str = "test.bad-capability"
    version: str = "1"
    checker_bindings: tuple[CheckerBinding, ...] = (
        CheckerBinding("Hypothesis", "assume", "kernel.hypothesis"),
    )

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("test/bad-capability", lambda request: Admitted())

    @property
    def parameter_schema(self) -> ParameterSchema[None]:
        return EMPTY_PARAMETER_SCHEMA

    @property
    def result_schema(self) -> ResultSchema:
        return ResultSchema(
            frozenset({ResultLanguage.EXPRESSION}),
            ResultShape.EXPRESSION,
        )

    @property
    def capability_requirements(self) -> frozenset[object]:
        return self.requirements

    def build_problem(self, request):
        raise AssertionError("unreachable")

    def propose(self, execution):
        raise AssertionError("unreachable")


@pytest.mark.parametrize(
    "requirements",
    [frozenset({"field"}), frozenset({object()})],
)
def test_an_operation_capability_must_be_a_capability(
    requirements: frozenset[object],
) -> None:
    operation = BadRequirementOperation(requirements)
    with pytest.raises(OperationError, match="Capability"):
        OperationRegistry(
            {operation.id: operation},
            provided_capabilities=frozenset(Capability),
        )


@pytest.mark.parametrize(
    "provided",
    [frozenset({"field"}), frozenset({object()})],
)
def test_provided_capabilities_must_be_capabilities(
    provided: frozenset[object],
) -> None:
    with pytest.raises(OperationError, match="provided capabilities"):
        OperationRegistry(
            {},
            provided_capabilities=provided,  # type: ignore[arg-type]
        )


def test_provided_capabilities_must_be_a_frozenset():
    with pytest.raises(OperationError, match="frozenset"):
        OperationRegistry(
            {},
            provided_capabilities={Capability.FIELD},  # type: ignore[arg-type]
        )
