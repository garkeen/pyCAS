"""Operation-owned parameter schemas and the removed central payload union."""

from dataclasses import dataclass

import pytest
from support import runtime_proposition, variable

from cas.language import sorts as S
from cas.language.functions import (
    FunctionParameter,
    FunctionRepresentation,
    FunctionValue,
)
from cas.language.problems import ParameterMode, ResultLanguage
from cas.operations.capabilities import Capability
from cas.operations.parameters import EMPTY_PARAMETER_SCHEMA
from cas.operations.protocols import (
    Admitted,
    CheckerBinding,
    FunctionComparisonInput,
    FunctionExtensionInput,
    GenericResultInput,
    InputSchema,
    InvalidRequest,
    OperationRequest,
    ParameterSchema,
    Parsed,
    ProblemBuilt,
    ProblemInvalid,
    ResultSchema,
    ResultShape,
    ValueMappingInput,
)
from cas.operations.registry import OperationError, OperationRegistry
from cas.runtime import bootstrap, bootstrap_parameterized
from cas.semantics.regions import region_from_proposition
from cas.semantics.specialization import GenericResult
from cas.syntax import term as T


def function_value(runtime):
    domain = runtime_proposition(runtime, T.TRUE)
    return FunctionValue(
        (FunctionParameter(runtime.variable, S.REAL),),
        domain,
        S.REAL,
        (FunctionRepresentation(variable(runtime), domain),),
    )


def generic_result(runtime):
    true = runtime_proposition(runtime, T.TRUE)
    return GenericResult.assemble(
        result=T.number(1),
        valid_on=region_from_proposition(true),
        excluded_cases=(),
        correctness_specification=true,
        parameter_mode=ParameterMode.ALL_PARAMETER_VALUES,
    )


def test_the_shared_empty_schema_accepts_no_parameters():
    parsed = EMPTY_PARAMETER_SCHEMA.parse(())
    assert isinstance(parsed, Parsed)
    assert parsed.value is None

    refused = EMPTY_PARAMETER_SCHEMA.parse((("unexpected", 1),))
    assert isinstance(refused, InvalidRequest)
    assert "takes no parameters" in refused.issues[0]


def test_parameter_schema_validates_its_own_contract():
    with pytest.raises(ValueError):
        ParameterSchema("", lambda parameters: Parsed(None))
    with pytest.raises(TypeError):
        ParameterSchema("test/schema", "not callable")  # type: ignore[arg-type]


def test_extension_rejects_a_wrong_parameter_type():
    runtime = bootstrap()
    operation = runtime.operations.get("extend_function")
    assert operation is not None
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (variable(runtime), variable(runtime)),
            parameters=(("extension", object()),),
        )
    )
    assert isinstance(outcome, ProblemInvalid)
    assert "FunctionExtensionInput" in outcome.detail


def test_extension_parameters_build_a_problem():
    runtime = bootstrap()
    operation = runtime.operations.get("extend_function")
    assert operation is not None
    value = function_value(runtime)
    domain = runtime_proposition(runtime, T.TRUE)
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (value.representations[0].term, value.representations[0].term),
            parameters=(
                (
                    "extension",
                    FunctionExtensionInput(value, domain, domain),
                ),
            ),
        )
    )
    assert isinstance(outcome, ProblemBuilt)
    assert outcome.problem.function_inputs == (value,)


def test_comparison_requires_its_parameter():
    runtime = bootstrap()
    operation = runtime.operations.get("compare_functions")
    assert operation is not None
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (variable(runtime), variable(runtime)),
        )
    )
    assert isinstance(outcome, ProblemInvalid)
    assert "comparison" in outcome.detail


def test_comparison_parameters_build_a_problem():
    runtime = bootstrap()
    operation = runtime.operations.get("compare_functions")
    assert operation is not None
    value = function_value(runtime)
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (value.representations[0].term, value.representations[0].term),
            parameters=(
                (
                    "comparison",
                    FunctionComparisonInput(value, value, 0, 0),
                ),
            ),
        )
    )
    assert isinstance(outcome, ProblemBuilt)
    assert outcome.problem.function_inputs == (value, value)


def test_specialization_requires_both_named_parameters():
    runtime = bootstrap_parameterized()
    operation = runtime.operations.get("specialize")
    assert operation is not None
    parameter = runtime.request.parameters[0]
    family = GenericResultInput(generic_result(runtime))

    missing_values = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (variable(runtime),),
            target=runtime.variable,
            parameters=(("family", family),),
        )
    )
    assert isinstance(missing_values, ProblemInvalid)
    assert "values" in missing_values.detail

    missing_family = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (variable(runtime),),
            target=runtime.variable,
            parameters=(
                ("values", ValueMappingInput({parameter: 1})),
            ),
        )
    )
    assert isinstance(missing_family, ProblemInvalid)
    assert "family" in missing_family.detail


def test_specialization_parameters_build_a_problem():
    runtime = bootstrap_parameterized()
    operation = runtime.operations.get("specialize")
    assert operation is not None
    parameter = runtime.request.parameters[0]
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (T.number(1),),
            target=runtime.variable,
            parameters=(
                ("family", GenericResultInput(generic_result(runtime))),
                ("values", ValueMappingInput({parameter: 1})),
            ),
        )
    )
    assert isinstance(outcome, ProblemBuilt)


def test_a_no_parameter_operation_refuses_a_stray_parameter():
    runtime = bootstrap()
    operation = runtime.operations.get("polynomial_gcd")
    assert operation is not None
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (variable(runtime), variable(runtime)),
            runtime.variable,
            parameters=(("unexpected", 1),),
        )
    )
    assert isinstance(outcome, ProblemInvalid)
    assert "takes no parameters" in outcome.detail


def test_a_no_parameter_operation_builds_its_problem():
    runtime = bootstrap()
    operation = runtime.operations.get("polynomial_gcd")
    assert operation is not None
    outcome = operation.build_problem(
        OperationRequest(
            runtime.frame.id,
            (variable(runtime), variable(runtime)),
            runtime.variable,
        )
    )
    assert isinstance(outcome, ProblemBuilt)


def test_the_registry_requires_a_parameter_schema():
    @dataclass(frozen=True, slots=True)
    class NoParameterSchema:
        id: str = "test.no-parameters"
        version: str = "1"
        checker_bindings: tuple[CheckerBinding, ...] = (
            CheckerBinding("Hypothesis", "assume", "kernel.hypothesis"),
        )

        @property
        def input_schema(self) -> InputSchema:
            return InputSchema(
                "test/no-parameters", lambda request: Admitted()
            )

        @property
        def parameter_schema(self) -> object:
            return object()

        @property
        def result_schema(self) -> ResultSchema:
            return ResultSchema(
                frozenset({ResultLanguage.EXPRESSION}),
                ResultShape.EXPRESSION,
            )

        @property
        def capability_requirements(self) -> frozenset[Capability]:
            return frozenset()

        def build_problem(self, request):
            raise AssertionError("unreachable")

        def propose(self, execution):
            raise AssertionError("unreachable")

    with pytest.raises(OperationError, match="parameter schema"):
        OperationRegistry(
            {"test.no-parameters": NoParameterSchema()},
            provided_capabilities=frozenset(Capability),
        )
