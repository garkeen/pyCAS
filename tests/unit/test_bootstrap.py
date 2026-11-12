"""Runtime assembly: everything is explicit and nothing leaks between worlds."""

from dataclasses import dataclass, replace

import pytest
from support import head_app, runtime_proposition

from cas.algebra.polynomial import MonomialOrder
from cas.foundation.ids import SymbolId
from cas.kernel.trust import BasisKind, CertificateSchema
from cas.language import sorts as S
from cas.language.problems import ParameterMode, ResultLanguage, Role
from cas.language.signatures import OperatorSignature, StructuralHead
from cas.math.algebra.factorization_checker import FactorizationChecker
from cas.math.algebra.factorization_operation import (
    FactorizationOperation,
)
from cas.math.algebra.factorization_specification import (
    FactorizationCertificate,
)
from cas.math.algebra.groebner_checker import GroebnerChecker
from cas.math.algebra.groebner_operation import GroebnerOperation
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.integration.logarithmic_checker import (
    LogarithmicIntegrationChecker,
)
from cas.math.calculus.integration.logarithmic_operation import (
    LogarithmicIntegrationOperation,
)
from cas.math.calculus.integration.logarithmic_specification import (
    RationalLogAntiderivativeCertificate,
)
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
from cas.operations.registry import OperationRegistry
from cas.runtime.bootstrap import (
    Runtime,
    bootstrap,
    bootstrap_elementary,
    bootstrap_parameterized,
    new_workspace,
)
from cas.semantics.bridge import ParameterPolynomialBridge
from cas.semantics.request import Interpretation
from cas.syntax import term as T
from cas.workflow.workspace import Workspace


def test_bootstrap_wires_the_world_explicitly():
    runtime = bootstrap()
    assert isinstance(runtime, Runtime)
    assert runtime.variable == runtime.table.lookup("x")
    assert runtime.table.name_of(runtime.variable) == "x"
    assert runtime.signature.head_of(runtime.variable) is None
    assert runtime.frames.world is runtime.world
    assert runtime.world.language is runtime.signature
    assert runtime.frame.world == runtime.world.id
    assert runtime.frames.sort_of(runtime.frame.id, runtime.variable) is S.REAL
    assert runtime.ring.generators == (runtime.variable,)
    assert runtime.parent.ring is runtime.ring
    assert runtime.differential.parent is runtime.parent
    assert runtime.vocabulary.symbol == runtime.table.lookup("HasDerivative")
    assert runtime.signature.operator_of(
        runtime.vocabulary.symbol
    ) == runtime.vocabulary.signature
    assert runtime.store.frames is runtime.frames
    assert runtime.store.checkers.get(runtime.checker.id) is runtime.checker
    assert runtime.checker.id == "calculus.derivative"
    assert runtime.store.stats()["judgments"] == 0
    assert runtime.signature.symbol_of(StructuralHead.PLUS) is not None
    assert runtime.request.parameters == ()
    assert runtime.request.target == runtime.variable
    assert runtime.request.parameter_ring is None
    assert runtime.request.parameter_mode is ParameterMode.SPECIFIED_VALUES
    assert runtime.request.interpretation is Interpretation.FORMAL
    assert runtime.request.role_of(runtime.variable) is Role.TARGET


def test_bootstrap_declares_y_and_registers_the_groebner_operation():
    runtime = bootstrap()
    operation = runtime.operations.get("groebner_basis")
    assert isinstance(operation, GroebnerOperation)
    y = runtime.table.lookup("y")
    assert y is not None
    assert runtime.frames.sort_of(runtime.frame.id, y) is S.REAL
    assert runtime.frames.sort_of(runtime.frame.id, runtime.variable) is S.REAL
    variables = (runtime.variable, y)
    assert operation.ring.generators == variables
    assert operation.ring.monomial_order is MonomialOrder.LEX
    assert operation.bridge.ring is operation.ring
    assert operation.request.parameter_ring is None
    assert operation.request.roles.target is None
    assert operation.request.roles.variables == variables
    assert operation.request.roles.variable_sorts == (S.REAL, S.REAL)
    assert operation.request.roles.role_of(runtime.variable) is Role.GENERATOR
    assert operation.request.roles.role_of(y) is Role.GENERATOR
    symbol = runtime.table.lookup("HasGroebnerBasis")
    assert symbol is not None
    assert runtime.signature.operator_of(symbol) is not None
    spec = runtime.store.checkers.spec(operation.checker_id)
    assert spec is not None
    assert isinstance(spec.checker, GroebnerChecker)
    assert spec.accepted_problem_kinds == frozenset({"groebner_basis"})
    assert spec.accepted_specification_kinds == frozenset(
        {"HasGroebnerBasis"}
    )
    assert operation.vocabulary.order is MonomialOrder.LEX


def test_parameterized_bootstrap_has_no_groebner_operation():
    runtime = bootstrap_parameterized()
    assert runtime.operations.get("groebner_basis") is None
    assert runtime.table.lookup("y") is None
    assert runtime.table.lookup("HasGroebnerBasis") is None


def test_bootstrap_registers_the_qx_factorization_operation():
    runtime = bootstrap()
    operation = runtime.operations.get("factor_polynomial")
    assert isinstance(operation, FactorizationOperation)
    assert operation.ring is runtime.ring
    assert operation.bridge is runtime.bridge
    assert operation.request is runtime.request
    assert operation.budget.max_prime_trials > 0
    symbol = runtime.table.lookup("HasFactorization")
    assert symbol is not None
    assert runtime.signature.operator_of(symbol) is not None
    spec = runtime.store.checkers.spec(operation.checker_id)
    assert spec is not None
    assert isinstance(spec.checker, FactorizationChecker)
    assert spec.accepted_problem_kinds == frozenset(
        {"factor_polynomial"}
    )
    assert spec.accepted_specification_kinds == frozenset(
        {"HasFactorization"}
    )
    assert spec.certificate_schema.certificate_type is (
        FactorizationCertificate
    )
    assert spec.requires_problem


def test_parameterized_bootstrap_has_no_factorization_operation():
    runtime = bootstrap_parameterized()
    assert runtime.operations.get("factor_polynomial") is None
    assert runtime.table.lookup("HasFactorization") is None


def test_elementary_bootstrap_registers_factorization():
    runtime = bootstrap_elementary()
    operation = runtime.operations.get("factor_polynomial")
    assert isinstance(operation, FactorizationOperation)
    assert runtime.store.checkers.get(operation.checker_id) is not None


def test_elementary_bootstrap_registers_rational_logarithmic_integration():
    runtime = bootstrap_elementary()
    operation = runtime.operations.get("integrate_rational_logarithmic")
    assert isinstance(operation, LogarithmicIntegrationOperation)
    predicate = runtime.table.lookup("HasRationalLogAntiderivative")
    assert predicate is not None
    assert operation.vocabulary.symbol is predicate
    assert runtime.signature.operator_of(predicate) == (
        operation.vocabulary.signature
    )
    log_symbol = runtime.table.lookup("log")
    assert log_symbol is not None
    assert operation.vocabulary.log_symbol is log_symbol
    semantics = operation.vocabulary.semantics
    assert semantics is not None
    assert semantics.library is runtime.elementary
    assert semantics.function.symbol is log_symbol
    assert semantics.function.name == "log"
    assert semantics.basis == runtime.elementary.basis
    assert operation.log_semantics is semantics
    assert runtime.signature.operator_of(log_symbol) == OperatorSignature(
        (S.REAL,), S.REAL
    )
    assert len(operation.checker_bindings) == 1
    checker_id = operation.checker_bindings[0].checker_id
    assert checker_id == "calculus.integration.rational_logarithmic"
    spec = runtime.store.checkers.spec(checker_id)
    assert spec is not None
    assert isinstance(spec.checker, LogarithmicIntegrationChecker)
    assert spec.checker.semantics is semantics
    assert spec.accepted_problem_kinds == frozenset(
        {"integrate_rational_logarithmic"}
    )
    assert spec.accepted_specification_kinds == frozenset(
        {"HasRationalLogAntiderivative"}
    )
    assert spec.certificate_schema == CertificateSchema(
        "rational_log_antiderivative",
        "1",
        RationalLogAntiderivativeCertificate,
    )
    assert spec.trusted_dependencies == (runtime.elementary.basis,)
    assert spec.requires_problem
    assert operation.views[0].field is spec.checker.field


def test_non_elementary_assemblies_do_not_register_rational_logarithmic():
    for runtime in (bootstrap(), bootstrap_parameterized()):
        assert runtime.operations.get("integrate_rational_logarithmic") is None
        assert runtime.table.lookup("HasRationalLogAntiderivative") is None
        assert runtime.table.lookup("log") is None


def test_elementary_bootstrap_declares_y_and_registers_groebner():
    runtime = bootstrap_elementary()
    y = runtime.table.lookup("y")
    assert y is not None
    assert runtime.frames.sort_of(runtime.frame.id, y) is S.REAL
    operation = runtime.operations.get("groebner_basis")
    assert isinstance(operation, GroebnerOperation)
    assert runtime.store.checkers.get(operation.checker_id) is not None


def test_the_polynomial_checker_is_admitted_with_explicit_metadata():
    runtime = bootstrap()
    spec = runtime.store.checkers.spec(runtime.checker.id)
    assert spec is not None
    assert spec.certificate_schema == CertificateSchema(
        "derivative", "1", DerivativeCertificate
    )
    assert spec.accepted_problem_kinds == frozenset(
        {"differentiate", "integrate"}
    )
    assert spec.accepted_specification_kinds == frozenset({"HasDerivative"})
    assert spec.trusted_dependencies == ()
    assert len(runtime.store.bases) == 0
    assert runtime.store.checkers.spec("kernel.contradiction") is not None


def test_elementary_bootstrap_admits_the_declaration_basis():
    runtime = bootstrap_elementary()
    library = runtime.elementary
    assert library is not None
    basis = library.basis
    assert basis is not None
    assert basis.kind is BasisKind.DECLARATION_FILE
    assert basis.name == "declarations.dsl"
    assert len(basis.digest) == 64
    assert basis.world == runtime.world.id

    spec = runtime.store.checkers.spec(runtime.derivative.checker_id)
    assert spec is not None
    assert spec.trusted_dependencies == (basis,)
    assert runtime.store.bases.verify(basis)
    assert len(runtime.store.bases) == 1
    assert spec.accepted_problem_kinds == frozenset({"differentiate"})
    assert spec.accepted_specification_kinds == frozenset({"HasDerivative"})

    polynomial_spec = runtime.store.checkers.spec(
        "calculus.derivative.polynomial"
    )
    assert polynomial_spec is not None
    assert polynomial_spec.accepted_problem_kinds == frozenset({"integrate"})
    assert polynomial_spec.trusted_dependencies == ()
    assert polynomial_spec.accepted_specification_kinds == frozenset(
        {"HasDerivative"}
    )


def test_parameterized_bootstrap_separates_roles():
    runtime = bootstrap_parameterized()
    parameter = runtime.request.parameters[0]
    assert runtime.table.name_of(parameter) == "a"
    assert runtime.variable not in runtime.request.parameters
    assert runtime.ring.generators == (runtime.variable,)
    assert set(runtime.ring.generators).isdisjoint(runtime.request.parameters)
    assert runtime.request.target == runtime.variable
    assert runtime.request.parameter_mode is ParameterMode.ALL_PARAMETER_VALUES
    assert runtime.request.interpretation is Interpretation.PARAMETER_FAMILY
    assert runtime.request.role_of(runtime.variable) is Role.TARGET
    assert runtime.request.role_of(parameter) is Role.PARAMETER
    assert runtime.frames.sort_of(runtime.frame.id, parameter) is S.REAL
    assert isinstance(runtime.bridge, ParameterPolynomialBridge)
    assert runtime.parent.ring is runtime.ring
    assert runtime.differential.parent is runtime.parent
    assert runtime.store.stats()["judgments"] == 0
    assert runtime.specialization is not None


def test_parameterized_bootstrap_assembles_the_concrete_view():
    runtime = bootstrap_parameterized()
    specialization = runtime.specialization
    assert specialization is not None
    assert specialization.ring.generators == (runtime.variable,)
    assert specialization.parent.ring is specialization.ring
    assert specialization.differential.parent is specialization.parent
    assert specialization.request.parameters == ()
    assert specialization.request.parameter_ring is None
    assert specialization.request.parameter_mode is ParameterMode.SPECIFIED_VALUES
    assert specialization.request.interpretation is Interpretation.EMBEDDED
    assert specialization.request.target == runtime.variable
    assert specialization.checker.id == "calculus.derivative.specialized"
    assert runtime.store.checkers.get(runtime.checker.id) is runtime.checker
    assert (
        runtime.store.checkers.get(specialization.checker.id)
        is specialization.checker
    )


def test_a_generic_request_keeps_the_formal_family_claim():
    runtime = bootstrap_parameterized(
        parameter_mode=ParameterMode.GENERIC_PARAMETERS
    )
    assert runtime.request.parameter_mode is ParameterMode.GENERIC_PARAMETERS
    assert runtime.specialization is not None


def test_every_differentiation_view_carries_its_request_differential():
    runtime = bootstrap()
    for view in runtime.views:
        assert view.request.differential is view.differential
    assert runtime.request.differential is runtime.differential


def test_the_parameterized_views_carry_their_request_differentials():
    runtime = bootstrap_parameterized()
    for view in runtime.views:
        assert view.request.differential is view.differential
    assert runtime.request.differential is runtime.differential
    specialization = runtime.specialization
    assert specialization is not None
    assert specialization.request.differential is specialization.differential
    assert specialization.differential.parent is specialization.parent


def test_the_elementary_view_carries_its_request_differential():
    runtime = bootstrap_elementary()
    for view in runtime.views:
        assert view.request.differential is view.differential
    assert runtime.request.differential is runtime.differential


def test_a_formal_family_cannot_claim_specified_values():
    with pytest.raises(ValueError):
        bootstrap_parameterized(
            parameter_mode=ParameterMode.SPECIFIED_VALUES
        )


def test_multiple_parameters_keep_the_target_separate():
    runtime = bootstrap_parameterized(("a", "b"))
    assert len(runtime.request.parameters) == 2
    assert runtime.ring.generators == (runtime.variable,)
    for parameter in runtime.request.parameters:
        assert runtime.frames.sort_of(runtime.frame.id, parameter) is S.REAL
        assert runtime.request.role_of(parameter) is Role.PARAMETER
    assert runtime.request.role_of(runtime.variable) is Role.TARGET


def test_parameterized_bootstrap_validates_names():
    with pytest.raises(ValueError):
        bootstrap_parameterized(())
    with pytest.raises(ValueError):
        bootstrap_parameterized(("a", "a"))
    with pytest.raises(ValueError):
        bootstrap_parameterized(("x",))
    with pytest.raises(ValueError):
        bootstrap_parameterized(("Plus",))
    with pytest.raises(ValueError):
        bootstrap_parameterized(("HasDerivative",))


@dataclass(frozen=True, slots=True)
class BoundOperation:
    checker_id: str
    id: str = "test.bound"
    version: str = "1"
    checker_bindings: tuple[CheckerBinding, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "checker_bindings",
            (
                CheckerBinding(
                    "HasDerivative", "differentiate", self.checker_id
                ),
            ),
        )

    @property
    def input_schema(self) -> InputSchema:
        return InputSchema("test/bound", lambda request: Admitted())

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
    def capability_requirements(self) -> frozenset[Capability]:
        return frozenset()


def test_runtime_rejects_unregistered_or_incompatible_bindings():
    runtime = bootstrap()
    missing = BoundOperation("missing.checker")
    with pytest.raises(ValueError, match="unregistered"):
        replace(
            runtime,
            operations=OperationRegistry(
                {missing.id: missing},
                provided_capabilities=frozenset(Capability),
            ),
        )

    incompatible = BoundOperation("kernel.hypothesis")
    with pytest.raises(ValueError, match="does not accept"):
        replace(
            runtime,
            operations=OperationRegistry(
                {incompatible.id: incompatible},
                provided_capabilities=frozenset(Capability),
            ),
        )


def test_separate_assemblies_share_no_state():
    first = bootstrap()
    second = bootstrap()
    assert first.store is not second.store
    assert first.frames is not second.frames
    assert first.table is not second.table
    assert first.parent is not second.parent
    assert first.store.stats()["judgments"] == 0
    assert second.store.stats()["judgments"] == 0
    assert first.frames.count() == second.frames.count() == 2
    assert first.variable == second.variable
    assert first.world is not second.world
    assert first.world.id != second.world.id

    proposition = runtime_proposition(
        first,
        head_app(
            first.signature,
            StructuralHead.GT,
            T.symbol(first.variable, "x"),
            T.number(0),
        ),
    )
    assert not second.frames.readable(proposition, second.frame.id)


def test_new_workspace_starts_at_the_runtime_frame():
    runtime = bootstrap()
    workspace = new_workspace(runtime)
    assert isinstance(workspace, Workspace)
    assert workspace.frame == runtime.frame.id
    assert workspace.expressions() == ()
    assert workspace.links() == ()
    assert workspace.events() == ()
    assert workspace.revision.label == "start"


def test_structural_head_ids_are_not_math_semantics(runtime):
    assert runtime.signature.head_of(runtime.variable) is None
    assert runtime.signature.head_of(runtime.vocabulary.symbol) is None
    assert runtime.signature.symbol_of(StructuralHead.PLUS) not in {
        runtime.variable,
        runtime.vocabulary.symbol,
        SymbolId(10_000),
    }
