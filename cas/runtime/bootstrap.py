"""Explicit assembly of the runtime.

One call builds a world, a coefficient structure, a polynomial ring, a chosen
derivation, a bridge between terms and ring elements, the `HasDerivative`
predicate and checker, a frame, and the kernel ledger. Nothing is installed into
module-level state; consumers receive the returned value.

The plain assembly has coefficients in Q and target `x`. The parameterized
assembly separates roles explicitly: formal parameters generate the coefficient
ring, while `x` remains the target, so parameter symbols never become target
generators by accident.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Generic, TypeVar

from cas.algebra.parents import Parent, ParentRegistry, ParentSpec
from cas.algebra.polynomial import (
    MonomialOrder,
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId, WorldId
from cas.kernel.condition_checker import ConditionChecker
from cas.kernel.consistency import ContradictionChecker
from cas.kernel.context_rules import HypothesisChecker
from cas.kernel.evidence import Checker, CheckerRegistry, CheckerSpec
from cas.kernel.store import KernelStore
from cas.kernel.trust import BasisKind, BasisRef, CertificateSchema
from cas.language import sorts as S
from cas.language.declarations import DeclarationSet, build_language
from cas.language.problems import ParameterMode
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.calculus.differentiation.certificate import (
    DerivativeCertificate,
)
from cas.math.calculus.differentiation.checker import DerivativeChecker
from cas.math.calculus.differentiation.elementary import (
    ElementaryDifferentiator,
)
from cas.math.calculus.differentiation.elementary_checker import (
    ElementaryDerivativeChecker,
)
from cas.math.calculus.differentiation.operation import (
    DifferentiationOperation,
)
from cas.math.calculus.differentiation.services import (
    ElementaryDerivativeService,
    PolynomialDerivativeService,
)
from cas.math.calculus.differentiation.specialization_operation import (
    SpecializationOperation,
)
from cas.math.calculus.differentiation.specification import DerivativeVocabulary
from cas.math.calculus.differentiation.view import SpecializationView
from cas.math.elementary.declarations import (
    ElementaryLibrary,
    build_elementary,
    default_elementary_declarations,
)
from cas.operations.registry import OperationRegistry
from cas.semantics.bridge import (
    ParameterPolynomialBridge,
    PolynomialBridge,
    SimplePolynomialBridge,
)
from cas.semantics.differential import DifferentialStructure, polynomial_structure
from cas.semantics.frames import Declaration, Frame, FrameStore, World
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.semantics.services import DerivativeService
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T
from cas.workflow.workspace import Workspace

E = TypeVar("E")


@dataclass(frozen=True, slots=True, eq=False)
class Runtime(Generic[E]):
    """One assembled world, its algebra view, ledger and supported operation."""

    def __post_init__(self) -> None:
        for operation in self.operations:
            for binding in operation.checker_bindings:
                spec = self.store.checkers.spec(binding.checker_id)
                if spec is None:
                    raise ValueError(
                        f"operation {operation.id!r} names an unregistered "
                        f"checker {binding.checker_id!r}"
                    )
                if spec.world != self.frames.world.id:
                    raise ValueError(
                        f"operation {operation.id!r} binds a checker from "
                        "another world"
                    )
                if binding.problem_kind not in spec.accepted_problem_kinds:
                    raise ValueError(
                        f"operation {operation.id!r} binds a checker that "
                        "does not accept its problem kind"
                    )
                if (
                    binding.specification_kind
                    not in spec.accepted_specification_kinds
                ):
                    raise ValueError(
                        f"operation {operation.id!r} binds a checker that "
                        "does not accept its specification kind"
                    )

    table: SymbolTable
    signature: LanguageSignature
    world: World
    frames: FrameStore
    frame: Frame
    variable: SymbolId
    ring: PolynomialRing[E]
    parent: Parent[Polynomial[E]]
    differential: DifferentialStructure[Polynomial[E]]
    vocabulary: DerivativeVocabulary
    checker: Checker
    store: KernelStore
    bridge: PolynomialBridge[E]
    request: AlgebraRequest
    derivative: DerivativeService
    operations: OperationRegistry
    specialization: SpecializationView | None = None
    elementary: ElementaryLibrary | None = None


def _core_specs(
    frames: FrameStore, signature: LanguageSignature
) -> dict[str, CheckerSpec]:
    """The scope and condition rules every assembled runtime admits."""
    return {
        ConditionChecker.id: CheckerSpec(
            ConditionChecker(frames, signature),
            CertificateSchema("condition", "1", type(None)),
            frozenset({"discharge"}),
            frozenset({"Condition"}),
            frames.world.id,
        ),
        HypothesisChecker.id: CheckerSpec(
            HypothesisChecker(frames),
            CertificateSchema("hypothesis", "1", type(None)),
            frozenset({"assume"}),
            frozenset({"Hypothesis"}),
            frames.world.id,
        ),
        ContradictionChecker.id: CheckerSpec(
            ContradictionChecker(frames, signature),
            CertificateSchema("contradiction", "1", type(None)),
            frozenset({"consistency"}),
            frozenset({"Contradiction"}),
            frames.world.id,
        ),
    }


def _start(
    *,
    table: SymbolTable | None = None,
    declarations: DeclarationSet | None = None,
) -> tuple[SymbolTable, DerivativeVocabulary, LanguageSignature, FrameStore]:
    """The common world and frame store every assembled runtime starts with.

    With declarations, the language is assembled by the declaration DSL; without
    them it contains only the structural heads and the derivative predicate.
    """
    actual = SymbolTable() if table is None else table
    predicate = actual.intern("HasDerivative")
    vocabulary = DerivativeVocabulary(predicate, "HasDerivative")
    extras = {predicate: vocabulary.signature}
    signature = (
        standard_language(actual, operators=extras)
        if declarations is None
        else build_language(actual.intern, declarations, extras)
    )
    world = World(WorldId(0), signature)
    return actual, vocabulary, signature, FrameStore(world)


def _derivative_spec(
    checker: Checker,
    world: WorldId,
    *,
    problem_kind: str = "differentiate",
    dependencies: tuple[BasisRef, ...] = (),
) -> CheckerSpec:
    """The one trust registration shared by derivative checkers."""
    return CheckerSpec(
        checker,
        CertificateSchema("derivative", "1", DerivativeCertificate),
        frozenset({problem_kind}),
        frozenset({"HasDerivative"}),
        world,
        dependencies,
    )


def _q_coefficient(
    registry: ParentRegistry,
) -> tuple[RationalField, Parent[Fraction]]:
    rationals = RationalField()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    return rationals, coefficient


def _polynomial_spec(
    base: ParentSpec | None,
    generators: tuple[SymbolId, ...],
    order: MonomialOrder = MonomialOrder.LEX,
) -> ParentSpec:
    """A polynomial description that states every representation choice."""
    return ParentSpec(
        "polynomial",
        base=base,
        generators=generators,
        options=(("monomial_order", order.value),),
    )


def _q_polynomial(
    registry: ParentRegistry,
    variable: SymbolId,
) -> tuple[
    RationalField,
    Parent[Fraction],
    UnivariatePolynomialRing[Fraction],
    Parent[Polynomial[Fraction]],
    DifferentialStructure[Polynomial[Fraction]],
]:
    rationals, coefficient = _q_coefficient(registry)
    ring = UnivariatePolynomialRing(variable, rationals)
    parent = registry.intern(
        _polynomial_spec(coefficient.spec, (variable,)),
        ring,
    )
    differential = polynomial_structure(parent, 0)
    return rationals, coefficient, ring, parent, differential


def bootstrap() -> Runtime[Fraction]:
    """Assemble Q[x] with target `x` and no formal parameters."""
    table, vocabulary, signature, frames = _start()
    variable = table.intern("x")
    frame = frames.create(
        frames.root.id,
        declarations=(Declaration(variable, "x", S.REAL),),
    )
    registry = ParentRegistry()
    _, coefficient, ring, parent, differential = _q_polynomial(
        registry, variable
    )
    bridge = SimplePolynomialBridge(
        ring, signature, table.name_of, T.number
    )
    checker = DerivativeChecker(
        ring, signature, vocabulary, bridge.to_value
    )
    specs = {
        checker.id: _derivative_spec(checker, frames.world.id),
        **_core_specs(frames, signature),
    }
    store = KernelStore(frames, CheckerRegistry(specs))
    request = AlgebraRequest(
        coefficient=coefficient,
        parameter_ring=None,
        parameters=(),
        target=variable,
        parameter_mode=ParameterMode.SPECIFIED_VALUES,
        interpretation=Interpretation.FORMAL,
    )
    service = PolynomialDerivativeService(
        bridge, differential, checker.id, "HasDerivative"
    )
    differentiation = DifferentiationOperation(
        signature,
        frames,
        vocabulary,
        request,
        table.name_of,
        service,
    )
    operations = OperationRegistry(
        {differentiation.id: differentiation}
    )
    return Runtime(
        table,
        signature,
        frames.world,
        frames,
        frame,
        variable,
        ring,
        parent,
        differential,
        vocabulary,
        checker,
        store,
        bridge,
        request,
        derivative=service,
        operations=operations,
    )


def bootstrap_parameterized(
    parameters: tuple[str, ...] = ("a",),
    *,
    parameter_mode: ParameterMode = ParameterMode.ALL_PARAMETER_VALUES,
) -> Runtime[Polynomial[Fraction]]:
    """Assemble Q[parameters][x] with formal parameters as coefficients.

    Parameters are ordinary declared symbols, but their role in this request is
    coefficient generator; `x` is the target. The bridge maps each role
    explicitly, so the two namespaces cannot be confused.

    The ordinary parameter-family request asks for all declared parameter
    values. The polynomial derivative introduces no denominator or branch, so
    its generic result is unconditional and can meet that request. A caller may
    still ask for `GENERIC_PARAMETERS`, in which case the result claims only the
    formal family. `SPECIFIED_VALUES` is rejected: this assembly has no exact
    values to fix.
    """
    if not parameters:
        raise ValueError("a parameterized runtime needs at least one parameter")
    if len(set(parameters)) != len(parameters):
        raise ValueError("parameter names must be distinct")
    if "x" in parameters:
        raise ValueError("the target name x cannot also be a parameter")
    if parameter_mode not in {
        ParameterMode.GENERIC_PARAMETERS,
        ParameterMode.ALL_PARAMETER_VALUES,
    }:
        raise ValueError(
            "a formal parameter family needs generic or all-values coverage"
        )
    reserved = {head.value for head in StructuralHead} | {"HasDerivative"}
    for name in parameters:
        if name in reserved:
            raise ValueError(f"parameter name is reserved: {name}")
    table, vocabulary, signature, frames = _start()
    variable = table.intern("x")
    parameter_ids = tuple(table.intern(name) for name in parameters)
    declarations = (Declaration(variable, "x", S.REAL),) + tuple(
        Declaration(identifier, name, S.REAL)
        for identifier, name in zip(parameter_ids, parameters)
    )
    frame = frames.create(frames.root.id, declarations=declarations)

    registry = ParentRegistry()
    rationals, coefficient = _q_coefficient(registry)
    parameter_ring = PolynomialRing(parameter_ids, rationals)
    parameter_parent = registry.intern(
        _polynomial_spec(coefficient.spec, parameter_ids),
        parameter_ring,
    )
    target_ring = PolynomialRing((variable,), parameter_ring)
    target_parent = registry.intern(
        _polynomial_spec(parameter_parent.spec, (variable,)),
        target_ring,
    )
    differential = polynomial_structure(target_parent, 0)

    def embed_rational(value: Fraction) -> Polynomial[Fraction]:
        return parameter_ring.constant(
            rationals.of_rational(value.numerator, value.denominator)
        )

    bridge = ParameterPolynomialBridge(
        target_ring,
        parameter_ring,
        {identifier: index for index, identifier in enumerate(parameter_ids)},
        signature,
        table.name_of,
        embed_rational,
        T.number,
    )
    checker = DerivativeChecker(
        target_ring, signature, vocabulary, bridge.to_value
    )

    base_ring = UnivariatePolynomialRing(variable, rationals)
    base_parent = registry.intern(
        _polynomial_spec(coefficient.spec, (variable,)),
        base_ring,
    )
    base_differential = polynomial_structure(base_parent, 0)
    base_bridge = SimplePolynomialBridge(
        base_ring, signature, table.name_of, T.number
    )
    base_checker = DerivativeChecker(
        base_ring,
        signature,
        vocabulary,
        base_bridge.to_value,
        identifier="calculus.derivative.specialized",
    )
    specs = {
        checker.id: _derivative_spec(checker, frames.world.id),
        base_checker.id: _derivative_spec(
            base_checker, frames.world.id, problem_kind="specialize"
        ),
        **_core_specs(frames, signature),
    }
    store = KernelStore(frames, CheckerRegistry(specs))
    request = AlgebraRequest(
        coefficient=coefficient,
        parameter_ring=parameter_parent,
        parameters=parameter_ids,
        target=variable,
        parameter_mode=parameter_mode,
        interpretation=Interpretation.PARAMETER_FAMILY,
    )
    specialized_request = AlgebraRequest(
        coefficient=coefficient,
        parameter_ring=None,
        parameters=(),
        target=variable,
        parameter_mode=ParameterMode.SPECIFIED_VALUES,
        interpretation=Interpretation.EMBEDDED,
    )
    specialization_view = SpecializationView(
        base_ring,
        base_parent,
        base_differential,
        base_bridge,
        base_checker,
        specialized_request,
    )
    service = PolynomialDerivativeService(
        bridge, differential, checker.id, "HasDerivative"
    )
    differentiation = DifferentiationOperation(
        signature,
        frames,
        vocabulary,
        request,
        table.name_of,
        service,
    )
    specialization_operation = SpecializationOperation(
        signature,
        frames,
        vocabulary,
        table.name_of,
        specialization_view,
        request,
    )
    operations = OperationRegistry(
        {
            differentiation.id: differentiation,
            specialization_operation.id: specialization_operation,
        }
    )
    return Runtime(
        table,
        signature,
        frames.world,
        frames,
        frame,
        variable,
        target_ring,
        target_parent,
        differential,
        vocabulary,
        checker,
        store,
        bridge,
        request,
        derivative=service,
        operations=operations,
        specialization=specialization_view,
    )


def bootstrap_elementary() -> Runtime[Fraction]:
    """Assemble the declared elementary fragment with target `x` over Q.

    The Q[x] fields are the algebra view of the polynomial subfragment. The
    active candidate generator and checker are the elementary ones; every
    function and law comes from the declaration file admitted at assembly.
    """
    source = default_elementary_declarations()
    basis = BasisRef(
        source.name,
        BasisKind.DECLARATION_FILE,
        "1",
        source.digest,
        WorldId(0),
    )
    table = SymbolTable()
    table, vocabulary, signature, frames = _start(
        table=table, declarations=source
    )
    library = build_elementary(
        table.intern,
        source,
        reserved=frozenset({"x", "HasDerivative"}),
        basis=basis,
    )
    variable = table.intern("x")
    declarations = (Declaration(variable, "x", S.REAL),) + tuple(
        Declaration(constant.symbol, constant.name, constant.sort)
        for constant in library.constants.values()
    )
    frame = frames.create(frames.root.id, declarations=declarations)

    registry = ParentRegistry()
    _, coefficient, ring, parent, differential = _q_polynomial(
        registry, variable
    )
    bridge = SimplePolynomialBridge(
        ring, signature, table.name_of, T.number
    )

    checker = ElementaryDerivativeChecker(
        library, signature, vocabulary, variable
    )
    specs = {
        checker.id: _derivative_spec(
            checker, frames.world.id, dependencies=(basis,)
        ),
        **_core_specs(frames, signature),
    }
    store = KernelStore(frames, CheckerRegistry(specs))
    differentiator = ElementaryDifferentiator(
        library, signature, variable, table.name_of
    )
    request = AlgebraRequest(
        coefficient=coefficient,
        parameter_ring=None,
        parameters=(),
        target=variable,
        parameter_mode=ParameterMode.SPECIFIED_VALUES,
        interpretation=Interpretation.FORMAL,
    )
    service = ElementaryDerivativeService(
        differentiator, checker.id, "HasDerivative"
    )
    differentiation = DifferentiationOperation(
        signature,
        frames,
        vocabulary,
        request,
        table.name_of,
        service,
    )
    operations = OperationRegistry(
        {differentiation.id: differentiation}
    )
    return Runtime(
        table,
        signature,
        frames.world,
        frames,
        frame,
        variable,
        ring,
        parent,
        differential,
        vocabulary,
        checker,
        store,
        bridge,
        request,
        derivative=service,
        operations=operations,
        elementary=library,
    )


def new_workspace(runtime: Runtime[Any]) -> Workspace:
    """Start an empty workspace over an assembled runtime."""
    return Workspace(runtime)


__all__ = [
    "Runtime",
    "bootstrap",
    "bootstrap_elementary",
    "bootstrap_parameterized",
    "new_workspace",
]
