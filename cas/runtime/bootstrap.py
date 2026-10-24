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
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId, WorldId
from cas.kernel.applicability import ConditionChecker
from cas.kernel.consistency import ContradictionChecker
from cas.kernel.context_rules import HypothesisChecker
from cas.kernel.evidence import Checker, CheckerRegistry, CheckerSpec
from cas.kernel.model import BasisKind, BasisRef, CertificateSchema
from cas.kernel.store import KernelStore
from cas.language import sorts as S
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
    default_elementary_source,
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
            ConditionChecker(signature),
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


def _world(
    table: SymbolTable, predicate: SymbolId
) -> tuple[DerivativeVocabulary, LanguageSignature, World]:
    vocabulary = DerivativeVocabulary(predicate, "HasDerivative")
    signature = standard_language(
        table, operators={predicate: vocabulary.signature}
    )
    world = World(WorldId(0), signature)
    return vocabulary, signature, world


def bootstrap() -> Runtime[Fraction]:
    """Assemble Q[x] with target `x` and no formal parameters."""
    table = SymbolTable()
    predicate = table.intern("HasDerivative")
    vocabulary, signature, world = _world(table, predicate)
    frames = FrameStore(world)
    variable = table.intern("x")
    frame = frames.create(
        frames.root.id,
        declarations=(Declaration(variable, "x", S.REAL),),
    )
    rationals = RationalField()
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    ring = UnivariatePolynomialRing(variable, rationals)
    parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=(variable,),
        ),
        ring,
    )
    differential = polynomial_structure(parent, 0)
    bridge = SimplePolynomialBridge(
        ring, signature, table.name_of, T.number
    )
    checker = DerivativeChecker(
        ring, signature, vocabulary, bridge.to_value
    )
    specs = {
        checker.id: CheckerSpec(
            checker,
            CertificateSchema("derivative", "1", DerivativeCertificate),
            frozenset({"differentiate"}),
            frozenset({"HasDerivative"}),
            world.id,
        ),
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
        variable,
        table.name_of,
        service,
        request.parameter_mode,
    )
    operations = OperationRegistry(
        {differentiation.id: differentiation}
    )
    return Runtime(
        table,
        signature,
        world,
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
    table = SymbolTable()
    predicate = table.intern("HasDerivative")
    vocabulary, signature, world = _world(table, predicate)
    frames = FrameStore(world)
    variable = table.intern("x")
    parameter_ids = tuple(table.intern(name) for name in parameters)
    declarations = (Declaration(variable, "x", S.REAL),) + tuple(
        Declaration(identifier, name, S.REAL)
        for identifier, name in zip(parameter_ids, parameters)
    )
    frame = frames.create(frames.root.id, declarations=declarations)

    rationals = RationalField()
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    parameter_ring = PolynomialRing(parameter_ids, rationals)
    parameter_parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=parameter_ids,
        ),
        parameter_ring,
    )
    target_ring = PolynomialRing((variable,), parameter_ring)
    target_parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=parameter_parent.spec,
            generators=(variable,),
        ),
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
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=(variable,),
        ),
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
        checker.id: CheckerSpec(
            checker,
            CertificateSchema("derivative", "1", DerivativeCertificate),
            frozenset({"differentiate"}),
            frozenset({"HasDerivative"}),
            world.id,
        ),
        base_checker.id: CheckerSpec(
            base_checker,
            CertificateSchema("derivative", "1", DerivativeCertificate),
            frozenset({"specialize"}),
            frozenset({"HasDerivative"}),
            world.id,
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
        variable,
        table.name_of,
        service,
        request.parameter_mode,
    )
    specialization_operation = SpecializationOperation(
        signature,
        frames,
        vocabulary,
        variable,
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
        world,
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
    source = default_elementary_source()
    basis = BasisRef(
        source.name,
        BasisKind.DECLARATION_FILE,
        "1",
        source.digest,
        WorldId(0),
    )
    table = SymbolTable()
    predicate = table.intern("HasDerivative")
    vocabulary = DerivativeVocabulary(predicate, "HasDerivative")
    library = build_elementary(
        table.intern,
        source,
        reserved=frozenset({"x", "HasDerivative"}),
        basis=basis,
    )
    signature = standard_language(
        table,
        operators={predicate: vocabulary.signature, **library.operators},
    )
    world = World(WorldId(0), signature)
    frames = FrameStore(world)
    variable = table.intern("x")
    declarations = (Declaration(variable, "x", S.REAL),) + tuple(
        Declaration(constant.symbol, constant.name, constant.sort)
        for constant in library.constants.values()
    )
    frame = frames.create(frames.root.id, declarations=declarations)

    rationals = RationalField()
    registry = ParentRegistry()
    coefficient = registry.intern(ParentSpec("Q"), rationals)
    ring = UnivariatePolynomialRing(variable, rationals)
    parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=coefficient.spec,
            generators=(variable,),
        ),
        ring,
    )
    differential = polynomial_structure(parent, 0)
    bridge = SimplePolynomialBridge(
        ring, signature, table.name_of, T.number
    )

    checker = ElementaryDerivativeChecker(
        library, signature, vocabulary, variable, table.name_of
    )
    specs = {
        checker.id: CheckerSpec(
            checker,
            CertificateSchema("derivative", "1", DerivativeCertificate),
            frozenset({"differentiate"}),
            frozenset({"HasDerivative"}),
            world.id,
            (basis,),
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
        variable,
        table.name_of,
        service,
        request.parameter_mode,
    )
    operations = OperationRegistry(
        {differentiation.id: differentiation}
    )
    return Runtime(
        table,
        signature,
        world,
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
