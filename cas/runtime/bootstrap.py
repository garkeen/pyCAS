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
from cas.language.decisions import Reason
from cas.language.problems import ParameterMode
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.calculus.differentiation.checker import (
    DerivativeCertificate,
    DerivativeChecker,
)
from cas.math.calculus.differentiation.elementary import (
    ElementaryDifferentiator,
)
from cas.math.calculus.differentiation.elementary_checker import (
    ElementaryDerivativeCertificate,
    ElementaryDerivativeChecker,
)
from cas.math.calculus.differentiation.specification import DerivativeVocabulary
from cas.math.elementary.declarations import (
    ElementaryLibrary,
    build_elementary,
    default_elementary_source,
)
from cas.semantics.bridge import (
    ParameterPolynomialBridge,
    PolynomialBridge,
    SimplePolynomialBridge,
)
from cas.semantics.differential import DifferentialStructure, polynomial_structure
from cas.semantics.frames import Declaration, Frame, FrameStore, World
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.semantics.services import (
    DerivationInvalid,
    DerivationOutcome,
    DerivationUnsupported,
    DerivativeService,
    Derived,
)
from cas.semantics.symbols import SymbolTable, standard_language
from cas.syntax import term as T
from cas.workflow.workspace import Workspace

E = TypeVar("E")


@dataclass(frozen=True, slots=True, eq=False)
class SpecializationRuntime:
    """The concrete `Q[x]` view used to specialize a parameter family.

    A specialization is a new algebra request, not a field homomorphism: the
    parameter ring disappears, and the target parent takes plain rational
    coefficients. The checker is independent of the family checker, so a
    specialized answer is verified in the specialized structure.
    """

    ring: UnivariatePolynomialRing[Fraction]
    parent: Parent[Polynomial[Fraction]]
    differential: DifferentialStructure[Polynomial[Fraction]]
    bridge: SimplePolynomialBridge[Fraction]
    checker: DerivativeChecker[Fraction]
    request: AlgebraRequest


@dataclass(frozen=True, slots=True)
class PolynomialDerivativeService(Generic[E]):
    """Candidate generation through a polynomial bridge and derivation."""

    bridge: PolynomialBridge[E]
    differential: DifferentialStructure[Polynomial[E]]
    checker_id: str
    specification_kind: str

    def candidate(self, term: T.Term) -> DerivationOutcome:
        value = self.bridge.to_value(term)
        if value is None:
            return DerivationUnsupported(
                Reason.FRAGMENT,
                "the source is outside the polynomial fragment",
            )
        rendered = self.bridge.to_term(self.differential.deriv(value))
        if rendered is None:
            return DerivationInvalid(
                "the derivative cannot be rendered in this language"
            )
        return Derived(rendered)

    def certificate(
        self,
        region: T.Term,
        source: T.Term,
        variable: SymbolId,
        candidate: T.Term,
    ) -> object:
        return DerivativeCertificate(region, source, variable, candidate)


@dataclass(frozen=True, slots=True)
class ElementaryDerivativeService:
    """Candidate generation through the declared elementary differentiator."""

    differentiator: ElementaryDifferentiator
    checker_id: str
    specification_kind: str

    def candidate(self, term: T.Term) -> DerivationOutcome:
        return self.differentiator.derive(term)

    def certificate(
        self,
        region: T.Term,
        source: T.Term,
        variable: SymbolId,
        candidate: T.Term,
    ) -> object:
        return ElementaryDerivativeCertificate(
            region, source, variable, candidate
        )


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
    specialization: SpecializationRuntime | None = None
    elementary: ElementaryLibrary | None = None


def _core_specs(
    frames: FrameStore, signature: LanguageSignature
) -> dict[str, CheckerSpec]:
    """The scope and condition rules every assembled runtime admits."""
    return {
        ConditionChecker.id: CheckerSpec(
            ConditionChecker(signature),
            CertificateSchema("condition", "1"),
            frozenset({"discharge"}),
            frozenset({"Condition"}),
        ),
        HypothesisChecker.id: CheckerSpec(
            HypothesisChecker(frames),
            CertificateSchema("hypothesis", "1"),
            frozenset({"assume"}),
            frozenset({"Hypothesis"}),
        ),
        ContradictionChecker.id: CheckerSpec(
            ContradictionChecker(frames, signature),
            CertificateSchema("contradiction", "1"),
            frozenset({"consistency"}),
            frozenset({"Contradiction"}),
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
            CertificateSchema("derivative", "1"),
            frozenset({"differentiate"}),
            frozenset({"HasDerivative"}),
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
        derivative=PolynomialDerivativeService(
            bridge, differential, checker.id, "HasDerivative"
        ),
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
            CertificateSchema("derivative", "1"),
            frozenset({"differentiate"}),
            frozenset({"HasDerivative"}),
        ),
        base_checker.id: CheckerSpec(
            base_checker,
            CertificateSchema("derivative", "1"),
            frozenset({"specialize"}),
            frozenset({"HasDerivative"}),
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
    specialization = SpecializationRuntime(
        base_ring,
        base_parent,
        base_differential,
        base_bridge,
        base_checker,
        specialized_request,
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
        derivative=PolynomialDerivativeService(
            bridge, differential, checker.id, "HasDerivative"
        ),
        specialization=specialization,
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
            CertificateSchema("elementary_derivative", "1"),
            frozenset({"differentiate"}),
            frozenset({"HasDerivative"}),
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
        derivative=ElementaryDerivativeService(
            differentiator, checker.id, "HasDerivative"
        ),
        elementary=library,
    )


def new_workspace(runtime: Runtime[Any]) -> Workspace:
    """Start an empty workspace over an assembled runtime."""
    return Workspace(runtime)


__all__ = [
    "Runtime",
    "SpecializationRuntime",
    "bootstrap",
    "bootstrap_elementary",
    "bootstrap_parameterized",
    "new_workspace",
]
