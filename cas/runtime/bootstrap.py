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
from cas.kernel.evidence import CheckerRegistry
from cas.kernel.store import KernelStore
from cas.language import sorts as S
from cas.language.problems import ParameterMode
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.math.calculus.differentiation.checker import DerivativeChecker
from cas.math.calculus.differentiation.specification import DerivativeVocabulary
from cas.semantics.bridge import (
    ParameterPolynomialBridge,
    PolynomialBridge,
    SimplePolynomialBridge,
)
from cas.semantics.differential import DifferentialStructure, polynomial_structure
from cas.semantics.frames import Declaration, Frame, FrameStore, World
from cas.semantics.request import AlgebraRequest, Interpretation
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
    checker: DerivativeChecker[E]
    store: KernelStore
    bridge: PolynomialBridge[E]
    request: AlgebraRequest


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
    store = KernelStore(frames, CheckerRegistry({checker.id: checker}))
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
    )


def bootstrap_parameterized(
    parameters: tuple[str, ...] = ("a",),
) -> Runtime[Polynomial[Fraction]]:
    """Assemble Q[parameters][x] with formal parameters as coefficients.

    Parameters are ordinary declared symbols, but their role in this request is
    coefficient generator; `x` is the target. The bridge maps each role
    explicitly, so the two namespaces cannot be confused.
    """
    if not parameters:
        raise ValueError("a parameterized runtime needs at least one parameter")
    if len(set(parameters)) != len(parameters):
        raise ValueError("parameter names must be distinct")
    if "x" in parameters:
        raise ValueError("the target name x cannot also be a parameter")
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
    store = KernelStore(frames, CheckerRegistry({checker.id: checker}))
    request = AlgebraRequest(
        coefficient=coefficient,
        parameter_ring=parameter_parent,
        parameters=parameter_ids,
        target=variable,
        parameter_mode=ParameterMode.GENERIC_PARAMETERS,
        interpretation=Interpretation.PARAMETER_FAMILY,
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
    )


def new_workspace(runtime: Runtime[Any]) -> Workspace:
    """Start an empty workspace over an assembled runtime."""
    return Workspace(runtime)


__all__ = [
    "Runtime",
    "bootstrap",
    "bootstrap_parameterized",
    "new_workspace",
]
