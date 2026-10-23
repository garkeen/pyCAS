"""Explicit assembly of the runtime for the first vertical slice.

One call builds a world that can differentiate polynomials in one variable:
Q, K[x], the chosen derivation, the `HasDerivative` predicate and its checker,
a frame declaring `x : Real`, and the kernel ledger. Nothing is installed into
module-level state; consumers receive the returned value.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from cas.algebra.parents import Parent, ParentRegistry, ParentSpec
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId, WorldId
from cas.kernel.evidence import CheckerRegistry
from cas.kernel.store import KernelStore
from cas.language import sorts as S
from cas.language.signatures import LanguageSignature
from cas.math.calculus.differentiation.checker import DerivativeChecker
from cas.math.calculus.differentiation.specification import DerivativeVocabulary
from cas.semantics.differential import DifferentialStructure, polynomial_structure
from cas.semantics.frames import Declaration, Frame, FrameStore, World
from cas.semantics.symbols import SymbolTable, standard_language
from cas.workflow.workspace import Workspace


@dataclass(frozen=True, slots=True, eq=False)
class Runtime:
    """One assembled world, ledger and the operations this slice supports."""

    table: SymbolTable
    signature: LanguageSignature
    world: World
    frames: FrameStore
    frame: Frame
    variable: SymbolId
    ring: UnivariatePolynomialRing[Fraction]
    parent: Parent[Polynomial[Fraction]]
    differential: DifferentialStructure[Polynomial[Fraction]]
    vocabulary: DerivativeVocabulary
    checker: DerivativeChecker[Fraction]
    store: KernelStore


def bootstrap() -> Runtime:
    """Assemble the world explicitly and return it."""
    table = SymbolTable()
    predicate = table.intern("HasDerivative")
    vocabulary = DerivativeVocabulary(predicate, "HasDerivative")
    signature = standard_language(
        table, operators={predicate: vocabulary.signature}
    )
    world = World(WorldId(0), signature)
    frames = FrameStore(world)
    variable = table.intern("x")
    frame = frames.create(
        frames.root.id,
        declarations=(Declaration(variable, "x", S.REAL),),
    )
    ring = UnivariatePolynomialRing(variable, RationalField())
    parents = ParentRegistry()
    parent = parents.intern(
        ParentSpec("polynomial", base=ParentSpec("Q"), generators=(variable,)),
        ring,
    )
    differential = polynomial_structure(parent, 0)
    checker = DerivativeChecker(ring, signature, vocabulary)
    store = KernelStore(frames, CheckerRegistry({checker.id: checker}))
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
    )


def new_workspace(runtime: Runtime) -> Workspace:
    """Start an empty workspace over an assembled runtime."""
    return Workspace(runtime)


__all__ = ["Runtime", "bootstrap", "new_workspace"]
