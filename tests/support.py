"""Constructors shared by the v5 tests.

These helpers only assemble already-public pieces; they never bypass a seal or a
validation that production code performs.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING

from cas.algebra.parents import Parent, ParentRegistry, ParentSpec
from cas.algebra.polynomial import MonomialOrder, Polynomial, PolynomialRing
from cas.foundation.ids import FrameId, SymbolId, WorldId
from cas.kernel.commit import (
    ValidatedCommitBatch,
    publish_commit,
    validate_commit,
)
from cas.kernel.evidence import AlgebraService, VerificationContext
from cas.kernel.trust import BasisKind, BasisRef
from cas.language import propositions as Pr
from cas.language import sorts as S
from cas.language import typing as Ty
from cas.language.declarations import DeclarationSet
from cas.language.problems import ParameterMode, VariableRoles
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.semantics import elaborate
from cas.semantics.bridge import (
    MultivariatePolynomialBridge,
    Rendered,
    ViewBuilt,
)
from cas.semantics.frames import Declaration, FrameSorts, FrameStore
from cas.semantics.request import AlgebraRequest, Interpretation
from cas.syntax import term as T

if TYPE_CHECKING:
    from cas.runtime.bootstrap import Runtime


class MapEnvironment:
    """An explicit symbol-to-sort table for typing tests."""

    def __init__(self, sorts: Mapping[SymbolId, S.Sort] | None = None) -> None:
        self._sorts: dict[SymbolId, S.Sort] = dict(sorts or {})

    def declare(self, symbol_id: SymbolId, sort: S.Sort) -> SymbolId:
        self._sorts[symbol_id] = sort
        return symbol_id

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        return self._sorts.get(symbol_id)

    def bound_sort(self, index: int) -> S.Sort | None:
        del index
        return None


class InconsistentSortEnvironment:
    """Return a scalar sort during inference and a function sort afterwards.

    A well-typed scalar expression cannot have a non-scalar free symbol.  The
    bridge still defends that invariant, so this environment issues the one
    sealed typed expression that exercises the refusal without forging it.
    """

    def __init__(self, symbol_id, scalar, binding):
        self._symbol_id = symbol_id
        self._scalar = scalar
        self._binding = binding
        self._calls = 0

    def sort_of(self, symbol_id):
        if symbol_id != self._symbol_id:
            return None
        self._calls += 1
        return self._scalar if self._calls == 1 else self._binding

    def bound_sort(self, index):
        del index
        return None


@dataclass(frozen=True, slots=True)
class MultivariateSetup:
    """An assembled Q[x_1, ..., x_n] view for the multivariate bridge tests."""

    frame: FrameId
    ring: PolynomialRing[Fraction]
    parent: Parent[Polynomial[Fraction]]
    bridge: MultivariatePolynomialBridge[Fraction]
    request: AlgebraRequest
    symbols: tuple[SymbolId, ...]


def multivariate_setup(
    runtime: "Runtime",
    names: tuple[str, ...] = ("x", "y"),
    *,
    extra_sorts: tuple[S.Sort, ...] = (),
    request_sorts: tuple[S.Sort, ...] | None = None,
    order: MonomialOrder = MonomialOrder.LEX,
) -> MultivariateSetup:
    """Assemble one multivariate view whose symbols are declared in a frame.

    `names[0]` must be the runtime's own variable: it is already declared in
    the root frame, so the child frame only adds the extra names.  `extra_sorts`
    declares each extra symbol and defaults to `REAL`; `request_sorts` overrides
    the sorts the request claims for all generators, which lets a test build a
    deliberately inconsistent request without forging a `VariableRoles` value.
    """
    symbols = tuple(runtime.table.intern(name) for name in names)
    if not symbols:
        raise ValueError("a multivariate setup needs at least one name")
    if len(set(symbols)) != len(symbols):
        raise ValueError("multivariate setup names must be distinct")
    if symbols[0] != runtime.variable:
        raise ValueError(
            "the first multivariate setup name must be the runtime variable"
        )
    extras = symbols[1:]
    declared = (
        tuple(extra_sorts)
        if extra_sorts
        else tuple(S.REAL for _ in extras)
    )
    if len(declared) != len(extras):
        raise ValueError("one extra sort per extra generator is required")
    extra_declarations: list[Declaration] = []
    effective: list[S.Sort] = []
    for symbol, sort in zip(extras, declared):
        existing = runtime.frames.sort_of(runtime.frame.id, symbol)
        if existing is not None:
            # `y` is declared by the default assembly now.  Re-declaring it in
            # a child frame is refused, so reuse the visible declaration and
            # require the requested sort to agree with it.
            if existing != sort:
                raise ValueError(
                    "an already declared generator has another sort"
                )
            effective.append(existing)
            continue
        effective.append(sort)
        extra_declarations.append(
            Declaration(symbol, runtime.table.name_of(symbol), sort)
        )
    frame = (
        runtime.frame
        if not extra_declarations
        else runtime.frames.create(
            runtime.frame.id,
            declarations=tuple(extra_declarations),
        )
    )
    frame_sorts = (S.REAL,) + tuple(effective)
    sorts = frame_sorts if request_sorts is None else tuple(request_sorts)
    ring = PolynomialRing(symbols, runtime.ring.coefficients, order)
    registry = ParentRegistry()
    parent = registry.intern(
        ParentSpec(
            "polynomial",
            base=runtime.request.coefficient.spec,
            generators=symbols,
            options=(("monomial_order", order.value),),
        ),
        ring,
    )
    bridge = MultivariatePolynomialBridge(
        ring,
        parent,
        runtime.world.id,
        runtime.signature,
        runtime.table.name_of,
        T.number,
    )
    request = AlgebraRequest(
        coefficient=runtime.request.coefficient,
        coefficient_domain=runtime.request.coefficient_domain,
        parameter_ring=None,
        roles=VariableRoles(
            None,
            (),
            ParameterMode.SPECIFIED_VALUES,
            runtime.world.id,
            None,
            (),
            symbols,
            sorts,
        ),
        interpretation=Interpretation.FORMAL,
    )
    return MultivariateSetup(frame.id, ring, parent, bridge, request, symbols)


def structural(signature: LanguageSignature, head: StructuralHead) -> T.SymbolRef:
    """The term-level symbol this world uses for a structural head."""
    identifier = signature.symbol_of(head)
    assert identifier is not None, f"the language has no symbol for {head}"
    return T.symbol(identifier, head.value)


def head_app(
    signature: LanguageSignature,
    head: StructuralHead,
    *arguments: T.Term,
) -> T.Apply:
    return T.app(structural(signature, head), *arguments)


def check_in(
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    term: T.Term,
) -> Pr.PropositionOutcome:
    return Pr.check(
        term,
        signature,
        FrameSorts(frames, frame),
        frames.get(frame).meaning,
    )


def typed_in(
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    term: T.Term,
) -> Ty.TypedExpr:
    """Issue the typed view of one test input without bypassing the seal."""
    outcome = elaborate.typed(term, frames, frame, signature)
    assert isinstance(outcome, Ty.TypedExpr), outcome
    return outcome


def admitted(runtime, term, *, frame=None, bridge=None, request=None):
    """Admit one test term through the production algebra bridge.

    The term is elaborated in `frame` and converted under `request`; a typing
    failure stays distinct from a bridge refusal.  `bridge` and `request` let a
    test use a runtime's non-default view (for example its specialization
    bridge) without copying any conversion logic.
    """
    identifier = runtime.frame.id if frame is None else frame
    typed = elaborate.typed(term, runtime.frames, identifier, runtime.signature)
    if not isinstance(typed, Ty.TypedExpr):
        return typed
    actual_bridge = runtime.bridge if bridge is None else bridge
    actual_request = runtime.request if request is None else request
    return actual_bridge.to_view(typed, actual_request)


def view_of(runtime, term, *, frame=None, bridge=None, request=None):
    """The algebra view `admitted` issues for one accepted test term."""
    outcome = admitted(
        runtime, term, frame=frame, bridge=bridge, request=request
    )
    assert isinstance(outcome, ViewBuilt), outcome
    return outcome.view


def render_value(runtime, value, *, view=None, bridge=None) -> T.Term:
    """Render one parent element through the production bridge."""
    actual_bridge = runtime.bridge if bridge is None else bridge
    if view is None:
        view = view_of(runtime, T.number(1), bridge=actual_bridge)
    outcome = actual_bridge.render(view, value)
    assert isinstance(outcome, Rendered), outcome
    return outcome.term


def require_proposition(outcome: Pr.PropositionOutcome) -> Pr.Proposition:
    assert isinstance(outcome, Pr.Proposition), outcome
    return outcome


def proposition_in(
    frames: FrameStore,
    frame: FrameId,
    signature: LanguageSignature,
    term: T.Term,
) -> Pr.Proposition:
    return require_proposition(check_in(frames, frame, signature, term))


def elementary_basis(
    source: DeclarationSet,
    world: WorldId = WorldId(0),
) -> BasisRef:
    """The admission record a basis-loaded elementary source must carry."""
    assert source.digest, "a loaded source carries its content digest"
    return BasisRef(
        source.name,
        BasisKind.DECLARATION_FILE,
        "1",
        source.digest,
        world,
    )


def variable(runtime: Runtime) -> T.SymbolRef:
    """The runtime's differentiation variable as a term."""
    return T.symbol(runtime.variable, runtime.table.name_of(runtime.variable))


def runtime_proposition(
    runtime: Runtime,
    term: T.Term,
    frame: FrameId | None = None,
) -> Pr.Proposition:
    identifier = runtime.frame.id if frame is None else frame
    return proposition_in(runtime.frames, identifier, runtime.signature, term)


def verification_context(
    runtime: Runtime,
    frame: FrameId | None = None,
    *,
    algebra: AlgebraRequest | None = None,
) -> VerificationContext:
    """The trusted context the kernel builds for `runtime`'s frame.

    `algebra` is the fixed request the kernel would derive from a mathematical
    proposal.  A function problem carries none, so the default stays `None`.
    """
    identifier = runtime.frame.id if frame is None else frame
    return VerificationContext(
        runtime.world.id,
        identifier,
        runtime.frames,
        algebra=None if algebra is None else AlgebraService(algebra),
    )


def equation(
    runtime: Runtime,
    left: T.Term,
    right: T.Term,
    frame: FrameId | None = None,
) -> Pr.Proposition:
    term = head_app(runtime.signature, StructuralHead.EQ, left, right)
    return runtime_proposition(runtime, term, frame)


def commit_now(store, proposal):
    """Validate and immediately publish one proposal for a test."""
    outcome = validate_commit(store, proposal)
    if isinstance(outcome, ValidatedCommitBatch):
        return publish_commit(store, outcome)
    return outcome
