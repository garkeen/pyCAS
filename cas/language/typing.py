"""Type inference and the sealed typed-expression view.

`infer` answers one question: which sort does this term denote, given a
signature and the declared sorts of free symbols? It does not decide
definedness, equivalence or declared function laws; those belong to semantic
elaboration.

The inference outcome is a closed hierarchy so that "cannot type" never
collapses into a bare ``None``:

- ``Typed(sort)``;
- ``NeedsDeclaration(symbol_id)`` — a free symbol has no declaration;
- ``Unsupported(detail)`` — a construct whose typing needs elaboration;
- ``IllTyped(detail)`` — the construct is structurally unusable.

`typed` is the single sealed constructor of `TypedExpr`. It checks scoping
before inference, then records the sort, the meaning environment and the
declared free symbols in one immutable view.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Protocol, TypeAlias

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.meaning import MeaningKey
from cas.language.signatures import (
    COMPARISON_HEADS,
    ORDER_COMPARISON_HEADS,
    LanguageSignature,
    OperatorSignature,
    StructuralHead,
)
from cas.syntax import binding as B
from cas.syntax import term as T

_SEAL = object()


class SortEnvironment(Protocol):
    """The declaration half of the environment: sorts of free symbols."""

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        """Return the declared sort, or None when the symbol is not declared."""

    def bound_sort(self, index: int) -> S.Sort | None:
        """Return the sort of a bound variable, or None outside a binder."""


class Typing:
    __slots__ = ()

    def is_typed(self) -> bool:
        return isinstance(self, Typed)


@dataclass(frozen=True, slots=True)
class Typed(Typing):
    sort: S.Sort


@dataclass(frozen=True, slots=True)
class NeedsDeclaration(Typing):
    symbol_id: SymbolId

    @property
    def detail(self) -> str:
        """A uniform explanation derived from the missing declaration."""
        return f"symbol {self.symbol_id} is undeclared"

    @property
    def missing(self) -> frozenset[str]:
        """The capability this failure lacks."""
        return frozenset({"declaration"})


@dataclass(frozen=True, slots=True)
class Unsupported(Typing):
    detail: str

    @property
    def missing(self) -> frozenset[str]:
        """The capability this failure lacks."""
        return frozenset({"typing_rule"})


@dataclass(frozen=True, slots=True)
class IllTyped(Typing):
    detail: str

    @property
    def missing(self) -> frozenset[str]:
        """The capability this failure lacks."""
        return frozenset({"well_typed"})


@dataclass(frozen=True, slots=True)
class IllScoped:
    """The term contains a bound index with no enclosing binder."""

    detail: str

    @property
    def missing(self) -> frozenset[str]:
        """The capability this failure lacks."""
        return frozenset({"well_scoped"})


@dataclass(frozen=True, slots=True)
class FreeSymbol:
    """A declared free symbol and its sort inside one typed expression."""

    symbol_id: SymbolId
    sort: S.Sort

    def __post_init__(self) -> None:
        if isinstance(self.symbol_id, bool) or not isinstance(
            self.symbol_id, int
        ):
            raise TypeError("a free symbol needs a SymbolId")
        if not isinstance(self.sort, S.Sort):
            raise TypeError("a free symbol needs a sort")


@dataclass(frozen=True, slots=True)
class BindingView:
    """The declared free symbols of one typed expression.

    The view is deliberately not binder-aware: bound variables are internal to
    their binder and never appear here.  Language heads and declared operators
    also carry no declaration sort, so they are not free symbols of the typed
    expression.  Entries are sorted and deduplicated by `SymbolId`.
    """

    symbols: tuple[FreeSymbol, ...] = ()

    def __post_init__(self) -> None:
        symbols = tuple(self.symbols)
        if any(not isinstance(item, FreeSymbol) for item in symbols):
            raise TypeError("a binding view holds free symbols")
        identifiers = tuple(item.symbol_id for item in symbols)
        if identifiers != tuple(sorted(set(identifiers))):
            raise ValueError(
                "binding-view symbols must be sorted and distinct by SymbolId"
            )
        object.__setattr__(self, "symbols", symbols)


_TYPED_FIELDS = frozenset({"term", "sort", "meaning", "bindings"})


def _require_typed_seal(value: object) -> None:
    """Refuse a typed expression whose factory did not set the module seal."""
    try:
        seal = object.__getattribute__(value, "_seal")
    except AttributeError:
        seal = None
    if seal is not _SEAL:
        raise ValueError("a typed expression is issued only by typing.typed")


@dataclass(frozen=True, slots=True)
class TypedExpr:
    """A term that has been scoped, typed and tied to a meaning environment.

    Construction requires the module seal; use `typed`.  `dataclasses.replace`
    cannot reproduce a typed expression, because the replacement is built
    through `__init__` without the seal and is refused by `__post_init__`.
    """

    term: T.Term
    sort: S.Sort
    meaning: MeaningKey
    bindings: BindingView
    _seal: object | None = field(
        init=False, default=None, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError("a typed expression is issued only by typing.typed")
        if not isinstance(self.term, T.Term):
            raise TypeError("a typed expression needs a term")
        if not isinstance(self.sort, S.Sort):
            raise TypeError("a typed expression needs a sort")
        if not isinstance(self.meaning, MeaningKey):
            raise TypeError("a typed expression needs a meaning key")
        if not isinstance(self.bindings, BindingView):
            raise TypeError("a typed expression needs a binding view")

    def __getattribute__(self, name: str) -> object:
        if name in _TYPED_FIELDS:
            _require_typed_seal(self)
        return object.__getattribute__(self, name)


InferenceOutcome: TypeAlias = (
    Typed | NeedsDeclaration | Unsupported | IllTyped
)
TypedExprFailure: TypeAlias = (
    NeedsDeclaration | Unsupported | IllTyped | IllScoped
)
TypedExprOutcome: TypeAlias = TypedExpr | TypedExprFailure


def _binding_view(
    term: T.Term,
    environment: SortEnvironment,
) -> BindingView:
    """Collect the declared free symbols of `term` in stable identity order."""
    symbols = tuple(
        FreeSymbol(symbol_id, sort)
        for symbol_id in sorted(B.free_symbols(term))
        if (sort := environment.sort_of(symbol_id)) is not None
    )
    return BindingView(symbols)


def _issue_typed(
    term: T.Term,
    sort: S.Sort,
    meaning: MeaningKey,
    bindings: BindingView,
) -> TypedExpr:
    """Construct one typed expression after setting the module seal."""
    value = object.__new__(TypedExpr)
    object.__setattr__(value, "term", term)
    object.__setattr__(value, "sort", sort)
    object.__setattr__(value, "meaning", meaning)
    object.__setattr__(value, "bindings", bindings)
    object.__setattr__(value, "_seal", _SEAL)
    value.__post_init__()
    return value


def typed(
    term: T.Term,
    signature: LanguageSignature,
    environment: SortEnvironment,
    meaning: MeaningKey,
) -> TypedExprOutcome:
    """Issue a `TypedExpr`, or explain why the term cannot be one.

    Scoping is checked before inference so that an escaping bound index is
    reported as `IllScoped`, never as an ill-typed formula.  The binding view
    is built only after inference succeeds: every declared free symbol then has
    a sort in the same environment.
    """
    if not B.well_scoped(term):
        return IllScoped("a term has a bound index outside its binder")
    outcome = infer(term, signature, environment)
    if not isinstance(outcome, Typed):
        return outcome
    return _issue_typed(
        term,
        outcome.sort,
        meaning,
        _binding_view(term, environment),
    )


def infer(
    term: T.Term,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> InferenceOutcome:
    """Infer the sort of `term`, or explain why it cannot be typed."""
    if isinstance(term, T.IntLit):
        return Typed(S.INTEGER)
    if isinstance(term, T.RatLit):
        return Typed(S.RATIONAL)
    if isinstance(term, T.BoolLit):
        return Typed(S.PROPOSITION)
    if isinstance(term, T.Quote):
        return Typed(S.SYNTAX)
    if isinstance(term, T.BoundVar):
        sort = environment.bound_sort(term.index)
        if sort is None:
            return IllTyped("a bound variable has no sort inside this scope")
        return Typed(sort)
    if isinstance(term, T.SymbolRef):
        sort = environment.sort_of(term.symbol_id)
        if sort is None:
            return NeedsDeclaration(term.symbol_id)
        return Typed(sort)
    if isinstance(term, T.Binder):
        return _infer_binder(term, signature, environment)
    if isinstance(term, T.Apply):
        return _apply(term, signature, environment)
    return IllTyped(f"unknown term variant: {type(term).__name__}")


class _BoundEnvironment:
    """A sort environment extended by the variables of enclosing binders."""

    __slots__ = ("_outer", "_sorts")

    def __init__(
        self,
        outer: SortEnvironment,
        sorts: tuple[S.Sort, ...],
    ) -> None:
        self._outer = outer
        self._sorts = sorts

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        return self._outer.sort_of(symbol_id)

    def bound_sort(self, index: int) -> S.Sort | None:
        if index < len(self._sorts):
            return self._sorts[index]
        return self._outer.bound_sort(index - len(self._sorts))


def _infer_binder(
    term: T.Binder,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> InferenceOutcome:
    scheme = signature.binder_of(term.signature)
    if scheme is None:
        return Unsupported(f"binder {term.signature!r} is not declared")
    if scheme.arity != term.arity:
        return IllTyped(
            f"binder {term.signature!r} introduces {scheme.arity} variables, "
            f"got {term.arity}"
        )
    if len(scheme.parameter_sorts) != scheme.arity:
        return Unsupported(
            f"binder {term.signature!r} has no declared parameter sorts"
        )
    for annotation in term.annotations:
        result = infer(annotation, signature, environment)
        if not isinstance(result, Typed):
            return result
    body = infer(
        term.body,
        signature,
        _BoundEnvironment(environment, scheme.parameter_sorts),
    )
    if not isinstance(body, Typed):
        return body
    if scheme.result is None:
        return Typed(
            S.FunctionSort(scheme.parameter_sorts, body.sort)
        )
    if not body.sort.embeds_into(scheme.result):
        return IllTyped(
            f"the body sort {body.sort!r} does not embed into {scheme.result!r}"
        )
    return Typed(scheme.result)


def _apply(
    term: T.Apply,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> InferenceOutcome:
    if not isinstance(term.operator, T.SymbolRef):
        return Unsupported("an applied expression must have a symbol operator")
    head = signature.head_of(term.operator.symbol_id)
    if head is None:
        declared = signature.operator_of(term.operator.symbol_id)
        if declared is None:
            return NeedsDeclaration(term.operator.symbol_id)
        return _apply_declared(declared, term, signature, environment)
    arity = signature.arity_of(head)
    if not arity.accepts(len(term.arguments)):
        return IllTyped(f"{head.value} takes {arity.describe()}")
    if head is StructuralHead.QUOTE:
        # Quoted syntax is held data: its content has no sort in this context.
        return Typed(S.SYNTAX)
    if head is StructuralHead.POWER:
        return _power(term.arguments[0], term.arguments[1], signature, environment)
    sorts: list[S.Sort] = []
    for argument in term.arguments:
        result = infer(argument, signature, environment)
        if not isinstance(result, Typed):
            return result
        sorts.append(result.sort)
    return _apply_sorted(head, sorts)


def _power(
    base_term: T.Term,
    exponent_term: T.Term,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> InferenceOutcome:
    """Type a power soundly with respect to the sign and kind of the exponent."""
    base = infer(base_term, signature, environment)
    if not isinstance(base, Typed):
        return base
    exponent = infer(exponent_term, signature, environment)
    if not isinstance(exponent, Typed):
        return exponent
    if not S.is_scalar(base.sort):
        return IllTyped("Power is defined on a scalar base")
    if exponent.sort not in (S.INTEGER, S.RATIONAL):
        return IllTyped("Power needs an exponent of exact rational type")
    if base.sort is S.UNKNOWN_SCALAR:
        return Typed(base.sort)
    if exponent.sort is S.RATIONAL:
        # An exact root may leave the real line (and the base's own field).
        return Typed(S.COMPLEX)
    if isinstance(exponent_term, T.IntLit) and exponent_term.value >= 0:
        return Typed(base.sort)
    # A symbolic or negative integer exponent may need an inverse, so an
    # integer base is no longer promised to stay integral.
    if base.sort is S.INTEGER:
        return Typed(S.RATIONAL)
    return Typed(base.sort)


def _apply_declared(
    declared: OperatorSignature,
    term: T.Apply,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> InferenceOutcome:
    """Type one application of a declared (non-structural) operator."""
    if len(term.arguments) != len(declared.arguments):
        return IllTyped(
            f"declared operator takes {len(declared.arguments)} arguments, "
            f"got {len(term.arguments)}"
        )
    for argument, expected in zip(term.arguments, declared.arguments):
        result = infer(argument, signature, environment)
        if not isinstance(result, Typed):
            return result
        if not result.sort.embeds_into(expected):
            return IllTyped(
                f"argument sort {result.sort!r} does not embed into {expected!r}"
            )
    return Typed(declared.result)


def _apply_sorted(head: StructuralHead, sorts: list[S.Sort]) -> InferenceOutcome:
    if head in (StructuralHead.PLUS, StructuralHead.TIMES):
        return _common_scalar(head, sorts)
    if head in COMPARISON_HEADS:
        common = S.join(sorts[0], sorts[1])
        if common is None:
            return IllTyped("comparison operands have no common sort")
        if head in ORDER_COMPARISON_HEADS and not S.is_ordered(common):
            return IllTyped("an order comparison needs an ordered sort")
        return Typed(S.PROPOSITION)
    if head in (StructuralHead.AND, StructuralHead.OR):
        if any(sort != S.PROPOSITION for sort in sorts):
            return IllTyped(f"{head.value} takes propositions")
        return Typed(S.PROPOSITION)
    if head is StructuralHead.NOT:
        if sorts[0] != S.PROPOSITION:
            return IllTyped("Not takes a proposition")
        return Typed(S.PROPOSITION)
    if head is StructuralHead.IMPLIES:
        if any(sort != S.PROPOSITION for sort in sorts):
            return IllTyped("Implies takes propositions")
        return Typed(S.PROPOSITION)
    if head is StructuralHead.GUARDED:
        condition, body = sorts
        if condition != S.PROPOSITION:
            return IllTyped("Guarded needs a proposition as its condition")
        return Typed(body)
    if head is StructuralHead.PIECEWISE:
        if len(sorts) % 2:
            return IllTyped("Piecewise takes (value, condition) pairs")
        conditions = sorts[1::2]
        if any(condition != S.PROPOSITION for condition in conditions):
            return IllTyped("every Piecewise branch needs a proposition condition")
        return _common_scalar(head, sorts[0::2])
    if head is StructuralHead.SET:
        if not sorts:
            # The empty set has no member sort.  It is not a nonempty set of
            # unknown-scalar members, which stays `empty=False`.
            return Typed(S.SetSort(S.UNKNOWN_SCALAR, empty=True))
        element: S.Sort = sorts[0]
        for sort in sorts[1:]:
            merged: S.Sort | None = S.join(element, sort)
            if merged is None:
                return IllTyped("Set members have no common sort")
            element = merged
        return Typed(S.SetSort(element, empty=False))
    return Unsupported(f"no typing rule for {head.value}")


def _common_scalar(head: StructuralHead, sorts: list[S.Sort]) -> InferenceOutcome:
    for sort in sorts:
        if not isinstance(sort, S.ScalarSort):
            return IllTyped(f"{head.value} is defined on scalars")
    common: S.Sort = sorts[0]
    for sort in sorts[1:]:
        merged = S.join(common, sort)
        if merged is None:
            return IllTyped(f"{head.value} arguments have no common scalar sort")
        common = merged
    return Typed(common)


__all__ = [
    "BindingView",
    "FreeSymbol",
    "IllScoped",
    "IllTyped",
    "NeedsDeclaration",
    "SortEnvironment",
    "Typed",
    "TypedExpr",
    "TypedExprFailure",
    "TypedExprOutcome",
    "Typing",
    "Unsupported",
    "infer",
    "typed",
]
