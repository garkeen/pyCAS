"""Type inference over pure syntax.

`infer` answers one question: which sort does this term denote, given a
signature and the declared sorts of free symbols? It does not decide
definedness, equivalence or declared function laws; those belong to semantic
elaboration.

The outcome is a closed hierarchy so that "cannot type" never collapses into a
bare ``None``:

- ``Typed(sort)``;
- ``NeedsDeclaration(symbol_id)`` — a free symbol has no declaration;
- ``Unsupported(detail)`` — a construct whose typing needs elaboration;
- ``IllTyped(detail)`` — the construct is structurally unusable.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from cas.foundation.ids import SymbolId
from cas.language import sorts as S
from cas.language.signatures import LanguageSignature, OperatorSignature, StructuralHead
from cas.syntax import term as T


class SortEnvironment(Protocol):
    """The declaration half of the environment: sorts of free symbols."""

    def sort_of(self, symbol_id: SymbolId) -> S.Sort | None:
        """Return the declared sort, or None when the symbol is not declared."""


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


@dataclass(frozen=True, slots=True)
class Unsupported(Typing):
    detail: str


@dataclass(frozen=True, slots=True)
class IllTyped(Typing):
    detail: str


_COMPARISONS = frozenset(
    {
        StructuralHead.EQ,
        StructuralHead.NE,
        StructuralHead.LT,
        StructuralHead.LE,
        StructuralHead.GT,
        StructuralHead.GE,
    }
)

_ORDERS = frozenset(
    {
        StructuralHead.LT,
        StructuralHead.LE,
        StructuralHead.GT,
        StructuralHead.GE,
    }
)


def infer(
    term: T.Term,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> Typing:
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
        return IllTyped("a bound variable has no sort outside its binder")
    if isinstance(term, T.SymbolRef):
        sort = environment.sort_of(term.symbol_id)
        if sort is None:
            return NeedsDeclaration(term.symbol_id)
        return Typed(sort)
    if isinstance(term, T.Binder):
        return Unsupported(
            "binder variables receive their sorts from elaboration, "
            "not from syntax inference"
        )
    if isinstance(term, T.Apply):
        return _apply(term, signature, environment)
    return IllTyped(f"unknown term variant: {type(term).__name__}")


def _apply(
    term: T.Apply,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> Typing:
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
    sorts: list[S.Sort] = []
    for argument in term.arguments:
        result = infer(argument, signature, environment)
        if not isinstance(result, Typed):
            return result
        sorts.append(result.sort)
    return _apply_sorted(head, sorts)


def _apply_declared(
    declared: OperatorSignature,
    term: T.Apply,
    signature: LanguageSignature,
    environment: SortEnvironment,
) -> Typing:
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


def _apply_sorted(head: StructuralHead, sorts: list[S.Sort]) -> Typing:
    if head in (StructuralHead.PLUS, StructuralHead.TIMES):
        return _common_scalar(head, sorts)
    if head is StructuralHead.POWER:
        base, exponent = sorts
        if not S.is_scalar(base):
            return IllTyped("Power is defined on a scalar base")
        if exponent not in (S.INTEGER, S.RATIONAL):
            return IllTyped("Power needs an exponent of exact rational type")
        return Typed(base)
    if head in _COMPARISONS:
        common = S.join(sorts[0], sorts[1])
        if common is None:
            return IllTyped("comparison operands have no common sort")
        if head in _ORDERS and not S.is_ordered(common):
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
    if head is StructuralHead.QUOTE:
        return Typed(S.SYNTAX)
    return Unsupported(f"no typing rule for {head.value}")


def _common_scalar(head: StructuralHead, sorts: list[S.Sort]) -> Typing:
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
    "IllTyped",
    "NeedsDeclaration",
    "SortEnvironment",
    "Typed",
    "Typing",
    "Unsupported",
    "infer",
]
