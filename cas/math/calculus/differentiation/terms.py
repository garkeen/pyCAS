"""Exact term construction used by the symbolic differentiator and verifier.

These helpers only apply identities that hold in the term language itself:
flattening an associative head, folding exact numeric literals, and removing
literal zeros and ones. They do not reorder unknown terms and they do not
simplify symbolic expressions.
"""

from __future__ import annotations

from fractions import Fraction

from cas.foundation.ids import SymbolId
from cas.language.signatures import LanguageSignature, StructuralHead
from cas.syntax import term as T


def numeric(term: T.Term) -> Fraction | None:
    if isinstance(term, T.IntLit):
        return Fraction(term.value)
    if isinstance(term, T.RatLit):
        return term.value
    return None


def _head(signature: LanguageSignature, head: StructuralHead) -> T.SymbolRef:
    symbol_id = signature.symbol_of(head)
    if symbol_id is None:
        raise ValueError(f"the language has no symbol for {head.value}")
    return T.symbol(symbol_id, head.value)


def plus(
    signature: LanguageSignature,
    *terms: T.Term,
) -> T.Term:
    """A sum with exact literal folding and zero removal."""
    flattened: list[T.Term] = []
    for term in terms:
        if (
            isinstance(term, T.Apply)
            and signature.head_of(
                _operator_id(term)
            )
            is StructuralHead.PLUS
        ):
            flattened.extend(term.arguments)
        else:
            flattened.append(term)
    coefficient = Fraction(0)
    symbolic: list[T.Term] = []
    for term in flattened:
        value = numeric(term)
        if value is None:
            symbolic.append(term)
        else:
            coefficient += value
    parts: list[T.Term] = []
    if coefficient != 0:
        parts.append(T.number(coefficient))
    parts.extend(symbolic)
    if not parts:
        return T.number(0)
    if len(parts) == 1:
        return parts[0]
    return T.app(_head(signature, StructuralHead.PLUS), *parts)


def times(
    signature: LanguageSignature,
    *factors: T.Term,
) -> T.Term:
    """A product with exact literal folding and zero/one removal."""
    flattened: list[T.Term] = []
    for factor in factors:
        if (
            isinstance(factor, T.Apply)
            and signature.head_of(
                _operator_id(factor)
            )
            is StructuralHead.TIMES
        ):
            flattened.extend(factor.arguments)
        else:
            flattened.append(factor)
    coefficient = Fraction(1)
    symbolic: list[T.Term] = []
    for factor in flattened:
        value = numeric(factor)
        if value is None:
            symbolic.append(factor)
        else:
            coefficient *= value
    if coefficient == 0:
        return T.number(0)
    parts: list[T.Term] = []
    if coefficient != 1:
        parts.append(T.number(coefficient))
    parts.extend(symbolic)
    if not parts:
        return T.number(1)
    if len(parts) == 1:
        return parts[0]
    return T.app(_head(signature, StructuralHead.TIMES), *parts)


def power(
    signature: LanguageSignature,
    base: T.Term,
    exponent: int,
) -> T.Term:
    if exponent < 0:
        raise ValueError("a symbolic power needs a nonnegative exponent")
    if exponent == 0:
        return T.number(1)
    if exponent == 1:
        return base
    return T.app(
        _head(signature, StructuralHead.POWER), base, T.number(exponent)
    )


def _operator_id(term: T.Apply) -> SymbolId:
    if not isinstance(term.operator, T.SymbolRef):
        raise ValueError("a structural application needs a symbol operator")
    return term.operator.symbol_id


__all__ = ["numeric", "plus", "power", "times"]
