"""Finite sets as a structural term form.

A set is language structure, not a mathematical function name.  The `Set` head
is part of the structural signature; its members are neutral terms.  The
canonical form is deduplication followed by the stable structural term order,
so set equality is structural equality of the canonical member sequence and a
set term is canonical once it is built through `set_term`.
"""

from __future__ import annotations

from cas.language.signatures import LanguageSignature, StructuralHead
from cas.syntax import term as T


def deduplicate(members: tuple[T.Term, ...]) -> tuple[T.Term, ...]:
    """Remove structurally repeated members, preserving first occurrence."""
    seen: set[T.Term] = set()
    out: list[T.Term] = []
    for member in members:
        if member in seen:
            continue
        seen.add(member)
        out.append(member)
    return tuple(out)


def _canonical_members(
    members: tuple[T.Term, ...],
) -> tuple[T.Term, ...]:
    """Deduplicate members and order them by the structural term order.

    `Term.__lt__` compares stable structural keys, not Python's randomized
    hash and not object identity, so the canonical order is process
    independent.
    """
    return tuple(sorted(deduplicate(members)))


def set_term(
    signature: LanguageSignature,
    members: tuple[T.Term, ...],
) -> T.Term:
    """Build the canonical finite-set term for `members`."""
    if any(not isinstance(member, T.Term) for member in members):
        raise TypeError("a set member must be a term")
    return T.app(
        signature.head_term(StructuralHead.SET), *_canonical_members(members)
    )


def set_members(
    term: T.Term,
    signature: LanguageSignature,
) -> tuple[T.Term, ...] | None:
    """The members of a `Set` application, or None for another term."""
    if not isinstance(term, T.Apply) or not isinstance(
        term.operator, T.SymbolRef
    ):
        return None
    head = signature.head_of(term.operator.symbol_id)
    if head is not StructuralHead.SET:
        return None
    return _canonical_members(term.arguments)


def is_set_term(term: T.Term, signature: LanguageSignature) -> bool:
    return set_members(term, signature) is not None


__all__ = [
    "deduplicate",
    "is_set_term",
    "set_members",
    "set_term",
]
