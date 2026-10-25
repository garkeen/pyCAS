"""Session symbol table: one stable id per declared name.

Structural heads are interned first, so a language signature is built from ids
rather than spellings. A name maps to one id for the whole session; shadowing
uses `fresh`, which allocates a new id and makes it the current one for `intern`.
"""

from __future__ import annotations

from collections.abc import Mapping

from cas.foundation.ids import IdIssuer, SymbolId
from cas.language.declarations import DeclarationSet, build_language
from cas.language.signatures import LanguageSignature, OperatorSignature


class SymbolTable:
    """A session-scoped name table; the kernel never consults it."""

    __slots__ = ("_ids", "_names", "_issuer")

    def __init__(self) -> None:
        self._ids: dict[str, SymbolId] = {}
        self._names: dict[SymbolId, str] = {}
        self._issuer = IdIssuer()

    def intern(self, name: str) -> SymbolId:
        """The current id for a name, allocating one on first use."""
        if not name:
            raise ValueError("a symbol needs a name")
        existing = self._ids.get(name)
        return existing if existing is not None else self.fresh(name)

    def fresh(self, name: str) -> SymbolId:
        """A new id for `name`, shadowing the previous one for later `intern`s."""
        if not name:
            raise ValueError("a symbol needs a name")
        identifier = SymbolId(self._issuer.issue())
        self._ids[name] = identifier
        self._names[identifier] = name
        return identifier

    def name_of(self, identifier: SymbolId) -> str:
        return self._names[identifier]

    def lookup(self, name: str) -> SymbolId | None:
        return self._ids.get(name)

    def __len__(self) -> int:
        return self._issuer.issued


def standard_language(
    table: SymbolTable,
    operators: Mapping[SymbolId, OperatorSignature] | None = None,
) -> LanguageSignature:
    """Build the language signature, interning every structural head."""
    return build_language(table.intern, DeclarationSet(), operators)


__all__ = ["SymbolTable", "standard_language"]
