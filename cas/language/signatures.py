"""The structural signature of the term language.

These are the language's own constructors: arithmetic, comparison, logic and
binding. Mathematical function names are declared data and never appear here.

A `LanguageSignature` maps the *stable ids* of structural heads to their
meaning. Assembly issues those ids, so nothing in this module depends on a
display spelling.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from types import MappingProxyType
from typing import Mapping

from cas.foundation.ids import SymbolId


class StructuralHead(StrEnum):
    """The closed set of heads the language itself defines."""

    PLUS = "Plus"
    TIMES = "Times"
    POWER = "Power"
    EQ = "Eq"
    NE = "Ne"
    LT = "Lt"
    LE = "Le"
    GT = "Gt"
    GE = "Ge"
    AND = "And"
    OR = "Or"
    NOT = "Not"
    IMPLIES = "Implies"
    GUARDED = "Guarded"
    PIECEWISE = "Piecewise"
    QUOTE = "Quote"


@dataclass(frozen=True, slots=True)
class Arity:
    """An accepted argument count range; `maximum=None` means unbounded."""

    minimum: int
    maximum: int | None = None

    def __post_init__(self) -> None:
        if self.minimum < 1:
            raise ValueError("every operator takes at least one argument")
        if self.maximum is not None and self.maximum < self.minimum:
            raise ValueError("an arity maximum cannot be below its minimum")

    def accepts(self, count: int) -> bool:
        return count >= self.minimum and (
            self.maximum is None or count <= self.maximum
        )

    def describe(self) -> str:
        if self.maximum is None:
            return f"at least {self.minimum} arguments"
        if self.minimum == self.maximum:
            return f"exactly {self.minimum} arguments"
        return f"{self.minimum}..{self.maximum} arguments"


@dataclass(frozen=True, slots=True)
class BindingSignature:
    """A binding form: how many variables it introduces.

    The sorts of those variables are established by elaboration from the
    annotation syntax, not by this record.
    """

    name: str
    arity: int

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("a binding signature needs a name")
        if self.arity < 1:
            raise ValueError("a binding signature must introduce a variable")


DEFAULT_ARITIES: Mapping[StructuralHead, Arity] = MappingProxyType(
    {
        StructuralHead.PLUS: Arity(2),
        StructuralHead.TIMES: Arity(2),
        StructuralHead.POWER: Arity(2, 2),
        StructuralHead.EQ: Arity(2, 2),
        StructuralHead.NE: Arity(2, 2),
        StructuralHead.LT: Arity(2, 2),
        StructuralHead.LE: Arity(2, 2),
        StructuralHead.GT: Arity(2, 2),
        StructuralHead.GE: Arity(2, 2),
        StructuralHead.AND: Arity(2),
        StructuralHead.OR: Arity(2),
        StructuralHead.NOT: Arity(1, 1),
        StructuralHead.IMPLIES: Arity(2, 2),
        StructuralHead.GUARDED: Arity(2, 2),
        StructuralHead.PIECEWISE: Arity(2),
        StructuralHead.QUOTE: Arity(1, 1),
    }
)


@dataclass(frozen=True, slots=True, eq=False)
class LanguageSignature:
    """An assembled, read-only signature.

    It is a runtime object, not a value: `eq=False` makes that explicit, because
    comparing mappings structurally would compare proxies by identity.
    """

    heads: Mapping[SymbolId, StructuralHead]
    arities: Mapping[StructuralHead, Arity]
    binders: Mapping[str, BindingSignature]

    @classmethod
    def build(
        cls,
        heads: Mapping[SymbolId, StructuralHead],
        binders: Mapping[str, BindingSignature] | None = None,
    ) -> LanguageSignature:
        return cls(
            MappingProxyType(dict(heads)),
            MappingProxyType(dict(DEFAULT_ARITIES)),
            MappingProxyType(dict(binders or {})),
        )

    def head_of(self, symbol_id: SymbolId) -> StructuralHead | None:
        return self.heads.get(symbol_id)

    def arity_of(self, head: StructuralHead) -> Arity:
        return self.arities[head]

    def binder_of(self, name: str) -> BindingSignature | None:
        return self.binders.get(name)


__all__ = [
    "Arity",
    "BindingSignature",
    "DEFAULT_ARITIES",
    "LanguageSignature",
    "StructuralHead",
]
