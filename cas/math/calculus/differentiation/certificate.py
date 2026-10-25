"""The certificate data shared by derivative checkers.

The record names the exact instance a caller asks to verify. The polynomial
checker verifies it by its own coefficient-level rule. The elementary checker
additionally requires a `Derivation` tree: each node names one local rule
instance, so the checker verifies the rule applications instead of re-running a
second recursive search.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from cas.foundation.ids import SymbolId
from cas.syntax import term as T


class Rule(StrEnum):
    """One local derivative rule instance."""

    LITERAL = "literal"
    VARIABLE = "variable"
    CONSTANT = "constant"
    SUM = "sum"
    PRODUCT = "product"
    POWER = "power"
    FUNCTION = "function"


@dataclass(frozen=True, slots=True)
class Derivation:
    """One rule instance with its children and the conditions it carries."""

    rule: Rule
    source: T.Term
    result: T.Term
    condition: T.Term | None = None
    defined: T.Term | None = None
    children: tuple["Derivation", ...] = ()


@dataclass(frozen=True, slots=True)
class DerivativeCertificate:
    """The exact derivative instance the caller asks to verify."""

    region: T.Term
    source: T.Term
    variable: SymbolId
    candidate: T.Term
    derivation: Derivation | None = None


__all__ = ["Derivation", "DerivativeCertificate", "Rule"]
