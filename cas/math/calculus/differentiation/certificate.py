"""The certificate data shared by derivative checkers.

The record names the exact instance a caller asks to verify. Both the
polynomial checker and the declared-elementary checker interpret this schema;
they differ in the independent verification procedure, not in the certificate
format.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.foundation.ids import SymbolId
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class DerivativeCertificate:
    """The exact derivative instance the caller asks to verify."""

    region: T.Term
    source: T.Term
    variable: SymbolId
    candidate: T.Term


__all__ = ["DerivativeCertificate"]
