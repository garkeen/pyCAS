"""Injected computation services.

The workflow asks for a candidate; it does not know whether the candidate came
from a polynomial ring or from a symbolic term fragment. The service reports
only a candidate, an honest refusal, or an internal invalid result. Verification
stays with the registered checker.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.syntax import term as T


class DerivationOutcome:
    __slots__ = ()


@dataclass(frozen=True, slots=True)
class Derived(DerivationOutcome):
    """A candidate and the region on which its derivative relation is stated.

    `condition` is None for the whole domain. `defined` is the region where the
    source is defined; it lets a constant composition use definedness rather
    than differentiability of an inner function. `evidence` is opaque
    derivation data for the registered checker; semantics never interprets it.
    """

    term: T.Term
    condition: T.Term | None = None
    defined: T.Term | None = None
    evidence: object | None = None


@dataclass(frozen=True, slots=True)
class DerivationUnsupported(DerivationOutcome):
    """The input is outside the implemented fragment."""

    reason: Reason
    detail: str


@dataclass(frozen=True, slots=True)
class DerivationInvalid(DerivationOutcome):
    """The candidate cannot be represented; this is an internal inconsistency."""

    detail: str


class DerivativeService(Protocol):
    """Candidate generation and certificate construction for one fragment."""

    @property
    def checker_id(self) -> str:
        """The registered checker that verifies this service's certificates."""

    @property
    def specification_kind(self) -> str:
        """The admitted specification family this service proposes."""

    def candidate(self, term: T.Term) -> DerivationOutcome:
        """Produce a candidate, or refuse honestly."""

    def certificate(
        self,
        region: T.Term,
        source: T.Term,
        variable: SymbolId,
        derivation: Derived,
    ) -> object:
        """Build the certificate the registered checker expects."""


__all__ = [
    "DerivationInvalid",
    "DerivationOutcome",
    "DerivationUnsupported",
    "DerivativeService",
    "Derived",
]
