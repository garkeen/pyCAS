"""Injected computation services.

The workflow asks for a candidate; it does not know whether the candidate came
from a polynomial ring or from a symbolic term fragment. The service reports
only a candidate, an honest refusal, or an internal invalid result. Verification
stays with the registered checker.

A service consumes the typed source and the algebra request the operation fixed
for it.  It never re-reads a bare term: the bridge decides whether the source is
inside the service's effective algebra representation, and the refusal carries
the same missing capabilities and open conditions as `ViewRefused`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, TypeAlias

from cas.foundation.ids import SymbolId
from cas.language.decisions import Reason
from cas.language.propositions import Proposition
from cas.language.typing import TypedExpr
from cas.semantics.request import AlgebraRequest
from cas.syntax import term as T


@dataclass(frozen=True, slots=True)
class Derived:
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
class DerivationUnsupported:
    """The input is outside the implemented fragment.

    `missing` names the capabilities the service lacks and `conditions` are the
    obligations that prevent a candidate.  This is a fragment or condition
    refusal, never a mathematical refutation.
    """

    reason: Reason
    detail: str
    missing: frozenset[str] = frozenset()
    conditions: tuple[Proposition, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.reason, Reason):
            raise TypeError("a derivation refusal needs a Reason")
        if not isinstance(self.detail, str):
            raise TypeError("a derivation refusal detail must be a string")
        if not self.detail:
            raise ValueError("a derivation refusal needs a detail")
        missing = frozenset(self.missing)
        if any(not isinstance(item, str) or not item for item in missing):
            raise TypeError(
                "derivation-refusal capabilities must be non-empty strings"
            )
        conditions = tuple(self.conditions)
        if any(not isinstance(item, Proposition) for item in conditions):
            raise TypeError("derivation-refusal conditions must be propositions")
        object.__setattr__(self, "missing", missing)
        object.__setattr__(self, "conditions", conditions)


@dataclass(frozen=True, slots=True)
class DerivationInvalid:
    """The candidate cannot be represented; this is an internal inconsistency."""

    detail: str


DerivationOutcome: TypeAlias = Derived | DerivationUnsupported | DerivationInvalid


class DerivativeService(Protocol):
    """Candidate generation and certificate construction for one fragment."""

    @property
    def checker_id(self) -> str:
        """The registered checker that verifies this service's certificates."""

    @property
    def specification_kind(self) -> str:
        """The admitted specification family this service proposes."""

    def supports(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> DerivationUnsupported | None:
        """Whether `source` is inside this service's declared input fragment."""

    def candidate(
        self, source: TypedExpr, request: AlgebraRequest
    ) -> DerivationOutcome:
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
