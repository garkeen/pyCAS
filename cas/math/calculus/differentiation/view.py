"""Request-local algebra views for differentiation.

A runtime freezes the structures it can use, but the target of a request is not
a property of the runtime.  One view fixes the coefficient structure, the
parameter structure, the target generator, the bridge, the derivation and the
checker for one target.  An operation selects the view named by the request;
it never mutates a global variable or reinterprets an old view.

The request is the single authority for the chosen derivation: a view accepts
only the exact `DifferentialStructure` object carried by its request, so a view
cannot silently introduce a second derivation choice.  A request without a
differential cannot back a differentiation or specialization view.

This module also keeps the concrete polynomial view used to specialise a
parameter family.  Both records are immutable: changing the target is a new
request over another pre-assembled view, not an edit of an existing one.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Generic, TypeVar

from cas.algebra.parents import Parent
from cas.algebra.polynomial import Polynomial, PolynomialRing, UnivariatePolynomialRing
from cas.foundation.ids import SymbolId
from cas.kernel.evidence import Checker
from cas.math.calculus.differentiation.checker import DerivativeChecker
from cas.semantics.bridge import PolynomialBridge, SimplePolynomialBridge
from cas.semantics.differential import DifferentialStructure
from cas.semantics.request import AlgebraRequest
from cas.semantics.services import DerivativeService

E = TypeVar("E")


def _require_request_differential(
    request: AlgebraRequest,
    differential: DifferentialStructure[Any],
) -> None:
    """Reject a view that does not carry the request's exact derivation.

    Identity, not structural equality, is the check: two equal-looking
    `DifferentialStructure` values are still two derivation choices, and the
    request must remain the only authority for the one this view uses.
    """
    request_differential = request.differential
    if request_differential is None:
        raise ValueError(
            "a differentiation or specialization view needs a request with "
            "a differential structure; the request is the single derivation "
            "authority"
        )
    if differential is not request_differential:
        raise ValueError(
            "the view differential is not the request's differential "
            "structure; the request is the single derivation authority"
        )


@dataclass(frozen=True, slots=True, eq=False)
class DifferentiationView(Generic[E]):
    """One target role with every structure needed to differentiate it."""

    request: AlgebraRequest
    ring: PolynomialRing[E]
    parent: Parent[Polynomial[E]]
    differential: DifferentialStructure[Polynomial[E]]
    bridge: PolynomialBridge[E]
    service: DerivativeService
    checker: Checker

    def __post_init__(self) -> None:
        _require_request_differential(self.request, self.differential)

    @property
    def target(self) -> SymbolId:
        """The target symbol this view fixes."""
        return self.request.target


@dataclass(frozen=True, slots=True, eq=False)
class SpecializationView:
    """A concrete Q[x] view with its own derivation, bridge and checker."""

    ring: UnivariatePolynomialRing[Fraction]
    parent: Parent[Polynomial[Fraction]]
    differential: DifferentialStructure[Polynomial[Fraction]]
    bridge: SimplePolynomialBridge[Fraction]
    checker: DerivativeChecker[Fraction]
    request: AlgebraRequest

    def __post_init__(self) -> None:
        _require_request_differential(self.request, self.differential)


__all__ = ["DifferentiationView", "SpecializationView"]
