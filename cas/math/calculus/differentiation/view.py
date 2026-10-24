"""The concrete polynomial view used to specialise a parameter family."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from cas.algebra.parents import Parent
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.math.calculus.differentiation.checker import DerivativeChecker
from cas.semantics.bridge import SimplePolynomialBridge
from cas.semantics.differential import DifferentialStructure
from cas.semantics.request import AlgebraRequest


@dataclass(frozen=True, slots=True, eq=False)
class SpecializationView:
    """A concrete Q[x] view with its own derivation, bridge and checker."""

    ring: UnivariatePolynomialRing[Fraction]
    parent: Parent[Polynomial[Fraction]]
    differential: DifferentialStructure[Polynomial[Fraction]]
    bridge: SimplePolynomialBridge[Fraction]
    checker: DerivativeChecker[Fraction]
    request: AlgebraRequest


__all__ = ["SpecializationView"]
