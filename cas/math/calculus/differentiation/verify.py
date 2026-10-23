"""Independent verification of a polynomial derivative.

This is a second implementation of the formal derivative rule: it walks the
source's terms, accumulates the expected coefficients, and compares them with
the candidate's terms directly. It never calls `PolynomialRing.derivative`, so a
defect in that routine cannot certify itself.

The rule is the same mathematics, encoded twice; independence here means two
code paths agree, not two different theorems.
"""

from __future__ import annotations

from typing import TypeVar

from cas.algebra.polynomial import Exponents, Polynomial, PolynomialRing

E = TypeVar("E")


def verify_derivative(
    ring: PolynomialRing[E],
    source: Polynomial[E],
    candidate: Polynomial[E],
    index: int,
) -> bool:
    """Whether `candidate` is the formal derivative of `source` in `index`."""
    if not ring.contains(source) or not ring.contains(candidate):
        raise ValueError("a polynomial belongs to another ring")
    coefficients = ring.coefficients
    expected: dict[Exponents, E] = {}
    for exponents, coefficient in source.terms:
        power = exponents[index]
        if power == 0:
            continue
        lowered = tuple(
            exponent - (1 if position == index else 0)
            for position, exponent in enumerate(exponents)
        )
        expected[lowered] = coefficients.add(
            expected.get(lowered, coefficients.zero()),
            coefficients.mul_int(coefficient, power),
        )
    actual = dict(candidate.terms)
    for key in set(expected) | set(actual):
        if not coefficients.equal(
            expected.get(key, coefficients.zero()),
            actual.get(key, coefficients.zero()),
        ):
            return False
    return True


__all__ = ["verify_derivative"]
