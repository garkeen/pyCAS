"""Independent verification of a supplied Sturm chain and its root counts.

This module is checker-side.  It never imports the root search module and never
rebuilds a second chain from the polynomial: it checks the certificate chain
link by link with exact ring division.  Both the root-count checker and the
root-isolation checker consume the same closed outcome and the same
open-interval counting formula, so the two verifiers cannot drift apart.

The chain is

    p0 = p,  p1 = p',  p_{i+1} = -rem(p_{i-1}, p_i)

and a valid certificate ends at a nonzero constant.  A complete Euclidean
chain whose last entry is a nonconstant gcd proves that the polynomial is not
squarefree; that is a fragment boundary, not a malformed certificate.  A
missing, extra, zero or recurrence-breaking entry is malformed evidence.

References
----------
Sturm's theorem: J. C. F. Sturm, *Mémoire sur la résolution des équations
numériques*, 1829.  Textbook treatment and the open-interval endpoint
convention: Basu, Pollack and Roy, *Algorithms in Real Algebraic Geometry*,
2nd ed., Chapter 2.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeVar

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.protocols import Ordered

E = TypeVar("E")


@dataclass(frozen=True, slots=True)
class ValidChain:
    """The certificate chain satisfies the Sturm recurrence and is squarefree."""


@dataclass(frozen=True, slots=True)
class ChainMismatch:
    """The supplied chain is malformed, missing, extra or not this polynomial's."""

    detail: str

    def __post_init__(self) -> None:
        if not self.detail:
            raise ValueError("a chain mismatch needs a detail")


@dataclass(frozen=True, slots=True)
class ChainFragmentGap:
    """The chain is complete but proves a precondition outside the fragment.

    The current gap is a nonconstant terminal gcd, which witnesses a repeated
    factor.  The caller reports `Unverified(FRAGMENT)` with `missing`; it must
    not turn the boundary into a mathematical refutation.
    """

    detail: str
    missing: frozenset[str]

    def __post_init__(self) -> None:
        if not self.detail:
            raise ValueError("a chain fragment gap needs a detail")
        missing = frozenset(self.missing)
        if not missing:
            raise ValueError("a chain fragment gap needs a missing set")
        object.__setattr__(self, "missing", missing)


SturmChainVerification = ValidChain | ChainMismatch | ChainFragmentGap


def verify_sturm_chain(
    ring: UnivariatePolynomialRing[E],
    polynomial: Polynomial[E],
    chain: tuple[Polynomial[E], ...],
) -> SturmChainVerification:
    """Verify a supplied Sturm chain without rebuilding it.

    Every non-final entry must be nonzero so the next division is defined.  The
    last entry of a valid chain is a nonzero constant.  If the Euclidean
    recurrence terminates at a nonconstant entry, the chain is complete and
    shows a nonconstant gcd; this is reported as a fragment gap.
    """
    if not chain:
        return ChainMismatch("the certificate Sturm chain is empty")
    if any(entry.is_zero() for entry in chain):
        return ChainMismatch("the Sturm chain contains a zero entry")
    if not ring.equal(chain[0], polynomial):
        return ChainMismatch("the first Sturm-chain entry is not the polynomial")
    if ring.is_constant(polynomial):
        if len(chain) != 1:
            return ChainMismatch(
                "a constant polynomial needs a one-entry Sturm chain"
            )
        return ValidChain()
    if len(chain) < 2:
        return ChainMismatch("the Sturm chain is missing the derivative entry")
    if not ring.equal(chain[1], ring.derivative(polynomial, 0)):
        return ChainMismatch(
            "the second Sturm-chain entry is not the derivative"
        )
    for index in range(len(chain) - 2):
        _, remainder = ring.divmod(chain[index], chain[index + 1])
        if remainder.is_zero():
            return ChainMismatch(
                "the Sturm chain reaches a zero remainder before its last "
                "entry"
            )
        if not ring.equal(chain[index + 2], ring.neg(remainder)):
            return ChainMismatch(
                "the certificate chain does not satisfy the Sturm recurrence"
            )
    if ring.is_constant(chain[-1]):
        return ValidChain()
    _, remainder = ring.divmod(chain[-2], chain[-1])
    if remainder.is_zero():
        return ChainFragmentGap(
            "the Sturm chain ends at a nonconstant gcd, so the polynomial is "
            "not squarefree",
            frozenset({"squarefree_polynomial"}),
        )
    return ChainMismatch("the Sturm chain does not end at a constant")


def _evaluate(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
    point: E,
) -> E:
    coefficients = ring.coefficients
    result = coefficients.zero()
    if value.is_zero():
        return result
    for exponent in range(ring.degree(value, 0), -1, -1):
        result = coefficients.add(
            coefficients.mul(result, point),
            ring.coefficient(value, (exponent,)),
        )
    return result


def _sign_variations(
    ring: UnivariatePolynomialRing[E],
    coefficients: Ordered[E],
    chain: tuple[Polynomial[E], ...],
    point: E,
) -> int:
    variations = 0
    previous = 0
    for value in chain:
        sign = coefficients.sign(_evaluate(ring, value, point))
        if sign == 0:
            continue
        if previous != 0 and sign != previous:
            variations += 1
        previous = sign
    return variations


def open_interval_count(
    ring: UnivariatePolynomialRing[E],
    polynomial: Polynomial[E],
    chain: tuple[Polynomial[E], ...],
    lower: E,
    upper: E,
) -> int:
    """The Sturm count in ``(lower, upper)`` from an already verified chain.

    The formula is ``V(lower) - V(upper) - [p(upper) = 0]``.  The last term
    fixes the endpoint convention: ``V`` at a simple root agrees with its
    right-hand limit, so the difference counts ``(lower, upper]`` and removes a
    root at the upper endpoint; a root at the lower endpoint is already
    excluded by the right-hand value.  The coefficient field must be ordered.
    """
    coefficients = ring.coefficients
    if not isinstance(coefficients, Ordered):
        raise TypeError(
            "open-interval counting needs an ordered coefficient field"
        )
    lower_variations = _sign_variations(ring, coefficients, chain, lower)
    upper_variations = _sign_variations(ring, coefficients, chain, upper)
    upper_root = 1 if coefficients.is_zero(
        _evaluate(ring, polynomial, upper)
    ) else 0
    return lower_variations - upper_variations - upper_root


__all__ = [
    "ChainFragmentGap",
    "ChainMismatch",
    "SturmChainVerification",
    "ValidChain",
    "open_interval_count",
    "verify_sturm_chain",
]
