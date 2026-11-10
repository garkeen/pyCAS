"""Exact Sturm counting of distinct real roots of a squarefree polynomial.

This module owns the *search* side of the first R0 slice: it builds the Sturm
chain of a univariate polynomial over an ordered characteristic-zero field and
counts the distinct real roots in an open interval.  Root isolation, interval
objects, multiplicity output and real algebraic numbers are deliberately not
part of this file; they are later R0/R1 capabilities.

Sturm's theorem
---------------

Let ``K`` be an ordered field of characteristic zero and let ``p`` in ``K[x]``
be nonzero and squarefree.  Define the chain

    p0 = p,  p1 = p',  p_{i+1} = -rem(p_{i-1}, p_i)

until the remainder sequence reaches a nonzero constant.  For ``a < b`` let
``V(x)`` be the number of sign changes in the sequence ``p0(x), p1(x), ...``
with zero entries omitted.  Then the number of distinct roots of ``p`` in the
open interval ``(a, b)`` is

    V(a) - V(b) - [p(b) = 0].

The last term is the endpoint convention: ``V`` at a simple root agrees with
the right-hand limit, so ``V(a) - V(b)`` counts roots in ``(a, b]`` and the
root at ``b`` is removed.  A root at ``a`` is already excluded by the right-hand
value ``V(a)``.  The convention is fixed here, not re-invented by consumers.

Preconditions and termination
-----------------------------

The coefficient structure must be a field of characteristic zero and must
expose a total order through ``Ordered.sign``.  The polynomial must be nonzero
and squarefree; for a nonconstant polynomial this is exactly the condition that
the Euclidean remainder chain ends in a nonzero constant.  The chain terminates
because every remainder after the first has strictly smaller degree; no
heuristic stopping rule is used.  Constant nonzero polynomials produce the
one-entry chain ``(p,)`` and count zero roots.  The zero polynomial is refused
because every real number is a root.

References
----------

Sturm's theorem: J. C. F. Sturm, *Mémoire sur la résolution des équations
numériques*, 1829.  Textbook treatment and endpoint conventions: Basu, Pollack
and Roy, *Algorithms in Real Algebraic Geometry*, 2nd ed., Chapter 2.  The
remainder recurrence is the classical Euclidean Sturm sequence; the polynomial
ring provides the required exact ``divmod`` and ``derivative``.  Maxima's
``src/polyrz.lisp:29-111`` (``sturmseq``/``sturm1``/``sturm``) is the
corresponding reference implementation.  This module only counts roots; it
does not isolate them and does not build `RootOf`.
"""

from __future__ import annotations

from typing import TypeVar

from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.protocols import Ordered

E = TypeVar("E")


class RealRootFragmentError(ValueError):
    """A real-root request is outside this module's declared fragment.

    ``missing`` is the structured capability set the caller turns into a
    fragment report.  The error is never a mathematical refutation: an
    unproved precondition is a boundary of this algorithm, not evidence that a
    claimed count is false.
    """

    def __init__(self, detail: str, *, missing: frozenset[str]) -> None:
        super().__init__(detail)
        self.detail = detail
        self.missing = frozenset(missing)


def _require_characteristic_zero(
    ring: UnivariatePolynomialRing[E], operation: str
) -> None:
    if ring.coefficients.characteristic != 0:
        raise RealRootFragmentError(
            f"{operation} needs a characteristic-zero coefficient field",
            missing=frozenset({"characteristic_zero_field"}),
        )


def evaluate(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
    point: E,
) -> E:
    """Evaluate ``value`` at ``point`` by exact Horner accumulation.

    The ring's coefficient operations are the only arithmetic used; no
    floating-point sampling and no approximate sign decision is involved.
    """
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


def sign_at(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
    point: E,
) -> int:
    """The sign of ``value`` at ``point`` in the ordered coefficient field."""
    coefficients = ring.coefficients
    if not isinstance(coefficients, Ordered):
        raise RealRootFragmentError(
            "a polynomial sign needs an ordered coefficient field",
            missing=frozenset({"ordered_coefficient_field"}),
        )
    return coefficients.sign(evaluate(ring, value, point))


def sturm_chain(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
) -> tuple[Polynomial[E], ...]:
    """The Sturm chain of a nonzero squarefree polynomial.

    The chain is ``value, value', -rem(value, value'), ...`` and ends at a
    nonzero constant.  It is refused when the polynomial is zero or when the
    remainder chain ends at a nonconstant gcd, which is precisely the
    non-squarefree case for a characteristic-zero field.  A nonzero constant
    input has the one-entry chain ``(value,)``: it has no roots and no
    derivative step that would divide by zero.
    """
    _require_characteristic_zero(ring, "the Sturm chain")
    if value.is_zero():
        raise RealRootFragmentError(
            "the zero polynomial has every real number as a root",
            missing=frozenset({"nonzero_polynomial"}),
        )
    if ring.is_constant(value):
        return (value,)
    chain: list[Polynomial[E]] = [
        value,
        ring.derivative(value, 0),
    ]
    while not ring.is_constant(chain[-1]):
        _, remainder = ring.divmod(chain[-2], chain[-1])
        following = ring.neg(remainder)
        if following.is_zero():
            break
        chain.append(following)
    if not ring.is_constant(chain[-1]):
        raise RealRootFragmentError(
            "the Sturm chain ends at a nonconstant gcd, so the polynomial is "
            "not squarefree",
            missing=frozenset({"squarefree_polynomial"}),
        )
    return tuple(chain)


def sign_variations(
    ring: UnivariatePolynomialRing[E],
    chain: tuple[Polynomial[E], ...],
    point: E,
) -> int:
    """The number of sign changes of ``chain`` at ``point``, zeros skipped."""
    coefficients = ring.coefficients
    if not isinstance(coefficients, Ordered):
        raise RealRootFragmentError(
            "sign variations need an ordered coefficient field",
            missing=frozenset({"ordered_coefficient_field"}),
        )
    variations = 0
    previous = 0
    for value in chain:
        sign = coefficients.sign(evaluate(ring, value, point))
        if sign == 0:
            continue
        if previous != 0 and sign != previous:
            variations += 1
        previous = sign
    return variations


def count_real_roots_open(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
    lower: E,
    upper: E,
) -> int:
    """Count distinct real roots in the open interval ``(lower, upper)``.

    The polynomial must be nonzero and squarefree, the endpoints must be field
    elements with ``lower < upper``, and the coefficient field must be ordered
    and of characteristic zero.  The returned count is ``V(lower) - V(upper)``
    minus one when ``upper`` is a root; see the module docstring for the
    endpoint convention.
    """
    coefficients = ring.coefficients
    if not isinstance(coefficients, Ordered):
        raise RealRootFragmentError(
            "root counting needs an ordered coefficient field",
            missing=frozenset({"ordered_coefficient_field"}),
        )
    if not coefficients.less(lower, upper):
        raise RealRootFragmentError(
            "a root-count interval needs lower < upper",
            missing=frozenset({"ordered_endpoints"}),
        )
    chain = sturm_chain(ring, value)
    lower_variations = sign_variations(ring, chain, lower)
    upper_variations = sign_variations(ring, chain, upper)
    upper_root = 1 if coefficients.is_zero(evaluate(ring, value, upper)) else 0
    return lower_variations - upper_variations - upper_root


__all__ = [
    "RealRootFragmentError",
    "count_real_roots_open",
    "evaluate",
    "sign_at",
    "sign_variations",
    "sturm_chain",
]
