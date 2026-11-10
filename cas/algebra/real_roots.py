"""Exact Sturm counting and open-interval isolation of real roots.

This module owns the *search* side of the R0 real-algebra slice: it builds the
Sturm chain of a univariate polynomial over an ordered characteristic-zero
field, counts the distinct real roots in an open interval, and isolates all
distinct real roots into disjoint open rational intervals.  The isolation
result is a finite set of witnesses, not real algebraic numbers: root objects,
multiplicity output and `RootOf` are later R1 capabilities.

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
corresponding reference implementation.  Root isolation uses the Cauchy root
bound (Cauchy, *Exercices de mathématiques*, 1829) and repeated exact
bisection; the bound and the Sturm count together certify that every real root
lies in exactly one open output interval.  This module does not build `RootOf`
or any real algebraic number.

Termination and budget
----------------------

The polynomial has finitely many roots and is squarefree.  Each bisection
strictly reduces the width of every remaining multi-root interval, so distinct
roots are eventually separated.  A root-valued midpoint is never used as a
split point: the search probes deterministic dyadic offsets around the
midpoint until it finds a non-root.  `budget` counts split and probe steps and
is resource control only; exhaustion raises `RealRootBudgetError` instead of
returning a partial set as if it were complete.
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


class RealRootBudgetError(RuntimeError):
    """The isolation budget was exhausted before a complete answer existed.

    This is a resource boundary, not a mathematical statement: no partial set
    of intervals may be published as the complete isolation.  `missing` names
    the resource the caller must enlarge to obtain an answer.
    """

    def __init__(
        self,
        detail: str,
        *,
        missing: frozenset[str] = frozenset({"root_isolation_budget"}),
    ) -> None:
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


def _require_ordered(
    ring: UnivariatePolynomialRing[E], operation: str
) -> Ordered[E]:
    coefficients = ring.coefficients
    if not isinstance(coefficients, Ordered):
        raise RealRootFragmentError(
            f"{operation} needs an ordered coefficient field",
            missing=frozenset({"ordered_coefficient_field"}),
        )
    return coefficients


def _absolute(coefficients: Ordered[E], value: E) -> E:
    return value if coefficients.sign(value) >= 0 else coefficients.neg(value)


def cauchy_bound(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
) -> E:
    """Cauchy's strict rational root bound of a nonzero polynomial.

    For ``p = a_n x^n + ... + a_0`` with ``a_n != 0`` the returned bound is

        ``1 + max_{i < n} |a_i / a_n|``.

    Every real root ``r`` satisfies ``|r| < bound``.  A nonzero constant has
    the bound ``1``; there is no root to bound.  The coefficient structure must
    be an ordered field of characteristic zero.  The zero polynomial is refused
    because every real number is a root.
    """
    _require_characteristic_zero(ring, "the Cauchy root bound")
    ordered = _require_ordered(ring, "the Cauchy root bound")
    coefficients = ring.coefficients
    if value.is_zero():
        raise RealRootFragmentError(
            "the zero polynomial has every real number as a root",
            missing=frozenset({"nonzero_polynomial"}),
        )
    if ring.is_constant(value):
        return coefficients.one()
    degree = ring.degree(value, 0)
    leading = ring.coefficient(value, (degree,))
    maximum = coefficients.zero()
    for exponent in range(degree):
        ratio = coefficients.div(
            ring.coefficient(value, (exponent,)), leading
        )
        magnitude = _absolute(ordered, ratio)
        if ordered.sign(ordered.sub(magnitude, maximum)) > 0:
            maximum = magnitude
    return coefficients.add(coefficients.one(), maximum)


def _count_from_chain(
    ring: UnivariatePolynomialRing[E],
    chain: tuple[Polynomial[E], ...],
    value: Polynomial[E],
    lower: E,
    upper: E,
) -> int:
    """The open-interval count using an already built Sturm chain."""
    coefficients = _require_ordered(ring, "root counting")
    lower_variations = sign_variations(ring, chain, lower)
    upper_variations = sign_variations(ring, chain, upper)
    upper_root = 1 if coefficients.is_zero(evaluate(ring, value, upper)) else 0
    return lower_variations - upper_variations - upper_root


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
    coefficients = _require_ordered(ring, "root counting")
    if not coefficients.less(lower, upper):
        raise RealRootFragmentError(
            "a root-count interval needs lower < upper",
            missing=frozenset({"ordered_endpoints"}),
        )
    chain = sturm_chain(ring, value)
    return _count_from_chain(ring, chain, value, lower, upper)


def _nonroot_split(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
    lower: E,
    upper: E,
    budget: int,
    spent: int,
) -> tuple[E, int]:
    """A non-root split point strictly inside ``(lower, upper)``.

    The midpoint is tried first.  If it is a root, deterministic dyadic offsets
    around it are probed; the polynomial has finitely many roots, so a non-root
    is found whenever the budget permits.  Both child intervals retain at least
    one quarter of the parent width, which keeps the bisection progressing.
    """
    _require_ordered(ring, "root isolation")
    coefficients = ring.coefficients
    two = coefficients.add(coefficients.one(), coefficients.one())
    width = coefficients.sub(upper, lower)
    middle = coefficients.add(lower, coefficients.div(width, two))
    if not coefficients.is_zero(evaluate(ring, value, middle)):
        return middle, spent
    four = coefficients.mul_int(coefficients.one(), 4)
    offset = coefficients.div(width, four)
    positive = True
    while True:
        if spent >= budget:
            raise RealRootBudgetError(
                "the root-isolation budget was exhausted while avoiding a "
                "root-valued split point",
                missing=frozenset({"root_isolation_budget"}),
            )
        spent += 1
        candidate = (
            coefficients.add(middle, offset)
            if positive
            else coefficients.sub(middle, offset)
        )
        if not coefficients.is_zero(evaluate(ring, value, candidate)):
            return candidate, spent
        if positive:
            positive = False
        else:
            positive = True
            offset = coefficients.div(offset, two)


def isolate_real_roots_open(
    ring: UnivariatePolynomialRing[E],
    value: Polynomial[E],
    *,
    budget: int,
) -> tuple[tuple[E, E], ...]:
    """Isolate every distinct real root in a disjoint open rational interval.

    Preconditions: ``value`` is a nonzero squarefree polynomial over an ordered
    characteristic-zero field, and ``budget`` is a nonnegative integer count of
    split/probe steps.  The search radius is strictly larger than Cauchy's
    bound, so every real root lies inside it and neither outer endpoint is a
    root.  Intervals are returned in increasing order, have non-root endpoints,
    and each has exactly one distinct root.  Open intervals may share a
    non-root endpoint; their interiors are disjoint.

    A budget refusal raises `RealRootBudgetError`; no partial tuple is
    returned.  The zero polynomial and a non-squarefree polynomial raise
    `RealRootFragmentError` exactly as `sturm_chain` does.
    """
    if isinstance(budget, bool) or not isinstance(budget, int):
        raise TypeError("a root-isolation budget must be an integer")
    if budget < 0:
        raise ValueError("a root-isolation budget cannot be negative")
    _require_characteristic_zero(ring, "root isolation")
    coefficients = _require_ordered(ring, "root isolation")
    chain = sturm_chain(ring, value)
    radius = coefficients.add(cauchy_bound(ring, value), coefficients.one())
    lower = coefficients.neg(radius)
    total = _count_from_chain(ring, chain, value, lower, radius)
    if total == 0:
        return ()
    stack: list[tuple[E, E, int]] = [(lower, radius, total)]
    intervals: list[tuple[E, E]] = []
    spent = 0
    while stack:
        current_lower, current_upper, count = stack.pop()
        if count == 0:
            continue
        if count == 1:
            intervals.append((current_lower, current_upper))
            continue
        if spent >= budget:
            raise RealRootBudgetError(
                "the root-isolation budget was exhausted before every root "
                "was separated",
                missing=frozenset({"root_isolation_budget"}),
            )
        spent += 1
        split, spent = _nonroot_split(
            ring,
            value,
            current_lower,
            current_upper,
            budget,
            spent,
        )
        left_count = _count_from_chain(
            ring, chain, value, current_lower, split
        )
        right_count = _count_from_chain(ring, chain, value, split, current_upper)
        stack.append((split, current_upper, right_count))
        stack.append((current_lower, split, left_count))
    return tuple(intervals)


__all__ = [
    "RealRootBudgetError",
    "RealRootFragmentError",
    "cauchy_bound",
    "count_real_roots_open",
    "evaluate",
    "isolate_real_roots_open",
    "sign_at",
    "sign_variations",
    "sturm_chain",
]
