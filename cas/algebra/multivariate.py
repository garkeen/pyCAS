"""Exact multivariate division, leading terms and S-polynomials over a field.

This module owns the primitives shared by the Groebner search and by the
independent checker that verifies a candidate basis.  The search itself, the
sealed reduced-basis record and the ideal queries live in
``cas.algebra.groebner``: a checker may import division, leading-term and
S-polynomial helpers from here without importing the Buchberger search module,
which is the separation ``cas_v5_arch.md`` §22.6 and §13.10 require.  Neither
module publishes a judgment; both are low-level algebra.

Scope boundary
--------------

The generator-mode request and view foundation, the `HasGroebnerBasis` claim,
the independent checker and the registered `groebner_basis` operation are
implemented in the language, semantics, math and runtime layers.  This module
remains a pure low-level algebra API; it never publishes a judgment and does
not assemble a problem or operation.

Representation and monomial order
---------------------------------

``PolynomialRing`` stores sparse exponent tuples in the ring's declared
``MonomialOrder`` (LEX, GRLEX or GREVLEX).  Terms are stored in ascending
order, so the leading term is the last stored term.  Every function here uses
``ring.monomial_order``; no function chooses a second order.  The leading
helpers refuse the zero polynomial because it has no leading term.

Multivariate division
---------------------

For a polynomial ``f`` and divisors ``d_1, ..., d_s`` over a field, the
standard division algorithm repeatedly removes the leading term of the current
remainder by the first divisor whose leading monomial divides it; when no
divisor applies, that leading term is moved to the remainder.  It returns
quotients ``q_i`` and a remainder ``r`` with

    f = sum_i q_i * d_i + r

and no monomial of ``r`` divisible by any leading monomial of a divisor.  Each
reduction strictly lowers the leading monomial under the fixed well-order, so
the algorithm terminates after finitely many steps.

When the divisors form a Groebner basis, ``r`` is the unique ideal normal form.
For an arbitrary divisor list, ``r`` is only a division remainder: it can
depend on the order of the divisors and is not an ideal normal form.  The
function name ``normal_form`` follows the standard terminology for a Groebner
basis; callers with an arbitrary divisor list must read the result as a
division remainder, not as a canonical form.

S-polynomials
-------------

With ``L = lcm(LM(left), LM(right))``, the S-polynomial of two nonzero
polynomials is

    (L / LT(left)) * left - (L / LT(right)) * right.

``s_polynomial_parts`` also returns the two multipliers; the search-side
cofactor bookkeeping needs them, while a checker that only verifies the
S-polynomial vanishes can call ``s_polynomial``.  Leading coefficients are
inverted in the coefficient field; zero inputs are refused because they have
no leading monomial, and a zero result is valid (for example for nonzero
scalar multiples).

Budget accounting
-----------------

``_divide`` accepts an optional ``spend`` callback invoked once per
leading-term reduction.  The callback lets the Groebner search charge its own
resource budget without this module importing the search's budget exception.
The count is returned as well.  A budget never changes the mathematical truth
of a completed answer.

Preconditions and refusals
--------------------------

- The coefficient structure must implement ``Field[E]``.  The algorithms work
  over any field, including positive characteristic; no characteristic-zero or
  ordered-field precondition is imposed here.
- Every polynomial must belong to the supplied ring.  Mixed rings are rejected
  before any arithmetic.
- Zero divisors and zero S-polynomial arguments are refused explicitly; they
  have no leading monomial.
- The empty divisor list is allowed by division: it returns no quotients and
  leaves the input as the remainder.

References
----------

D. Cox, J. Little and D. O'Shea, *Ideals, Varieties, and Algorithms*, 4th ed.,
Chapter 2: §3 for the division algorithm, §6-7 for S-polynomials and
Buchberger's criterion.  Geddes, Czapor and Labahn, *Algorithms for Computer
Algebra*, Chapter 7, for the polynomial-algebra background.  Reference
implementations: FriCAS ``src/algebra/gbintern.spad`` (internal normal-form
reductions) and Maxima ``share/algebra/grob1.lisp``.  These implementations are
evidence for algorithm structure, not replacements for the proofs above.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable
from dataclasses import dataclass
from typing import Generic, TypeVar, cast

from cas.algebra.polynomial import (
    Exponents,
    Polynomial,
    PolynomialRing,
)
from cas.algebra.protocols import Field

E = TypeVar("E")

_FIELD_MISSING = frozenset({"coefficient_field"})
_NONZERO_POLYNOMIAL_MISSING = frozenset({"nonzero_polynomial"})
_NONZERO_DIVISOR_MISSING = frozenset({"nonzero_divisor"})


class GroebnerFragmentError(ValueError):
    """A request is outside this module's declared algebraic fragment.

    ``missing`` is the structured capability or precondition set the caller
    turns into a fragment report.  This error is never a mathematical
    refutation; it says that the low-level algorithm cannot apply its
    assumptions to the supplied data.
    """

    def __init__(
        self,
        detail: str,
        *,
        missing: frozenset[str],
    ) -> None:
        super().__init__(detail)
        self.detail = detail
        self.missing = frozenset(missing)


@dataclass(frozen=True, slots=True)
class MultivariateDivision(Generic[E]):
    """Quotients and remainder of one multivariate division.

    ``value == sum(quotient_i * divisor_i) + remainder``.
    """

    quotients: tuple[Polynomial[E], ...]
    remainder: Polynomial[E]


def leading_term(
    ring: PolynomialRing[E],
    polynomial: Polynomial[E],
) -> tuple[Exponents, E]:
    """The leading exponent tuple and coefficient under the ring's order."""
    _require_owned(ring, polynomial, "leading term")
    if polynomial.is_zero():
        raise GroebnerFragmentError(
            "a zero polynomial has no leading term",
            missing=_NONZERO_POLYNOMIAL_MISSING,
        )
    return polynomial.terms[-1]


def leading_monomial(
    ring: PolynomialRing[E],
    polynomial: Polynomial[E],
) -> Exponents:
    """The leading monomial (exponent tuple) under the ring's order."""
    return leading_term(ring, polynomial)[0]


def leading_coefficient(
    ring: PolynomialRing[E],
    polynomial: Polynomial[E],
) -> E:
    """The coefficient of the leading term under the ring's order."""
    return leading_term(ring, polynomial)[1]


def multivariate_divmod(
    ring: PolynomialRing[E],
    polynomial: Polynomial[E],
    divisors: Iterable[Polynomial[E]],
) -> MultivariateDivision[E]:
    """Divide ``polynomial`` by an ordered list of nonzero divisors.

    Return the quotient tuple and the division remainder.  The coefficient
    structure must be a field; zero divisors and elements from another ring are
    refused.  The empty divisor list is allowed and leaves the input as the
    remainder with an empty quotient tuple.

    If the divisors are not a Groebner basis, the remainder is not an ideal
    normal form and can depend on divisor order.  See ``normal_form``.
    """
    division, _ = _divide(ring, polynomial, tuple(divisors))
    return division


def normal_form(
    ring: PolynomialRing[E],
    polynomial: Polynomial[E],
    divisors: Iterable[Polynomial[E]],
) -> Polynomial[E]:
    """The division remainder of ``polynomial`` by ``divisors``.

    With a Groebner basis this is the unique ideal normal form.  With an
    arbitrary divisor list it is only the division remainder: it may depend on
    the order of the divisors and is not a canonical ideal normal form.  The
    name records the standard use; callers must not treat a non-Groebner
    remainder as an ideal membership decision.
    """
    return multivariate_divmod(ring, polynomial, divisors).remainder


def s_polynomial_parts(
    ring: PolynomialRing[E],
    left: Polynomial[E],
    right: Polynomial[E],
) -> tuple[Polynomial[E], Polynomial[E], Polynomial[E]]:
    """The S-polynomial and the two monomial multipliers that define it.

    With ``L = lcm(LM(left), LM(right))``, the parts are

        (value, L / LT(left), L / LT(right))

    where ``value`` is ``left_multiplier * left - right_multiplier * right``.
    The search side needs the multipliers to carry polynomial cofactors; a
    checker that only needs the S-polynomial calls ``s_polynomial``.  Leading
    coefficients are inverted in the coefficient field, so both inputs must be
    nonzero and belong to the supplied ring.
    """
    coefficients = _require_field(ring, "an S-polynomial")
    _require_owned(ring, left, "an S-polynomial")
    _require_owned(ring, right, "an S-polynomial")
    if left.is_zero() or right.is_zero():
        raise GroebnerFragmentError(
            "an S-polynomial needs nonzero inputs",
            missing=_NONZERO_POLYNOMIAL_MISSING,
        )
    left_exponents, left_coefficient = left.terms[-1]
    right_exponents, right_coefficient = right.terms[-1]
    common = _monomial_lcm(left_exponents, right_exponents)
    left_multiplier = ring.monomial(
        tuple(
            exponent - current
            for exponent, current in zip(common, left_exponents)
        ),
        coefficients.div(coefficients.one(), left_coefficient),
    )
    right_multiplier = ring.monomial(
        tuple(
            exponent - current
            for exponent, current in zip(common, right_exponents)
        ),
        coefficients.div(coefficients.one(), right_coefficient),
    )
    value = ring.sub(
        ring.mul(left_multiplier, left),
        ring.mul(right_multiplier, right),
    )
    return value, left_multiplier, right_multiplier


def s_polynomial(
    ring: PolynomialRing[E],
    left: Polynomial[E],
    right: Polynomial[E],
) -> Polynomial[E]:
    """The exact S-polynomial of two nonzero polynomials.

    With ``L = lcm(LM(left), LM(right))``, return

        (L / LT(left)) * left - (L / LT(right)) * right.

    Leading coefficients are inverted in the coefficient field.  Zero input
    polynomials are refused because they have no leading monomial; a zero
    result is valid (for example when the inputs are nonzero scalar
    multiples).
    """
    value, _, _ = s_polynomial_parts(ring, left, right)
    return value


def _require_field(
    ring: PolynomialRing[E],
    operation: str,
) -> Field[E]:
    coefficients = ring.coefficients
    if not isinstance(coefficients, Field):
        raise GroebnerFragmentError(
            f"{operation} needs a field of coefficients",
            missing=_FIELD_MISSING,
        )
    return cast("Field[E]", coefficients)


def _require_owned(
    ring: PolynomialRing[E],
    polynomial: Polynomial[E],
    operation: str,
) -> None:
    if not ring.contains(polynomial):
        raise ValueError(f"{operation}: a polynomial belongs to another ring")


def _monomial_divides(divisor: Exponents, dividend: Exponents) -> bool:
    return all(
        left <= right for left, right in zip(divisor, dividend)
    )


def _monomial_lcm(left: Exponents, right: Exponents) -> Exponents:
    return tuple(
        max(first, second) for first, second in zip(left, right)
    )


def _divide(
    ring: PolynomialRing[E],
    polynomial: Polynomial[E],
    divisors: tuple[Polynomial[E], ...],
    *,
    spend: Callable[[str], None] | None = None,
) -> tuple[MultivariateDivision[E], int]:
    """One division with quotients, the remainder and the reduction count.

    ``spend`` is the optional resource callback: it is invoked once per
    leading-term reduction with the phase name.  The search passes its budget's
    ``spend``; a checker passes nothing and gets the exact count for free.
    """
    coefficients = _require_field(ring, "multivariate division")
    _require_owned(ring, polynomial, "multivariate division")
    for divisor in divisors:
        _require_owned(ring, divisor, "multivariate division")
        if divisor.is_zero():
            raise GroebnerFragmentError(
                "a divisor must be nonzero",
                missing=_NONZERO_DIVISOR_MISSING,
            )

    zero = ring.zero()
    quotients = [zero for _ in divisors]
    remainder = zero
    current = polynomial
    reductions = 0
    while not current.is_zero():
        exponents, coefficient = current.terms[-1]
        for index, divisor in enumerate(divisors):
            divisor_exponents, divisor_coefficient = divisor.terms[-1]
            if not _monomial_divides(divisor_exponents, exponents):
                continue
            if spend is not None:
                spend("leading-term reduction")
            factor = ring.monomial(
                tuple(
                    first - second
                    for first, second in zip(exponents, divisor_exponents)
                ),
                coefficients.div(coefficient, divisor_coefficient),
            )
            quotients[index] = ring.add(quotients[index], factor)
            current = ring.sub(current, ring.mul(factor, divisor))
            reductions += 1
            break
        else:
            term = ring.monomial(exponents, coefficient)
            remainder = ring.add(remainder, term)
            current = ring.sub(current, term)
    return MultivariateDivision(tuple(quotients), remainder), reductions


__all__ = [
    "GroebnerFragmentError",
    "MultivariateDivision",
    "leading_coefficient",
    "leading_monomial",
    "leading_term",
    "multivariate_divmod",
    "normal_form",
    "s_polynomial",
    "s_polynomial_parts",
]
