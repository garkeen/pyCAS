"""Integer-polynomial normalization and coefficient bounds for ``Z[x]``.

This low-level A2a1 module owns the bridge between rational polynomials and
their integer primitive form, the conservative coefficient bound needed by a
later Hensel/Zassenhaus recombination search, and a few exact integer helpers.
It reuses ``PolynomialRing``, ``IntegerRing``, ``RationalField`` and the
existing content/primitive-part/exact-division primitives; it introduces no
second polynomial representation.

Primitive form
--------------

For a nonzero ``value`` in ``Q[x]``, clear all denominators with their least
common multiple ``L``, take the integer content ``c`` of the resulting
polynomial, and normalize the sign so that the primitive part has a positive
leading coefficient.  The returned ``IntegerPolynomialForm(unit, primitive)``
satisfies

    value == unit * primitive,  unit in Q*,  primitive in Z[x],

with ``primitive`` content-free and of positive leading coefficient.  This
representation is unique, and zero is refused because it has no primitive
form.  Constants are handled without a special algorithm: they reduce to the
constant ``1`` with their rational value as the unit.

Coefficient bound
-----------------

Let ``f`` in ``Z[x]`` be nonzero of degree ``n`` and let ``g`` be an integer
factor of ``f`` of degree ``m <= n``.  The Mahler measure is

    M(f) = |lc(f)| * product over the complex roots alpha of f of
           max(1, |alpha|).

Landau's inequality gives ``M(f) <= ||f||_2 = sqrt(sum_i a_i**2)``, and the
roots of ``g`` are a sub-multiset of those of ``f`` (with ``|lc(g)| <=
|lc(f)|`` because ``g`` divides ``f`` in ``Z[x]``).  By Vieta, every
coefficient of ``g`` is bounded by

    2**m * |lc(g)| * product max(1, |alpha|)
        = 2**m * M(g)
        <= 2**m * M(f)
        <= 2**m * ||f||_2
        <= 2**n * ||f||_2.

The returned integer bound

    B = (1 << n) * (isqrt(sum(a_i**2)) + 1)

is strictly larger than ``2**n * ||f||_2`` because ``isqrt(s) + 1 > sqrt(s)``.
It is a proven conservative bound, not the tighter ``comb(n, n//2)``
Mignotte bound; the looser form is used deliberately so that the proof above
does not depend on an unstated binomial-coefficient estimate.  For a nonzero
constant, ``n = 0`` and ``B = |a_0| + 1``.

References: E. Landau, "Sur quelques théorèmes de M. Petrovitch" (1905), and
M. Mignotte, "An inequality about factors of polynomials", *Mathematics of
Computation* 28 (1974), 1153--1157, and *Mathematics for Computer Algebra*
(Springer, 1992).  Textbook treatment: Geddes, Czapor and Labahn, *Algorithms
for Computer Algebra*, Chapters 8--9; Cohen, *A Course in Computational
Algebraic Number Theory*, Chapter 3, for the Zassenhaus/Hensel pipeline that
consumes such bounds.  Reference implementations: Maxima ``src/factor.lisp``
and FriCAS ``src/algebra/gdpoly.spad``/``gaussfac.spad`` for the surrounding
integer-factorization conventions.  This module does not factor ``Z[x]`` or
``Q[x]`` and does not publish a judgment; Hensel lifting, recombination and
the A2a2 checker remain pending.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt, lcm

from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import Polynomial, PolynomialRing, UnivariatePolynomialRing
from cas.algebra.rationals import RationalField


@dataclass(frozen=True, slots=True, eq=False)
class IntegerPolynomialForm:
    """A rational polynomial as ``unit * primitive`` over ``Z[x]``.

    ``unit`` is nonzero, ``primitive`` is nonzero, has content one and a
    positive leading coefficient, and both live in a univariate integer
    polynomial ring.  The constructor checks these invariants, so an illegal
    form cannot be represented.  Equality is structural: the unit, generator
    and coefficient tuple all have to agree, even when two forms come from
    separately constructed integer rings.
    """

    unit: Fraction
    primitive: Polynomial[int]

    def __post_init__(self) -> None:
        if not isinstance(self.unit, Fraction):
            raise TypeError("an integer-polynomial form needs a Fraction unit")
        if self.unit == 0:
            raise ValueError("the zero polynomial has no primitive form")
        owner = self.primitive.owner
        if (
            len(owner.generators) != 1
            or not isinstance(owner.coefficients, IntegerRing)
        ):
            raise TypeError(
                "a primitive part must be a univariate integer polynomial"
            )
        if self.primitive.is_zero():
            raise ValueError("a primitive part must be nonzero")
        if not owner.coefficients.is_one(owner.content(self.primitive)):
            raise ValueError("a primitive part must have content one")
        degree = owner.degree(self.primitive, 0)
        if owner.coefficient(self.primitive, (degree,)) <= 0:
            raise ValueError(
                "a primitive part must have a positive leading coefficient"
            )

    def __eq__(self, other: object) -> bool:
        if self is other:
            return True
        if not isinstance(other, IntegerPolynomialForm):
            return NotImplemented
        return (
            self.unit == other.unit
            and self.primitive.owner.generators
            == other.primitive.owner.generators
            and self.primitive.terms == other.primitive.terms
        )

    def __hash__(self) -> int:
        return hash(
            (
                self.unit,
                self.primitive.owner.generators,
                self.primitive.terms,
            )
        )


def _require_qx(
    ring_q: UnivariatePolynomialRing[Fraction],
    operation: str,
) -> None:
    if not isinstance(ring_q, UnivariatePolynomialRing) or not isinstance(
        ring_q.coefficients, RationalField
    ):
        raise TypeError(f"{operation} needs a univariate polynomial ring over Q")


def _require_zx(
    ring_z: PolynomialRing[int],
    operation: str,
) -> None:
    if len(ring_z.generators) != 1 or not isinstance(
        ring_z.coefficients, IntegerRing
    ):
        raise TypeError(f"{operation} needs a univariate polynomial ring over Z")


def _integer_ring_of(
    ring_q: UnivariatePolynomialRing[Fraction],
) -> PolynomialRing[int]:
    return PolynomialRing((ring_q.generators[0],), IntegerRing())


def _positive_modulus(modulus: int) -> int:
    if isinstance(modulus, bool) or not isinstance(modulus, int):
        raise TypeError("a modulus must be an integer")
    if modulus <= 0:
        raise ValueError("a modulus must be positive")
    return modulus


def _content_and_positive_primitive(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
) -> tuple[int, Polynomial[int]]:
    """The integer content and the primitive part with positive leading term."""
    content = ring_z.content(value)
    primitive = ring_z.primitive_part(value)
    degree = ring_z.degree(primitive, 0)
    if ring_z.coefficient(primitive, (degree,)) < 0:
        primitive = ring_z.neg(primitive)
        content = -content
    return content, primitive


def integer_primitive_form(
    ring_q: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> IntegerPolynomialForm:
    """The unique primitive form ``value == unit * primitive`` over ``Z[x]``.

    Denominators are cleared with their least common multiple, the existing
    integer content/primitive-part primitives are applied, and the sign is
    normalized so the primitive part has positive leading coefficient.  Zero is
    refused; nonzero constants map to ``unit = value`` and ``primitive = 1``.
    """
    _require_qx(ring_q, "the integer primitive form")
    if not ring_q.contains(value):
        raise ValueError("the polynomial belongs to another ring")
    if value.is_zero():
        raise ValueError("the zero polynomial has no integer primitive form")
    denominator_lcm = 1
    for _, coefficient in value.terms:
        denominator_lcm = lcm(denominator_lcm, coefficient.denominator)
    integer_ring = _integer_ring_of(ring_q)
    scaled = integer_ring.sum(
        integer_ring.monomial(
            exponents,
            coefficient.numerator
            * (denominator_lcm // coefficient.denominator),
        )
        for exponents, coefficient in value.terms
    )
    content, primitive = _content_and_positive_primitive(integer_ring, scaled)
    form = IntegerPolynomialForm(Fraction(content, denominator_lcm), primitive)
    embedded = rational_polynomial_form(ring_q, form.primitive)
    if not ring_q.equal(
        ring_q.mul(ring_q.constant(form.unit), embedded),
        value,
    ):
        raise AssertionError(
            "the primitive form does not reconstruct the rational polynomial"
        )
    return form


def rational_polynomial_form(
    ring_q: UnivariatePolynomialRing[Fraction],
    value: Polynomial[int],
) -> Polynomial[Fraction]:
    """Embed an integer polynomial into ``Q[x]`` coefficient by coefficient.

    The exponent support is preserved and the leading coefficient is not
    changed: this is the coefficient embedding, not the monic normalization.
    The source must be a univariate integer polynomial ring with the same
    generator as ``ring_q``.
    """
    _require_qx(ring_q, "the rational polynomial embedding")
    owner = value.owner
    if len(owner.generators) != 1 or not isinstance(
        owner.coefficients, IntegerRing
    ):
        raise TypeError("the source must be a univariate integer polynomial")
    if owner.generators != ring_q.generators:
        raise ValueError("the integer and rational rings use different generators")
    return ring_q.sum(
        ring_q.monomial(exponents, Fraction(coefficient))
        for exponents, coefficient in value.terms
    )


def monic_rational_form(
    ring_q: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> Polynomial[Fraction]:
    """Divide a nonzero rational polynomial by its leading coefficient."""
    _require_qx(ring_q, "the monic rational form")
    if not ring_q.contains(value):
        raise ValueError("the polynomial belongs to another ring")
    if value.is_zero():
        raise ValueError("the zero polynomial has no monic normalization")
    return ring_q.monic(value)


def coefficient_bound(value: Polynomial[int]) -> int:
    """A proven coefficient bound for every integer factor of ``value``.

    For a nonzero polynomial of degree ``n`` return

        ``(1 << n) * (isqrt(sum(a_i**2)) + 1)``.

    Every coefficient of every integer factor is strictly smaller than this
    bound.  The proof is in the module docstring (Landau's inequality plus
    Vieta and the factor-root inclusion).  Zero is refused; a nonzero constant
    uses ``n = 0``.  The bound is deliberately the conservative
    ``2**n * ||value||_2`` form, not the tighter binomial Mignotte bound.
    """
    _require_zx(value.owner, "the coefficient bound")
    if value.is_zero():
        raise ValueError("the zero polynomial has no coefficient bound")
    degree = value.owner.degree(value, 0)
    norm_squared = sum(
        coefficient * coefficient for _, coefficient in value.terms
    )
    return (1 << degree) * (isqrt(norm_squared) + 1)


def _symmetric_coefficient(coefficient: int, divisor: int) -> int:
    residue = coefficient % divisor
    if residue > divisor // 2:
        return residue - divisor
    return residue


def symmetric_residue(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
    modulus: int,
) -> Polynomial[int]:
    """Reduce each coefficient to the symmetric range ``(-m/2, m/2]``.

    For even ``m`` the upper endpoint ``m/2`` is included and ``-m/2`` is not;
    for odd ``m`` the range is the usual ``-(m-1)/2, ..., (m-1)/2``.  The
    modulus must be a positive integer.  Coefficients that reduce to zero are
    omitted by the ring's canonical construction.
    """
    _require_zx(ring_z, "the symmetric residue")
    if not ring_z.contains(value):
        raise ValueError("the polynomial belongs to another ring")
    divisor = _positive_modulus(modulus)
    return ring_z.sum(
        ring_z.monomial(
            exponents,
            _symmetric_coefficient(coefficient, divisor),
        )
        for exponents, coefficient in value.terms
    )


def positive_primitive_part(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
) -> Polynomial[int]:
    """The content-free part with positive leading coefficient.

    The zero polynomial maps to zero explicitly: it has no leading coefficient
    to normalize and the primitive-part convention of the underlying ring is
    already ``zero -> zero``.  Every nonzero input is divided by the
    nonnegative integer content and negated exactly when its leading
    coefficient is negative.
    """
    _require_zx(ring_z, "the positive primitive part")
    if not ring_z.contains(value):
        raise ValueError("the polynomial belongs to another ring")
    if value.is_zero():
        return value
    _, primitive = _content_and_positive_primitive(ring_z, value)
    return primitive


def integer_divisors(value: int) -> tuple[int, ...]:
    """The positive divisors of ``value`` in ascending order.

    ``value == 0`` is refused because it has infinitely many divisors.  A
    negative input is interpreted through ``abs(value)``: ``d`` divides ``n``
    exactly when ``d`` divides ``-n`` for positive ``d``.  ``1`` and ``-1``
    both return ``(1,)``.
    """
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("integer_divisors needs an integer")
    if value == 0:
        raise ValueError("zero has infinitely many divisors")
    magnitude = abs(value)
    small: list[int] = []
    large: list[int] = []
    divisor = 1
    while divisor * divisor <= magnitude:
        if magnitude % divisor == 0:
            small.append(divisor)
            paired = magnitude // divisor
            if paired != divisor:
                large.append(paired)
        divisor += 1
    return tuple(small + large[::-1])


def congruent_mod(
    left: Polynomial[int],
    right: Polynomial[int],
    modulus: int,
) -> bool:
    """Whether two integer polynomials are congruent coefficient-wise mod ``m``.

    The comparison is exact integer divisibility of the coefficient
    differences; the modulus must be positive.  Both polynomials must belong
    to the same univariate integer polynomial ring, so a structural mismatch is
    never disguised as a congruence.
    """
    if not isinstance(left, Polynomial) or not isinstance(right, Polynomial):
        raise TypeError("congruence needs two polynomials")
    if left.owner is not right.owner:
        raise ValueError("the polynomials belong to different rings")
    _require_zx(left.owner, "coefficient congruence")
    divisor = _positive_modulus(modulus)
    difference = left.owner.sub(left, right)
    return all(
        coefficient % divisor == 0
        for _, coefficient in difference.terms
    )


__all__ = [
    "IntegerPolynomialForm",
    "coefficient_bound",
    "congruent_mod",
    "integer_divisors",
    "integer_primitive_form",
    "monic_rational_form",
    "positive_primitive_part",
    "rational_polynomial_form",
    "symmetric_residue",
]
