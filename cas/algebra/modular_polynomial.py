"""Exact modular polynomial arithmetic and Rabin irreducibility over ``F_p``.

This module is the low-level A2a1 polynomial layer.  It works only with a
``UnivariatePolynomialRing[int]`` whose coefficient structure is a
``PrimeField`` and reuses that ring's ``divmod``, ``gcd`` and ``derivative``;
there is no second polynomial representation and no second coefficient field.

Modular exponentiation
----------------------

``pow_mod`` evaluates ``base**exponent mod modulus`` by binary
square-and-multiply.  The exponent must be a nonnegative integer and the
modulus must be nonzero and monic.  Requiring a monic modulus is not a
mathematical restriction -- any nonzero polynomial generates the same ideal
-- but it fixes the canonical form of the remainder and matches the
Berlekamp precondition.  The result is reduced by the ring's field long
division, so no coefficient inverse is invented outside the prime field.

Squarefreeness and Rabin irreducibility
---------------------------------------

For a monic nonconstant ``f`` in ``F_p[x]``, ``f`` is squarefree exactly when
``gcd(f, f') == 1``.  This is the standard derivative criterion
(Geddes--Czapor--Labahn, *Algorithms for Computer Algebra*, Chapter 8); it also
covers the positive-characteristic case where ``f' == 0``, because then
``gcd(f, 0) = f`` is nonconstant.

``is_irreducible_mod_prime`` is the deterministic Rabin test.  With
``n = deg(f)`` and ``p`` prime, ``f`` is irreducible precisely when

    x**(p**n) == x (mod f)

and, for every prime divisor ``q`` of ``n``,

    gcd(f, x**(p**(n/q)) - x) == 1.

No random sampling is used.  The prime divisors of the small integer ``n`` are
found by trial division; that is a helper for the degree, not a general
integer-factorization API.  A monic linear polynomial is irreducible.  A monic
nonconstant polynomial that is not squarefree is reducible and returns
``False``; zero, constants, and non-monic inputs are refused structurally.

Frobenius equivalence also gives a direct way to build the Berlekamp matrix in
``cas.algebra.modular_factorization``; this module only owns exponentiation,
coefficient reduction, the squarefree predicate and the Rabin predicate.

Coefficient reduction
---------------------

``reduce_mod_prime(ring, value)`` maps a univariate polynomial over the
integer ring ``Z`` into the target prime-field ring with the same generator.
It reduces each coefficient modulo ``p`` and preserves the exponent support.
A polynomial already owned by the target ring is returned unchanged.  Mixing
generators or using non-integer coefficients is refused instead of
reinterpreting them.

Preconditions and structured refusals
--------------------------------------

Every public function requires ``UnivariatePolynomialRing[int]`` over a
``PrimeField``.  A non-univariate ring raises ``ModularPolynomialError`` with
``missing={"univariate_polynomial_ring"}`` and non-prime coefficients raise
``missing={"prime_field_coefficients"}``.  Foreign-ring polynomials,
zero/non-monic moduli, zero/constant/non-monic inputs and negative exponents
raise the same error type with a precise ``missing`` token and a nonempty
``detail``.  These are fragment boundaries, not mathematical refutations.

References
----------

Geddes, Czapor and Labahn, *Algorithms for Computer Algebra*, Chapters 8--9,
for squarefree decomposition, finite-field factorization and irreducibility.
Rabin, "Probabilistic algorithms in finite fields", *SIAM Journal on
Computing* 9 (1980), 273--280, for the deterministic criterion above.
Reference implementations: Maxima ``src/factor.lisp`` (``cpberl`` and the
finite-field factorization helpers) and FriCAS ``src/algebra/gdpoly.spad``
(polynomial coefficient operations).  Reference behavior is not a proof; the
arguments in this docstring and the property tests are the local evidence.
"""

from __future__ import annotations

from cas.algebra.finite_field import PrimeField
from cas.algebra.integers import IntegerRing
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing

_PRIME_FIELD_MISSING = frozenset({"prime_field_coefficients"})
_UNIVARIATE_RING_MISSING = frozenset({"univariate_polynomial_ring"})
_RING_OWNERSHIP_MISSING = frozenset({"ring_ownership"})
_NONZERO_MODULUS_MISSING = frozenset({"nonzero_modulus"})
_MONIC_MODULUS_MISSING = frozenset({"monic_modulus"})
_NONNEGATIVE_EXPONENT_MISSING = frozenset({"nonnegative_exponent"})
_NONZERO_POLYNOMIAL_MISSING = frozenset({"nonzero_polynomial"})
_NONCONSTANT_POLYNOMIAL_MISSING = frozenset({"nonconstant_polynomial"})
_MONIC_POLYNOMIAL_MISSING = frozenset({"monic_polynomial"})
_INTEGER_COEFFICIENTS_MISSING = frozenset({"integer_coefficients"})
_MATCHING_GENERATORS_MISSING = frozenset({"matching_generators"})


class ModularPolynomialError(ValueError):
    """A modular-polynomial request is outside this module's fragment.

    ``detail`` is nonempty prose and ``missing`` is the structured capability
    or precondition set.  The error is never a mathematical refutation; it
    states that the low-level algorithm cannot apply its assumptions to the
    supplied data.
    """

    def __init__(self, detail: str, *, missing: frozenset[str]) -> None:
        super().__init__(detail)
        self.detail = detail
        self.missing = frozenset(missing)


def _require_prime_field(
    ring: UnivariatePolynomialRing[int],
    operation: str,
) -> PrimeField:
    if not isinstance(ring, UnivariatePolynomialRing):
        raise ModularPolynomialError(
            f"{operation} needs a univariate polynomial ring",
            missing=_UNIVARIATE_RING_MISSING,
        )
    coefficients = ring.coefficients
    if not isinstance(coefficients, PrimeField):
        raise ModularPolynomialError(
            f"{operation} needs polynomial coefficients in a prime field",
            missing=_PRIME_FIELD_MISSING,
        )
    return coefficients


def _require_owned(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
    operation: str,
) -> None:
    if not ring.contains(value):
        raise ModularPolynomialError(
            f"{operation}: the polynomial belongs to another ring",
            missing=_RING_OWNERSHIP_MISSING,
        )


def _require_monic_nonzero_modulus(
    ring: UnivariatePolynomialRing[int],
    modulus: Polynomial[int],
    field: PrimeField,
    operation: str,
) -> None:
    _require_owned(ring, modulus, operation)
    if modulus.is_zero():
        raise ModularPolynomialError(
            f"{operation} needs a nonzero modulus",
            missing=_NONZERO_MODULUS_MISSING,
        )
    degree = ring.degree(modulus, 0)
    if not field.is_one(ring.coefficient(modulus, (degree,))):
        raise ModularPolynomialError(
            f"{operation} needs a monic modulus",
            missing=_MONIC_MODULUS_MISSING,
        )


def _require_monic_nonconstant(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
    field: PrimeField,
    operation: str,
) -> int:
    _require_owned(ring, value, operation)
    if value.is_zero():
        raise ModularPolynomialError(
            f"{operation} needs a nonzero polynomial",
            missing=_NONZERO_POLYNOMIAL_MISSING,
        )
    degree = ring.degree(value, 0)
    if degree == 0:
        raise ModularPolynomialError(
            f"{operation} needs a nonconstant polynomial",
            missing=_NONCONSTANT_POLYNOMIAL_MISSING,
        )
    if not field.is_one(ring.coefficient(value, (degree,))):
        raise ModularPolynomialError(
            f"{operation} needs a monic polynomial",
            missing=_MONIC_POLYNOMIAL_MISSING,
        )
    return degree


def pow_mod(
    ring: UnivariatePolynomialRing[int],
    base: Polynomial[int],
    exponent: int,
    modulus: Polynomial[int],
) -> Polynomial[int]:
    """Return ``base**exponent mod modulus`` by square-and-multiply.

    Preconditions: prime-field coefficients, a nonnegative integer exponent,
    a nonzero monic modulus, and all polynomials owned by ``ring``.  The
    return value is the canonical remainder, so its degree is smaller than
    ``deg(modulus)``.  ``exponent == 0`` returns ``1`` reduced modulo the
    modulus.
    """
    field = _require_prime_field(ring, "modular exponentiation")
    _require_owned(ring, base, "modular exponentiation")
    if isinstance(exponent, bool) or not isinstance(exponent, int):
        raise TypeError("a modular exponent must be an integer")
    if exponent < 0:
        raise ModularPolynomialError(
            "modular exponentiation needs a nonnegative exponent",
            missing=_NONNEGATIVE_EXPONENT_MISSING,
        )
    _require_monic_nonzero_modulus(
        ring, modulus, field, "modular exponentiation"
    )
    _, result = ring.divmod(ring.one(), modulus)
    _, current = ring.divmod(base, modulus)
    remaining = exponent
    while remaining:
        if remaining & 1:
            _, result = ring.divmod(ring.mul(result, current), modulus)
        remaining >>= 1
        if remaining:
            _, current = ring.divmod(ring.mul(current, current), modulus)
    return result


def _reduce_coefficient(coefficient: int, field: PrimeField) -> int:
    return coefficient % field.modulus


def _reduce_terms(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
    field: PrimeField,
) -> Polynomial[int]:
    return ring.sum(
        ring.monomial(
            exponents,
            _reduce_coefficient(coefficient, field),
        )
        for exponents, coefficient in value.terms
    )


def reduce_mod_prime(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> Polynomial[int]:
    """Reduce an integer polynomial into the target prime-field ring.

    ``value`` either already belongs to ``ring`` (and is returned unchanged) or
    belongs to a univariate polynomial ring over ``IntegerRing`` with exactly
    the same generator.  Each integer coefficient is reduced modulo the target
    modulus; the exponent support is preserved and zero coefficients vanish
    through the ring's canonical construction.  A mismatched generator or a
    non-integer coefficient ring is refused.
    """
    field = _require_prime_field(ring, "coefficient reduction modulo p")
    if value.owner is ring:
        return value
    source = value.owner
    if len(source.generators) != 1 or source.generators != ring.generators:
        raise ModularPolynomialError(
            "coefficient reduction needs one matching polynomial generator",
            missing=_MATCHING_GENERATORS_MISSING,
        )
    if not isinstance(source.coefficients, IntegerRing):
        raise ModularPolynomialError(
            "coefficient reduction needs integer source coefficients",
            missing=_INTEGER_COEFFICIENTS_MISSING,
        )
    return _reduce_terms(ring, value, field)


def is_squarefree_mod_prime(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> bool:
    """Whether a monic nonconstant polynomial over ``F_p`` is squarefree.

    The decision is exactly ``gcd(value, value') == 1``.  Zero, constants and
    non-monic values are structural refusals; a non-squarefree value returns
    ``False``.
    """
    field = _require_prime_field(ring, "squarefree test")
    _require_monic_nonconstant(ring, value, field, "squarefree test")
    derivative = ring.derivative(value, 0)
    return ring.is_one(ring.gcd(value, derivative))


def _distinct_prime_divisors(value: int) -> tuple[int, ...]:
    """Distinct prime divisors of a positive integer by trial division."""
    if value < 2:
        return ()
    divisors: list[int] = []
    remaining = value
    candidate = 2
    while candidate * candidate <= remaining:
        if remaining % candidate == 0:
            divisors.append(candidate)
            while remaining % candidate == 0:
                remaining //= candidate
        candidate += 1
    if remaining > 1:
        divisors.append(remaining)
    return tuple(divisors)


def is_irreducible_mod_prime(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> bool:
    """Deterministic Rabin irreducibility for a monic ``F_p[x]`` polynomial.

    For ``n = deg(value)`` the test checks

        x**(p**n) == x (mod value)

    and, for every distinct prime divisor ``q`` of ``n``,

        gcd(value, x**(p**(n/q)) - x) == 1.

    Monic linear polynomials return ``True`` immediately.  A monic nonconstant
    polynomial that fails the squarefree derivative test is reducible and
    returns ``False``.  Zero, constants and non-monic inputs are refused
    structurally.  No randomness is used, and ``p == 2`` is supported.
    """
    field = _require_prime_field(ring, "irreducibility test")
    degree = _require_monic_nonconstant(ring, value, field, "irreducibility test")
    if degree == 1:
        return True
    derivative = ring.derivative(value, 0)
    if not ring.is_one(ring.gcd(value, derivative)):
        return False
    generator = ring.generator(0)
    frobenius = pow_mod(
        ring,
        generator,
        field.modulus**degree,
        value,
    )
    if not ring.equal(frobenius, generator):
        return False
    for prime in _distinct_prime_divisors(degree):
        exponent = field.modulus ** (degree // prime)
        powered = pow_mod(ring, generator, exponent, value)
        if not ring.is_one(ring.gcd(value, ring.sub(powered, generator))):
            return False
    return True


__all__ = [
    "ModularPolynomialError",
    "is_irreducible_mod_prime",
    "is_squarefree_mod_prime",
    "pow_mod",
    "reduce_mod_prime",
]
