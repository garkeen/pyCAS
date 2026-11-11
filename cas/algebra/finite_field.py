"""Prime fields ``F_p`` and deterministic primality for machine-word moduli.

Representation
--------------

A member of ``PrimeField(p)`` is a Python ``int`` in the canonical range
``0 <= value < p``.  The field owns that representation: ``contains`` rejects
booleans, non-integers and integers outside the range, and every arithmetic
operation rejects non-members instead of silently reducing an arbitrary Python
integer.  Addition, negation and multiplication reduce modulo ``p``; inversion
uses Fermat's little theorem, ``a**(p-2) mod p``.  This is correct because the
constructor only accepts a proven prime.

Primality certificate
---------------------

``is_prime64`` is a deterministic Miller--Rabin test for ``0 <= n < 2**64``.
It first trial-divides by the small primes up to 37, then runs the strong
probable-prime test with the exact base set

    (2, 325, 9375, 28178, 450775, 9780504, 1795265022).

This seven-base set is deterministic on the whole 64-bit range (Sinclair's
base set, reproduced in the deterministic Miller--Rabin literature; see also
Jaeschke, *Mathematics of Computation* 61 (1993), 915--926, and Sorenson and
Webster, *Mathematics of Computation* 86 (2017), 985--1003).  The range bound
is part of the certificate: values at or above ``2**64`` raise ``ValueError``
instead of returning ``False``, because "outside the proven range" is not the
same mathematical statement as "composite".  Values below 2 return ``False``.

Why no order and no embeddings
------------------------------

A finite field of positive characteristic cannot carry an order compatible
with its field operations, so ``PrimeField`` deliberately does not implement
``Ordered``.  It also does not implement ``IntegerEmbedding`` or
``RationalEmbedding``: the map ``Z -> F_p`` is not injective, and ``Q`` has no
ring map into a field of positive characteristic.  ``Ring.mul_int`` remains
available because it is the intrinsic ``Z``-algebra action ``n * a``, not an
embedding claim.  ``PrimeField`` does not implement ``DescribedRing`` either;
it is an algebraic structure, not a registered parent description.

References
----------

The deterministic Miller--Rabin base set and the strong probable-prime test:
Jaeschke (1993) and Sorenson--Webster (2016), as above.  Field arithmetic and
Fermat inversion are standard; see Cohen, *A Course in Computational Algebraic
Number Theory*, Chapter 1, for the number-theoretic background.  This module
is a low-level algebra API.  It does not construct a polynomial factorization,
publish a judgment, or register a workflow operation.
"""

from __future__ import annotations

from cas.algebra.protocols import Field

_SMALL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
_MILLER_RABIN_BASES = (
    2,
    325,
    9375,
    28178,
    450775,
    9780504,
    1795265022,
)
_UINT64_LIMIT = 1 << 64


def is_prime64(value: int) -> bool:
    """Deterministically decide primality for integers below ``2**64``.

    ``True`` means ``value`` is prime.  ``False`` means ``value < 2`` or a
    Miller--Rabin witness proved compositeness.  A non-integer (including
    ``bool``) raises ``TypeError``; a value at or above ``2**64`` raises
    ``ValueError`` because the deterministic base set is certified only on
    that range.  Out-of-range values are not reported as composite.
    """
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("is_prime64 needs an integer")
    if value < 2:
        return False
    if value >= _UINT64_LIMIT:
        raise ValueError(
            "is_prime64 is certified only for integers below 2**64"
        )
    for prime in _SMALL_PRIMES:
        if value % prime == 0:
            return value == prime
    remaining = value - 1
    power_of_two = 0
    while remaining % 2 == 0:
        remaining //= 2
        power_of_two += 1
    for base in _MILLER_RABIN_BASES:
        witness = base % value
        if witness == 0:
            continue
        residue = pow(witness, remaining, value)
        if residue == 1 or residue == value - 1:
            continue
        for _ in range(power_of_two - 1):
            residue = residue * residue % value
            if residue == value - 1:
                break
        else:
            return False
    return True


class PrimeField(Field[int]):
    """The prime field ``F_p`` for a proven prime ``p < 2**64``.

    Members are the canonical integers ``0, ..., p-1``.  ``characteristic`` is
    ``p``.  ``inv(0)`` raises ``ZeroDivisionError``.  The class intentionally
    has no order and no integer/rational embedding; see the module docstring.
    """

    __slots__ = ("_modulus",)

    def __init__(self, modulus: int) -> None:
        if isinstance(modulus, bool) or not isinstance(modulus, int):
            raise TypeError("a prime-field modulus must be an integer")
        if modulus < 2 or modulus >= _UINT64_LIMIT:
            raise ValueError(
                "a prime-field modulus must satisfy 2 <= p < 2**64"
            )
        if not is_prime64(modulus):
            raise ValueError("a prime-field modulus must be a proven prime")
        self._modulus = modulus

    @property
    def modulus(self) -> int:
        """The prime ``p``."""
        return self._modulus

    @property
    def characteristic(self) -> int:
        return self._modulus

    def zero(self) -> int:
        return 0

    def one(self) -> int:
        return 1

    def _member(self, value: int) -> int:
        if (
            isinstance(value, bool)
            or not isinstance(value, int)
            or not 0 <= value < self._modulus
        ):
            raise ValueError(
                "an element of F_p must be a canonical integer below p"
            )
        return value

    def add(self, left: int, right: int) -> int:
        return (self._member(left) + self._member(right)) % self._modulus

    def neg(self, value: int) -> int:
        return -self._member(value) % self._modulus

    def mul(self, left: int, right: int) -> int:
        return (self._member(left) * self._member(right)) % self._modulus

    def inv(self, value: int) -> int:
        member = self._member(value)
        if member == 0:
            raise ZeroDivisionError("zero has no inverse in F_p")
        # p is prime, so Fermat's little theorem gives a**(p-2) = a**(-1).
        return pow(member, self._modulus - 2, self._modulus)

    def contains(self, value: object) -> bool:
        return (
            isinstance(value, int)
            and not isinstance(value, bool)
            and 0 <= value < self._modulus
        )

    def equal(self, left: int, right: int) -> bool:
        return self._member(left) == self._member(right)


__all__ = ["PrimeField", "is_prime64"]
