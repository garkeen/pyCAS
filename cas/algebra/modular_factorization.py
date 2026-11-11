"""Deterministic Berlekamp factorization over a prime field.

This is the low-level A2a1 finite-field factorization primitive.  It accepts a
monic squarefree polynomial in ``F_p[x]`` with ``p`` a proven 64-bit prime,
returns the complete tuple of monic irreducible factors, and uses only the
existing polynomial ring, ``pow_mod`` and ``MatrixSpace.nullspace``.  It does
not implement Hensel lifting, Zassenhaus recombination, ``Q[x]`` or ``Z[x]``
factorization, and it publishes no judgment or operation.

Berlekamp's algorithm
---------------------

Let ``f`` be monic, squarefree and of degree ``n`` over ``F_p``.  Build the
``n x n`` Berlekamp matrix ``Q`` whose column ``i`` is the coefficient vector
of ``x**(i*p) mod f`` for ``i = 0, ..., n-1``.  The nullspace of ``Q - I`` is
the Berlekamp subalgebra

    B = { b in F_p[x] : deg(b) < n and b**p == b (mod f) }.

Because ``f`` is squarefree, the Chinese remainder theorem identifies ``B``
with ``F_p**r``, where ``r`` is the number of distinct irreducible factors of
``f``.  Hence ``dim B = r``; ``r == 1`` means ``f`` is irreducible.  For a
basis polynomial ``b`` and a constant ``c`` in ``F_p``, ``gcd(f, b - c)`` is
the product of the irreducible factors on which ``b`` reduces to ``c``.
Scanning a basis and all constants therefore separates a reducible ``f`` into
two proper monic factors.  Constant basis polynomials are skipped: their gcd
with ``f`` is either one or ``f`` itself, so they cannot produce a proper
split.  The search applies this split to every pending factor until only
irreducible pieces remain.

Determinism, termination and budget
-----------------------------------

Every object is processed in a deterministic order: ``Q``'s columns are built
in increasing powers, ``MatrixSpace.nullspace`` returns the basis in free
column order, constants are scanned as ``0, 1, ..., p-1``, and the final
factor list is sorted by ``(degree, coefficient tuple)``.  No random element,
randomized polynomial or heuristic stopping rule is used.

Each split strictly lowers the degree of the pending factors, so the binary
split tree has exactly ``r - 1`` internal nodes and at most ``r`` leaves.
``ModularBudget.splitting`` bounds those internal split steps and
``ModularBudget.gcd`` bounds the trial gcd evaluations performed while
searching for a split.  The single squarefree precondition is input validation
and is not charged to the search budget.  Exhaustion raises
``ModularFactorizationError`` with ``missing={"modular_factorization_budget"}``
and never returns a partial factor list; a budget is resource control only and
does not change the truth of a completed factorization.

Preconditions and refusals
--------------------------

The coefficient structure must be a ``PrimeField`` and ``value`` must be monic,
nonzero and nonconstant.  A non-squarefree value is refused structurally: this
function factors squarefree values and does not silently add multiplicity
handling.  Zero, constants, non-monic values, foreign rings, non-prime
coefficient fields and non-``UnivariatePolynomialRing`` inputs raise
``ModularFactorizationError`` with a precise ``missing`` token and nonempty
``detail``.  A prime field of characteristic two is fully supported.

References
----------

E. R. Berlekamp, "Factoring polynomials over finite fields", *Bell System
Technical Journal* 46 (1967), 1853--1859, and "Factoring polynomials over large
finite fields", *Mathematics of Computation* 24 (1970), 713--735.  M. O. Rabin,
"Probabilistic algorithms in finite fields", *SIAM Journal on Computing* 9
(1980), 273--280, for the deterministic irreducibility criterion consumed by
the factorization tests.  Geddes, Czapor and Labahn, *Algorithms for Computer
Algebra*, Chapters 8--9, for the textbook treatment.  Cohen, *A Course in
Computational Algebraic Number Theory*, Chapter 3, for finite-field
factorization and its place in the Hensel/Zassenhaus pipeline.

Reference implementations: Maxima ``src/factor.lisp`` (``cpberl``, the
finite-field Berlekamp driver, together with ``cpber1``/``cpbg``) and FriCAS
``src/algebra/gdpoly.spad``/``gaussfac.spad`` for the surrounding polynomial
and integer-factorization conventions.  Reference behavior is not a proof;
the split identity and termination argument above are the local evidence.  The
``Z[x]``/``Q[x]`` completion (Hensel lifting, recombination and an independent
checker) is a later A2a2 slice.
"""

from __future__ import annotations

from dataclasses import dataclass

from cas.algebra.finite_field import PrimeField
from cas.algebra.linear import MatrixSpace
from cas.algebra.modular_polynomial import (
    ModularPolynomialError,
    is_squarefree_mod_prime,
    pow_mod,
)
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing

_BUDGET_MISSING = frozenset({"modular_factorization_budget"})
_PRIME_FIELD_MISSING = frozenset({"prime_field_coefficients"})
_RING_OWNERSHIP_MISSING = frozenset({"ring_ownership"})
_UNIVARIATE_RING_MISSING = frozenset({"univariate_polynomial_ring"})
_SQUAREFREE_MISSING = frozenset({"squarefree_polynomial"})


@dataclass(frozen=True, slots=True)
class ModularBudget:
    """Resource limits for the Berlekamp split search.

    ``splitting`` is the maximum number of bisection steps (internal nodes of
    the factor tree) and ``gcd`` is the maximum number of trial gcd evaluations
    while searching for those steps.  Both are nonnegative integers; booleans
    are rejected.  The limits are resource control, not mathematical data.
    """

    splitting: int = 1024
    gcd: int = 1 << 20

    def __post_init__(self) -> None:
        if isinstance(self.splitting, bool) or not isinstance(self.splitting, int):
            raise TypeError("a splitting budget must be an integer")
        if self.splitting < 0:
            raise ValueError("a splitting budget cannot be negative")
        if isinstance(self.gcd, bool) or not isinstance(self.gcd, int):
            raise TypeError("a gcd budget must be an integer")
        if self.gcd < 0:
            raise ValueError("a gcd budget cannot be negative")


class ModularFactorizationError(ValueError):
    """A Berlekamp-factorization request is outside the declared fragment.

    ``detail`` is nonempty prose and ``missing`` is the structured capability,
    precondition or budget token.  It is never a mathematical refutation: the
    error means that no complete factorization was produced under the stated
    assumptions.
    """

    def __init__(self, detail: str, *, missing: frozenset[str]) -> None:
        super().__init__(detail)
        self.detail = detail
        self.missing = frozenset(missing)


def _factor_key(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
) -> tuple[int, tuple[int, ...]]:
    """The deterministic factor order: degree first, then coefficients."""
    degree = ring.degree(value, 0)
    return (
        degree,
        tuple(ring.coefficient(value, (index,)) for index in range(degree + 1)),
    )


def _berlekamp_basis(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
    field: PrimeField,
) -> tuple[Polynomial[int], ...]:
    """A basis of the Berlekamp subalgebra of ``value``."""
    degree = ring.degree(value, 0)
    generator = ring.generator(0)
    columns = tuple(
        pow_mod(ring, generator, index * field.modulus, value)
        for index in range(degree)
    )
    rows = [
        [
            ring.coefficient(column, (row,))
            for column in columns
        ]
        for row in range(degree)
    ]
    space = MatrixSpace(field, degree, degree)
    berlekamp = space.matrix(rows)
    difference = space.sub(berlekamp, space.one())
    return tuple(
        ring.sum(
            ring.monomial((index,), coefficient)
            for index, coefficient in enumerate(vector)
        )
        for vector in space.nullspace(difference)
    )


def factor_squarefree_mod_prime(
    ring: UnivariatePolynomialRing[int],
    value: Polynomial[int],
    budget: ModularBudget = ModularBudget(),
) -> tuple[Polynomial[int], ...]:
    """Factor a monic squarefree polynomial over ``F_p`` into irreducibles.

    Return the complete tuple of monic irreducible factors, sorted by
    ``(degree, coefficient tuple)``.  The product of the result is ``value``.
    The input must be nonzero, nonconstant, monic and squarefree; all of these
    are checked before any factor is returned.  Budget exhaustion raises
    ``ModularFactorizationError`` and never yields a partial list.
    """
    if not isinstance(budget, ModularBudget):
        raise TypeError("a modular factorization budget is required")
    if not isinstance(ring, UnivariatePolynomialRing):
        raise ModularFactorizationError(
            "Berlekamp factorization needs a univariate polynomial ring",
            missing=_UNIVARIATE_RING_MISSING,
        )
    coefficients = ring.coefficients
    if not isinstance(coefficients, PrimeField):
        raise ModularFactorizationError(
            "Berlekamp factorization needs prime-field coefficients",
            missing=_PRIME_FIELD_MISSING,
        )
    if not ring.contains(value):
        raise ModularFactorizationError(
            "Berlekamp factorization: the polynomial belongs to another ring",
            missing=_RING_OWNERSHIP_MISSING,
        )
    try:
        squarefree = is_squarefree_mod_prime(ring, value)
    except ModularPolynomialError as error:
        raise ModularFactorizationError(
            error.detail,
            missing=error.missing,
        ) from error
    if not squarefree:
        raise ModularFactorizationError(
            "Berlekamp factorization needs a squarefree polynomial",
            missing=_SQUAREFREE_MISSING,
        )
    field = coefficients
    remaining_splits = budget.splitting
    remaining_gcds = budget.gcd

    def spend_gcd() -> None:
        nonlocal remaining_gcds
        if remaining_gcds <= 0:
            raise ModularFactorizationError(
                "the modular factorization budget was exhausted while "
                "searching for a factor",
                missing=_BUDGET_MISSING,
            )
        remaining_gcds -= 1

    def spend_split() -> None:
        nonlocal remaining_splits
        if remaining_splits <= 0:
            raise ModularFactorizationError(
                "the modular factorization budget was exhausted while "
                "splitting a reducible factor",
                missing=_BUDGET_MISSING,
            )
        remaining_splits -= 1

    pending: list[Polynomial[int]] = [value]
    factors: list[Polynomial[int]] = []
    while pending:
        current = pending.pop()
        current_degree = ring.degree(current, 0)
        if current_degree <= 1:
            factors.append(current)
            continue
        basis = _berlekamp_basis(ring, current, field)
        if len(basis) == 1:
            factors.append(current)
            continue
        split = False
        for candidate in basis:
            if ring.is_constant(candidate):
                continue
            for constant in range(field.modulus):
                spend_gcd()
                divisor = ring.gcd(
                    current,
                    ring.sub(candidate, ring.constant(constant)),
                )
                divisor_degree = ring.degree(divisor, 0)
                if not 0 < divisor_degree < current_degree:
                    continue
                spend_split()
                quotient, remainder = ring.divmod(current, divisor)
                if not remainder.is_zero():
                    raise AssertionError(
                        "a Berlekamp divisor does not divide the polynomial"
                    )
                pending.append(divisor)
                pending.append(quotient)
                split = True
                break
            if split:
                break
        if not split:
            raise AssertionError(
                "a squarefree reducible polynomial must have a Berlekamp split"
            )
    return tuple(sorted(factors, key=lambda factor: _factor_key(ring, factor)))


__all__ = [
    "ModularBudget",
    "ModularFactorizationError",
    "factor_squarefree_mod_prime",
]
