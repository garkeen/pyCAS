"""Hensel lifting for integer polynomials and witness construction over ``Q[x]``.

This is the low-level A2a2a module.  It lifts a complete modular
factorization of a primitive squarefree integer polynomial to a factorization
modulo a prime power, and it builds the witness that a later Zassenhaus
recombination step and an independent irreducibility checker will consume.  The
module does *not* recombine lifted factors into integer factors, does not
factor ``Z[x]`` or ``Q[x]``, and publishes no specification, checker,
operation, workflow or REPL command.

Linear Hensel lifting
---------------------

Let ``f`` in ``Z[x]`` be primitive, squarefree, nonconstant and have positive
leading coefficient ``a = lc(f)``.  Fix a prime ``p`` with ``p`` not dividing
``a`` and let ``F = a**(-1) * f mod p**k``.  If ``F mod p = g_1 * ... * g_r``
is a complete factorization into pairwise coprime monic polynomials, Hensel's
lemma lifts that factorization uniquely to monic ``G_i`` modulo ``p**k`` with

    f == a * G_1 * ... * G_r  (mod p**k).

The implementation uses the binary-tree variant of the linear lifting step.
The leaves are the modular factors; every internal node stores the product of
the modular factors in its subtree.  The root polynomial is ``F``.  Splitting a
node with polynomial ``F_node`` and modular children ``g`` and ``h`` proceeds
from precision ``j`` to ``j + 1`` by

    E   = (F_node - G H) / p**j  mod p,
    s g + t h = 1                over F_p,
    dG  = (t E) mod g,
    dH  = (s E) mod h,
    G  <- G + p**j dG,
    H  <- H + p**j dH,

and the congruence ``F_node == G H (mod p**(j+1))`` is checked after every
step.  The child polynomials are then split recursively with the same step.
Every coefficient is kept in ``[0, p**k)``, and the final product identity and
the degree sum are checked again before the result is returned.  The argument
that the reductions of ``dG`` and ``dH`` are harmless uses
``deg(E) < deg(F_node) = deg(g) + deg(h)``: any multiple of ``g h`` added to the
sum must vanish, so the Bezout combination still produces ``E`` (Geddes,
Czapor and Labahn, *Algorithms for Computer Algebra*, §8.4; Cohen, *A Course in
Computational Algebraic Number Theory*, Algorithm 3.5.5; von zur Gathen and
Gerhard, *Modern Computer Algebra*, Chapter 15).

Witness construction
--------------------

``hensel_witness_for_radical`` accepts a monic squarefree nonzero nonconstant
``Q[x]`` polynomial ``radical`` (the product of the distinct claimed factors of
a later factorization), converts it to its primitive integer form ``R`` with
positive leading coefficient ``a``, and scans primes in ascending order.  For
each prime it independently reduces ``R/a`` mod ``p``, checks that the
reduction is squarefree, factors it with Berlekamp, and lifts to the least
precision ``k`` with ``p**k > 2 * coefficient_bound(R)``.  The bound is the
Landau/Mignotte coefficient bound of ``cas.algebra.integer_polynomial``; the
factor ``2`` makes the symmetric residue of every true integer factor
unambiguous.  The witness is ``HenselLift(p, k, lifted)``.  The caller's
factor data is never trusted: the modular factorization is recomputed here.

Budgets and refusals
--------------------

``FactorizationBudget.max_hensel_precision`` bounds the Hensel precision:
every internal step from ``j`` to ``j + 1`` requires ``j + 1 <= precision <=
max_hensel_precision``, so a request that asks for more precision than the
budget is refused before any lift is attempted.  ``max_prime_trials`` bounds
the number of ascending primes inspected by the witness, and the nested
``ModularBudget`` is passed unchanged to Berlekamp.  Exhaustion raises
``FactorizationBudgetError`` with a precise ``missing`` token and never returns
a partial lift.  Structural refusals raise ``FactorizationFragmentError``
with a nonempty ``detail`` and ``missing`` set; neither error is a
mathematical refutation.

References
----------

Hensel's lemma and the linear lifting recurrence: Geddes, Czapor and Labahn,
*Algorithms for Computer Algebra*, Chapter 8; Cohen, *A Course in
Computational Algebraic Number Theory*, Chapter 3 (Hensel lifting and the
Zassenhaus pipeline); von zur Gathen and Gerhard, *Modern Computer Algebra*,
Chapter 15.  Coefficient bound: Landau (1905) and Mignotte, *Mathematics for
Computer Algebra* (Springer, 1992), as documented in
``cas.algebra.integer_polynomial``.

Reference implementations: FriCAS ``src/algebra/ghensel.spad``
(``GeneralHenselPackage``, ``HenselLift`` lifts without recombination and its
``completeHensel`` recombines on the way) and ``src/algebra/galfact.spad``
(``henselFact``); Maxima ``src/factor.lisp`` for the surrounding integer
factorization entry points.  The reference implementations are used for
algorithm structure only, not as a correctness proof.  The Zassenhaus subset
recombination, ``Z[x]``/``Q[x]`` factorization, ``HasFactorization``,
independent checker, operation, bootstrap, workflow and REPL are not
implemented here; A2 is not complete.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from fractions import Fraction

from cas.algebra.finite_field import PrimeField, is_prime64
from cas.algebra.integer_polynomial import (
    coefficient_bound,
    congruent_mod,
    integer_primitive_form,
    rational_polynomial_form,
)
from cas.algebra.integers import IntegerRing
from cas.algebra.modular_factorization import (
    ModularBudget,
    ModularFactorizationError,
    factor_squarefree_mod_prime,
)
from cas.algebra.modular_polynomial import (
    ModularPolynomialError,
    is_squarefree_mod_prime,
    reduce_mod_prime,
)
from cas.algebra.polynomial import (
    Polynomial,
    PolynomialRing,
    UnivariatePolynomialRing,
)
from cas.algebra.rationals import RationalField

_UINT64_LIMIT = 1 << 64
_RING_OWNERSHIP_MISSING = frozenset({"ring_ownership"})
_NONZERO_POLYNOMIAL_MISSING = frozenset({"nonzero_polynomial"})
_NONCONSTANT_POLYNOMIAL_MISSING = frozenset({"nonconstant_polynomial"})
_MONIC_POLYNOMIAL_MISSING = frozenset({"monic_polynomial"})
_PRIMITIVE_SQUAREFREE_MISSING = frozenset(
    {"primitive_squarefree_polynomial"}
)
_POSITIVE_LEADING_MISSING = frozenset({"positive_leading_coefficient"})
_PRIME_MODULUS_MISSING = frozenset({"prime_modulus"})
_APPLICABLE_PRIME_MISSING = frozenset({"applicable_prime"})
_POSITIVE_PRECISION_MISSING = frozenset({"positive_precision"})
_MONIC_FACTORS_MISSING = frozenset({"monic_factors"})
_NONCONSTANT_FACTORS_MISSING = frozenset({"nonconstant_factors"})
_COMPLETE_FACTORIZATION_MISSING = frozenset({"complete_factorization"})
_DISTINCT_FACTORS_MISSING = frozenset({"distinct_factors"})
_COPRIME_FACTORS_MISSING = frozenset({"coprime_factors"})
_FACTOR_RING_MISSING = frozenset({"factor_ring"})
_FACTORIZATION_BUDGET_MISSING = frozenset({"factorization_budget"})
_HENSEL_PRECISION_MISSING = frozenset({"hensel_precision"})


@dataclass(frozen=True, slots=True)
class FactorizationBudget:
    """Resource limits for Hensel lifting and witness construction.

    ``max_prime_trials`` is the maximum number of ascending primes inspected by
    ``hensel_witness_for_radical``; ``max_hensel_precision`` bounds the Hensel
    precision ``k`` (every internal step from ``j`` to ``j + 1`` needs
    ``j + 1 <= k <= max_hensel_precision``); ``modular`` is passed unchanged to
    the Berlekamp factorization.  All limits are nonnegative integers and
    booleans are rejected.  The limits are resource control, not mathematical
    data.
    """

    max_prime_trials: int = 64
    max_hensel_precision: int = 1 << 12
    modular: ModularBudget = ModularBudget()

    def __post_init__(self) -> None:
        if isinstance(self.max_prime_trials, bool) or not isinstance(
            self.max_prime_trials, int
        ):
            raise TypeError("a prime-trial budget must be an integer")
        if self.max_prime_trials < 0:
            raise ValueError("a prime-trial budget cannot be negative")
        if isinstance(self.max_hensel_precision, bool) or not isinstance(
            self.max_hensel_precision, int
        ):
            raise TypeError("a Hensel-precision budget must be an integer")
        if self.max_hensel_precision < 0:
            raise ValueError("a Hensel-precision budget cannot be negative")
        if not isinstance(self.modular, ModularBudget):
            raise TypeError("a factorization budget needs a modular budget")


class FactorizationError(ValueError):
    """A Hensel request is outside the declared fragment or budget.

    ``detail`` is nonempty prose and ``missing`` is the structured capability,
    precondition or budget token.  The error is never a mathematical
    refutation: it states that no complete lift was produced under the stated
    assumptions.
    """

    def __init__(self, detail: str, *, missing: frozenset[str]) -> None:
        if not detail:
            raise ValueError("a factorization error needs a detail")
        if not missing:
            raise ValueError("a factorization error needs a missing token")
        super().__init__(detail)
        self.detail = detail
        self.missing = frozenset(missing)


class FactorizationFragmentError(FactorizationError):
    """The supplied data does not satisfy the declared Hensel preconditions."""


class FactorizationBudgetError(FactorizationError):
    """The declared resource budget is exhausted; no partial result exists."""


@dataclass(frozen=True, slots=True)
class HenselLift:
    """A lifted modular factorization consumed by the future checker.

    ``prime`` is a proven 64-bit prime, ``precision`` is a positive integer,
    and ``lifted`` is a nonempty tuple of monic nonconstant integer polynomials
    owned by one univariate integer polynomial ring, with every coefficient in
    ``[0, prime**precision)``.  The record does not carry the polynomial it was
    built from; the future checker reconstructs the congruence independently
    from the candidate radical.  The constructor enforces the structural
    invariants, so an illegal witness cannot be represented.
    """

    prime: int
    precision: int
    lifted: tuple[Polynomial[int], ...]

    def __post_init__(self) -> None:
        if isinstance(self.prime, bool) or not isinstance(self.prime, int):
            raise TypeError("a Hensel prime must be an integer")
        if self.prime < 2 or self.prime >= _UINT64_LIMIT:
            raise ValueError("a Hensel prime must be below 2**64")
        if not is_prime64(self.prime):
            raise ValueError("a Hensel prime must be a proven prime")
        if isinstance(self.precision, bool) or not isinstance(
            self.precision, int
        ):
            raise TypeError("a Hensel precision must be an integer")
        if self.precision <= 0:
            raise ValueError("a Hensel precision must be positive")
        if not isinstance(self.lifted, tuple):
            raise TypeError("a Hensel lift needs a tuple of polynomials")
        if not self.lifted:
            raise ValueError("a Hensel lift needs at least one factor")
        if not isinstance(self.lifted[0], Polynomial):
            raise TypeError("a lifted Hensel factor must be a polynomial")
        owner = self.lifted[0].owner
        if (
            len(owner.generators) != 1
            or not isinstance(owner.coefficients, IntegerRing)
        ):
            raise TypeError(
                "lifted Hensel factors must be univariate integer polynomials"
            )
        modulus = self.prime**self.precision
        for factor in self.lifted:
            if not isinstance(factor, Polynomial):
                raise TypeError("a lifted Hensel factor must be a polynomial")
            if factor.owner is not owner:
                raise ValueError(
                    "lifted Hensel factors must share one integer ring"
                )
            if factor.is_zero():
                raise ValueError("a lifted Hensel factor must be nonzero")
            degree = owner.degree(factor, 0)
            if degree < 1:
                raise ValueError("a lifted Hensel factor must be nonconstant")
            if not owner.coefficients.is_one(
                owner.coefficient(factor, (degree,))
            ):
                raise ValueError("a lifted Hensel factor must be monic")
            for _, coefficient in factor.terms:
                if not 0 <= coefficient < modulus:
                    raise ValueError(
                        "a lifted coefficient must lie in [0, p**precision)"
                    )


@dataclass(frozen=True, slots=True)
class _FactorTree:
    """A binary tree of modular factors with subtree products over ``F_p``."""

    product: Polynomial[int]
    children: tuple[_FactorTree, _FactorTree] | None


def _require_z_ring(ring: PolynomialRing[int], operation: str) -> None:
    if (
        not isinstance(ring, PolynomialRing)
        or len(ring.generators) != 1
        or not isinstance(ring.coefficients, IntegerRing)
    ):
        raise TypeError(
            f"{operation} needs a univariate polynomial ring over Z"
        )


def _require_q_ring(
    ring: UnivariatePolynomialRing[Fraction],
    operation: str,
) -> None:
    if not isinstance(ring, UnivariatePolynomialRing) or not isinstance(
        ring.coefficients, RationalField
    ):
        raise TypeError(
            f"{operation} needs a univariate polynomial ring over Q"
        )


def _q_ring_of(ring_z: PolynomialRing[int]) -> UnivariatePolynomialRing[Fraction]:
    return UnivariatePolynomialRing(
        ring_z.generators[0],
        RationalField(),
    )


def _prime_ring_of(
    ring_z: PolynomialRing[int],
    prime: int,
) -> UnivariatePolynomialRing[int]:
    return UnivariatePolynomialRing(
        ring_z.generators[0],
        PrimeField(prime),
    )


def _prime_field(ring_p: UnivariatePolynomialRing[int]) -> PrimeField:
    coefficients = ring_p.coefficients
    if not isinstance(coefficients, PrimeField):
        raise TypeError(
            "Hensel lifting needs prime-field modular coefficients"
        )
    return coefficients


def _integer_lift(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
) -> Polynomial[int]:
    """Copy an ``F_p`` polynomial into ``ring_z`` with nonnegative coefficients."""
    return ring_z.sum(
        ring_z.monomial(exponents, coefficient)
        for exponents, coefficient in value.terms
    )


def _reduce_coefficients(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
    modulus: int,
) -> Polynomial[int]:
    return ring_z.sum(
        ring_z.monomial(exponents, coefficient % modulus)
        for exponents, coefficient in value.terms
    )


def _scaled_integer_lift(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
    scale: int,
    modulus: int,
) -> Polynomial[int]:
    """Return ``scale * value`` with every coefficient reduced modulo ``modulus``."""
    return ring_z.sum(
        ring_z.monomial(
            exponents,
            (scale * coefficient) % modulus,
        )
        for exponents, coefficient in value.terms
    )


def _is_squarefree_over_z(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
) -> bool:
    ring_q = _q_ring_of(ring_z)
    rational = rational_polynomial_form(ring_q, value)
    derivative = ring_q.derivative(rational, 0)
    return ring_q.is_one(ring_q.gcd(rational, derivative))


def _as_prime_polynomial(
    ring_p: UnivariatePolynomialRing[int],
    factor: Polynomial[int],
) -> Polynomial[int]:
    if not isinstance(factor, Polynomial):
        raise TypeError("a modular factor must be a polynomial")
    owner = factor.owner
    same_generator = owner.generators == ring_p.generators
    coefficients = owner.coefficients
    if (
        same_generator
        and isinstance(coefficients, PrimeField)
        and coefficients.modulus == _prime_field(ring_p).modulus
    ):
        return ring_p.sum(
            ring_p.monomial(exponents, coefficient)
            for exponents, coefficient in factor.terms
        )
    try:
        return reduce_mod_prime(ring_p, factor)
    except ModularPolynomialError as error:
        raise FactorizationFragmentError(
            error.detail,
            missing=_FACTOR_RING_MISSING,
        ) from error


def _build_factor_tree(
    ring_p: UnivariatePolynomialRing[int],
    factors: tuple[Polynomial[int], ...],
) -> _FactorTree:
    if len(factors) == 1:
        return _FactorTree(factors[0], None)
    middle = len(factors) // 2
    left = _build_factor_tree(ring_p, factors[:middle])
    right = _build_factor_tree(ring_p, factors[middle:])
    return _FactorTree(
        ring_p.mul(left.product, right.product),
        (left, right),
    )


def _lift_two_factors(
    ring_z: PolynomialRing[int],
    ring_p: UnivariatePolynomialRing[int],
    node_polynomial: Polynomial[int],
    left_modular: Polynomial[int],
    right_modular: Polynomial[int],
    precision: int,
) -> tuple[Polynomial[int], Polynomial[int]]:
    """Lift one coprime pair from precision one to ``precision``."""
    prime = _prime_field(ring_p).modulus
    gcd, left_coefficient, right_coefficient = ring_p.xgcd(
        left_modular, right_modular
    )
    if not ring_p.is_one(gcd):
        raise AssertionError(
            "Hensel lifting needs coprime modular factors"
        )
    left = _integer_lift(ring_z, left_modular)
    right = _integer_lift(ring_z, right_modular)
    if not congruent_mod(
        ring_z.sub(node_polynomial, ring_z.mul(left, right)),
        ring_z.zero(),
        prime,
    ):
        raise AssertionError(
            "the Hensel pair does not match its node polynomial modulo p"
        )
    for level in range(1, precision):
        step = prime**level
        modulus = step * prime
        difference = ring_z.sub(
            node_polynomial, ring_z.mul(left, right)
        )
        divided = ring_z.exact_div(
            difference, ring_z.constant(step)
        )
        error = reduce_mod_prime(ring_p, divided)
        delta_left = ring_p.divmod(
            ring_p.mul(right_coefficient, error), left_modular
        )[1]
        delta_right = ring_p.divmod(
            ring_p.mul(left_coefficient, error), right_modular
        )[1]
        left = _reduce_coefficients(
            ring_z,
            ring_z.add(
                left,
                _scaled_integer_lift(
                    ring_z, _integer_lift(ring_z, delta_left), step, modulus
                ),
            ),
            modulus,
        )
        right = _reduce_coefficients(
            ring_z,
            ring_z.add(
                right,
                _scaled_integer_lift(
                    ring_z,
                    _integer_lift(ring_z, delta_right),
                    step,
                    modulus,
                ),
            ),
            modulus,
        )
        if not congruent_mod(
            ring_z.sub(node_polynomial, ring_z.mul(left, right)),
            ring_z.zero(),
            modulus,
        ):
            raise AssertionError(
                "the Hensel step does not preserve the modular congruence"
            )
    return left, right


def _lift_tree(
    ring_z: PolynomialRing[int],
    ring_p: UnivariatePolynomialRing[int],
    tree: _FactorTree,
    node_polynomial: Polynomial[int],
    precision: int,
) -> tuple[Polynomial[int], ...]:
    if tree.children is None:
        return (node_polynomial,)
    left_tree, right_tree = tree.children
    left, right = _lift_two_factors(
        ring_z,
        ring_p,
        node_polynomial,
        left_tree.product,
        right_tree.product,
        precision,
    )
    return _lift_tree(ring_z, ring_p, left_tree, left, precision) + _lift_tree(
        ring_z, ring_p, right_tree, right, precision
    )


def hensel_lift_factorization(
    ring_z: PolynomialRing[int],
    value: Polynomial[int],
    prime: int,
    factors: tuple[Polynomial[int], ...],
    precision: int,
    budget: FactorizationBudget = FactorizationBudget(),
) -> tuple[Polynomial[int], ...]:
    """Lift a complete modular factorization of a primitive squarefree ``f``.

    The input ``value`` is primitive, squarefree, nonconstant and has positive
    leading coefficient ``a``.  ``prime`` is a proven 64-bit prime not dividing
    ``a``, ``factors`` is a complete tuple of pairwise distinct monic
    irreducible factors of ``(value / a) mod prime``, and ``precision`` is a
    positive integer.  The return value is the tuple of monic ``G_i`` with
    coefficients in ``[0, prime**precision)`` satisfying

        value == a * G_1 * ... * G_r  (mod prime**precision)

    and ``sum(deg(G_i)) == deg(value)``.  The congruences are checked at every
    internal lifting step and again at the end.  The tuple order follows the
    supplied factor order; it is not a canonical factor order.  The function
    validates completeness, monicity, pairwise distinctness and pairwise
    coprimality of the supplied factors; irreducibility is a caller precondition
    that the later recombination and the independent checker verify rather than
    a property this congruence lift needs.
    """
    if not isinstance(budget, FactorizationBudget):
        raise TypeError("a factorization budget is required")
    _require_z_ring(ring_z, "Hensel lifting")
    if not ring_z.contains(value):
        raise FactorizationFragmentError(
            "the value belongs to another polynomial ring",
            missing=_RING_OWNERSHIP_MISSING,
        )
    if value.is_zero():
        raise FactorizationFragmentError(
            "Hensel lifting needs a nonzero polynomial",
            missing=_NONZERO_POLYNOMIAL_MISSING,
        )
    degree = ring_z.degree(value, 0)
    if degree == 0:
        raise FactorizationFragmentError(
            "Hensel lifting needs a nonconstant polynomial",
            missing=_NONCONSTANT_POLYNOMIAL_MISSING,
        )
    leading = ring_z.coefficient(value, (degree,))
    if leading <= 0:
        raise FactorizationFragmentError(
            "Hensel lifting needs a positive leading coefficient",
            missing=_POSITIVE_LEADING_MISSING,
        )
    if not ring_z.coefficients.is_one(ring_z.content(value)):
        raise FactorizationFragmentError(
            "Hensel lifting needs a primitive polynomial",
            missing=_PRIMITIVE_SQUAREFREE_MISSING,
        )
    if not _is_squarefree_over_z(ring_z, value):
        raise FactorizationFragmentError(
            "Hensel lifting needs a squarefree polynomial",
            missing=_PRIMITIVE_SQUAREFREE_MISSING,
        )
    if isinstance(prime, bool) or not isinstance(prime, int):
        raise TypeError("a Hensel prime must be an integer")
    if prime < 2 or prime >= _UINT64_LIMIT or not is_prime64(prime):
        raise FactorizationFragmentError(
            "Hensel lifting needs a proven prime below 2**64",
            missing=_PRIME_MODULUS_MISSING,
        )
    if leading % prime == 0:
        raise FactorizationFragmentError(
            "the Hensel prime divides the leading coefficient",
            missing=_APPLICABLE_PRIME_MISSING,
        )
    if isinstance(precision, bool) or not isinstance(precision, int):
        raise TypeError("a Hensel precision must be an integer")
    if precision <= 0:
        raise FactorizationFragmentError(
            "Hensel lifting needs a positive precision",
            missing=_POSITIVE_PRECISION_MISSING,
        )
    if precision > budget.max_hensel_precision:
        raise FactorizationBudgetError(
            "the requested Hensel precision exceeds the budget",
            missing=_HENSEL_PRECISION_MISSING,
        )
    if not isinstance(factors, tuple):
        raise TypeError("Hensel lifting needs a tuple of modular factors")
    if not factors:
        raise FactorizationFragmentError(
            "Hensel lifting needs a complete modular factorization",
            missing=_COMPLETE_FACTORIZATION_MISSING,
        )
    ring_p = _prime_ring_of(ring_z, prime)
    modular_factors = tuple(
        _as_prime_polynomial(ring_p, factor) for factor in factors
    )
    for factor in modular_factors:
        if factor.is_zero() or ring_p.degree(factor, 0) < 1:
            raise FactorizationFragmentError(
                "every modular factor must be nonconstant",
                missing=_NONCONSTANT_FACTORS_MISSING,
            )
        factor_degree = ring_p.degree(factor, 0)
        if not ring_p.coefficients.is_one(
            ring_p.coefficient(factor, (factor_degree,))
        ):
            raise FactorizationFragmentError(
                "every modular factor must be monic",
                missing=_MONIC_FACTORS_MISSING,
            )
    for index, factor in enumerate(modular_factors):
        for other in modular_factors[index + 1 :]:
            if ring_p.equal(factor, other):
                raise FactorizationFragmentError(
                    "the modular factors must be pairwise distinct",
                    missing=_DISTINCT_FACTORS_MISSING,
                )
            if not ring_p.is_one(ring_p.gcd(factor, other)):
                raise FactorizationFragmentError(
                    "the modular factors must be pairwise coprime",
                    missing=_COPRIME_FACTORS_MISSING,
                )
    value_mod_prime = reduce_mod_prime(ring_p, value)
    if ring_p.degree(value_mod_prime, 0) != degree:
        raise AssertionError(
            "a prime not dividing the leading coefficient changed the degree"
        )
    inverse_leading = ring_p.coefficients.inv(
        ring_p.coefficient(value_mod_prime, (degree,))
    )
    normalized = ring_p.mul(
        ring_p.constant(inverse_leading), value_mod_prime
    )
    modular_product = ring_p.one()
    for factor in modular_factors:
        modular_product = ring_p.mul(modular_product, factor)
    if not ring_p.equal(modular_product, normalized):
        raise FactorizationFragmentError(
            "the modular factors are not a complete factorization of value/a",
            missing=_COMPLETE_FACTORIZATION_MISSING,
        )
    modulus = prime**precision
    inverse_leading_integer = pow(leading, -1, modulus)
    node_polynomial = _scaled_integer_lift(
        ring_z, value, inverse_leading_integer, modulus
    )
    if not congruent_mod(
        ring_z.mul(ring_z.constant(leading), node_polynomial),
        value,
        modulus,
    ):
        raise AssertionError(
            "the normalized node polynomial does not match value/a modulo p**k"
        )
    tree = _build_factor_tree(ring_p, modular_factors)
    lifted = _lift_tree(
        ring_z, ring_p, tree, node_polynomial, precision
    )
    product = ring_z.one()
    degrees = 0
    for factor in lifted:
        factor_degree = ring_z.degree(factor, 0)
        if factor_degree < 1:
            raise AssertionError("a lifted factor must be nonconstant")
        if not ring_z.coefficients.is_one(
            ring_z.coefficient(factor, (factor_degree,))
        ):
            raise AssertionError("a lifted factor must be monic")
        for _, coefficient in factor.terms:
            if not 0 <= coefficient < modulus:
                raise AssertionError(
                    "a lifted coefficient is outside [0, p**precision)"
                )
        product = ring_z.mul(product, factor)
        degrees += factor_degree
    if degrees != degree:
        raise AssertionError(
            "the lifted factor degrees do not sum to the input degree"
        )
    if not congruent_mod(
        ring_z.mul(ring_z.constant(leading), product), value, modulus
    ):
        raise AssertionError(
            "the lifted factors do not reconstruct value modulo p**precision"
        )
    return lifted


def _ascending_primes() -> Iterator[int]:
    candidate = 2
    while candidate < _UINT64_LIMIT:
        if is_prime64(candidate):
            yield candidate
        candidate += 1 if candidate == 2 else 2


def _least_precision(prime: int, bound: int) -> int:
    """The least ``k >= 1`` with ``prime**k > bound``."""
    precision = 1
    power = prime
    while power <= bound:
        precision += 1
        power *= prime
    return precision


def hensel_witness_for_radical(
    ring_q: UnivariatePolynomialRing[Fraction],
    radical: Polynomial[Fraction],
    budget: FactorizationBudget = FactorizationBudget(),
) -> HenselLift:
    """Build a Hensel witness for a monic squarefree ``Q[x]`` radical.

    ``radical`` is the product of the distinct claimed factors of a later
    factorization: monic, squarefree, nonzero and nonconstant.  It is converted
    to its primitive integer form ``R`` with positive leading coefficient
    ``a``.  The primes are scanned in ascending order; for each prime the
    function independently reduces ``R/a`` modulo ``p``, checks that the
    reduction is squarefree, factors it with Berlekamp, and lifts to the least
    precision ``k`` with ``p**k > 2 * coefficient_bound(R)``.  The first prime
    whose precision fits the budget produces ``HenselLift(p, k, lifted)``.

    The caller's factor data is not accepted at all; the modular factorization
    is recomputed here.  If no prime is found within ``max_prime_trials`` the
    function raises ``FactorizationBudgetError`` with
    ``missing={"factorization_budget"}``; if every applicable prime needs more
    than ``max_hensel_precision`` it raises with
    ``missing={"hensel_precision"}``.  A non-monic, non-squarefree, zero or
    constant radical raises ``FactorizationFragmentError``.
    """
    if not isinstance(budget, FactorizationBudget):
        raise TypeError("a factorization budget is required")
    _require_q_ring(ring_q, "the Hensel witness")
    if not ring_q.contains(radical):
        raise FactorizationFragmentError(
            "the radical belongs to another polynomial ring",
            missing=_RING_OWNERSHIP_MISSING,
        )
    if radical.is_zero():
        raise FactorizationFragmentError(
            "the Hensel witness needs a nonzero radical",
            missing=_NONZERO_POLYNOMIAL_MISSING,
        )
    radical_degree = ring_q.degree(radical, 0)
    if radical_degree == 0:
        raise FactorizationFragmentError(
            "the Hensel witness needs a nonconstant radical",
            missing=_NONCONSTANT_POLYNOMIAL_MISSING,
        )
    if not ring_q.coefficients.is_one(
        ring_q.coefficient(radical, (radical_degree,))
    ):
        raise FactorizationFragmentError(
            "the Hensel witness needs a monic radical",
            missing=_MONIC_POLYNOMIAL_MISSING,
        )
    derivative = ring_q.derivative(radical, 0)
    if not ring_q.is_one(ring_q.gcd(radical, derivative)):
        raise FactorizationFragmentError(
            "the Hensel witness needs a squarefree radical",
            missing=_PRIMITIVE_SQUAREFREE_MISSING,
        )
    form = integer_primitive_form(ring_q, radical)
    primitive = form.primitive
    ring_z = primitive.owner
    _require_z_ring(ring_z, "the Hensel witness")
    degree = ring_z.degree(primitive, 0)
    leading = ring_z.coefficient(primitive, (degree,))
    if leading <= 0:
        raise AssertionError(
            "a primitive form with positive leading coefficient was expected"
        )
    bound = 2 * coefficient_bound(primitive)
    saw_precision_limit = False
    trials = 0
    primes = _ascending_primes()
    while trials < budget.max_prime_trials:
        prime = next(primes)
        trials += 1
        if leading % prime == 0:
            continue
        ring_p = _prime_ring_of(ring_z, prime)
        reduced = reduce_mod_prime(ring_p, primitive)
        reduced_degree = ring_p.degree(reduced, 0)
        if reduced_degree != degree:
            continue
        inverse_leading = ring_p.coefficients.inv(
            ring_p.coefficient(reduced, (reduced_degree,))
        )
        normalized = ring_p.mul(
            ring_p.constant(inverse_leading), reduced
        )
        if not is_squarefree_mod_prime(ring_p, normalized):
            continue
        precision = _least_precision(prime, bound)
        if precision > budget.max_hensel_precision:
            saw_precision_limit = True
            continue
        try:
            modular_factors = factor_squarefree_mod_prime(
                ring_p, normalized, budget.modular
            )
        except ModularFactorizationError as error:
            raise FactorizationBudgetError(
                error.detail,
                missing=_FACTORIZATION_BUDGET_MISSING,
            ) from error
        lifted = hensel_lift_factorization(
            ring_z,
            primitive,
            prime,
            modular_factors,
            precision,
            budget,
        )
        return HenselLift(
            prime=prime,
            precision=precision,
            lifted=lifted,
        )
    if saw_precision_limit:
        raise FactorizationBudgetError(
            "every applicable prime needs more Hensel precision than the budget",
            missing=_HENSEL_PRECISION_MISSING,
        )
    raise FactorizationBudgetError(
        "no applicable prime was found within the prime-trial budget",
        missing=_FACTORIZATION_BUDGET_MISSING,
    )


__all__ = [
    "FactorizationBudget",
    "FactorizationBudgetError",
    "FactorizationError",
    "FactorizationFragmentError",
    "HenselLift",
    "hensel_lift_factorization",
    "hensel_witness_for_radical",
]
