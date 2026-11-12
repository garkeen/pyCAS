"""Rational-residue logarithmic integration over ``Q(x)``.

This module is the I0-L0/L1 low-level slice: the exact logarithmic part of a
rational function integral when every residue is rational.  It publishes the
result records, the residue polynomial and the integration algorithm.  It
publishes no specification, certificate, checker, operation, bootstrap,
workflow or REPL entry; those belong to later slices, and the full I0
logarithmic part (algebraic residues, RootSum representations, real-log and
branch handling) remains open.

Algorithm
---------

Write ``f = P/Q`` in reduced form with ``Q`` monic.  Polynomial division gives

    f = q + A/Q,        deg(A) < deg(Q),

and the polynomial antiderivative of ``q`` (zero constant term) is one part of
the answer.  The proper fraction is reduced with the existing
``cas.algebra.hermite.hermite_reduce`` into

    A/Q = D(v) + A'/B,

where ``B`` is monic and squarefree and ``gcd(A', B) = 1``.  Hermite reduction
is not duplicated here.

For the squarefree remainder, define the residue polynomial

    R(y) = Res_x(B(x), A'(x) - y*B'(x))  in Q[y].

Because ``B`` is squarefree, the product formula for the resultant gives

    R(y) = product over B(alpha)=0 of (A'(alpha) - y*B'(alpha)),

so each factor is linear in ``y`` and the roots of ``R`` are exactly the
residues of ``A'/B``.  If ``R`` factors over ``Q`` into linear factors only,
then for every distinct rational residue ``c``

    g_c = monic gcd(B, A' - c*B')

and ``B = product_c g_c``.  Comparing principal parts at every root of ``B``
gives the exact identity

    A'/B = sum_c c * g_c'/g_c.

Consequently

    f = D(polynomial_part) + sum_{c != 0} c * D(g_c)/g_c,

where ``polynomial_part`` collects the antiderivative of ``q`` and Hermite's
``v``.  The terms with ``c = 0`` contribute no logarithm; they still take part
in the partition check of ``B``.  The emitted representation is a rational
function polynomial part plus a tuple of rational coefficients and monic
squarefree logarithm arguments.  It makes no claim about algebraic or
irrational residues.

The residue polynomial is computed exactly in a ``Q(y)`` tower: ``Y = Q[y]``
with a private, never-interned negative ``SymbolId``, ``K = Frac(Y)`` and
``X = K[x]``.  ``B``, ``A'`` and ``B'`` are embedded into ``X`` and the existing
univariate resultant is evaluated there.  The result is a rational function in
``y`` whose denominator must be the constant one; the monic numerator is the
residue polynomial.  The dummy symbol never appears in a log-term argument or
in the returned integral record, which are owned by the caller's ``Q[x]``.

``R`` is factored over ``Q`` with ``cas.algebra.factorization``.  An
irreducible factor of degree at least two is refused as a structured fragment
error: the rational-residue fragment excludes it and no partial result is
returned.  Under the declared preconditions the multiplicity of a rational
residue ``c`` in ``R`` equals ``deg(g_c)``; both the multiplicity equality and
the product decomposition of ``B`` are checked internally and a mismatch is an
``AssertionError`` (an implementation invariant, never a user-facing
mathematical refusal).  The final ``Q(x)`` identity is verified before the
record is returned.

Preconditions and refusal boundary
----------------------------------

``rational_log_integral`` accepts any reduced element of a rational function
field over ``Q[x]``; zero, constants and polynomials are handled by the same
pipeline.  ``residue_polynomial`` requires a monic squarefree denominator ``B``,
``deg(A) < deg(B)`` and ``gcd(A, B) = 1``.  Inputs outside these preconditions
raise ``LogarithmicIntegrationFragmentError`` with precise ``missing`` tokens.

``max_degree`` bounds the input rational function's numerator and denominator
degree and the denominator degree of a direct residue-polynomial request; it is
resource control, not mathematical data.  The nested ``FactorizationBudget`` is
passed unchanged to the factorization search.  Factorization budget exhaustion is re-raised as
``LogarithmicIntegrationBudgetError`` with the original ``missing`` tokens.
No exhaustion path returns a partial integral.

References
----------

The method is the rational-residue/Rothstein--Trager logarithmic part:
M. Rothstein, "A new algorithm for the integration of elementary functions",
*Proceedings of the 1976 ACM Symposium on Symbolic and Algebraic Computation*
(SYMSAC '76), 1976, and his 1976 MIT thesis *Algorithms for symbolic
integration and their applications*; B. Trager, "Algebraic factoring and
rational function integration", SYMSAC '76, 1976; D. Lazard, R. Rioboo and
B. Trager, "Integration of rational functions: rational computation of the
logarithmic part", *Journal of Symbolic Computation* 9 (1990), 113--116.
The surrounding design is M. Bronstein, *Symbolic Integration I: Transcendental
Functions*, 2nd edition, Springer 2005, §4.4 and Chapter 8, and K. Geddes,
S. Czapor and G. Labahn, *Algorithms for Computer Algebra*, Kluwer 1992, §11.2.
Reference implementations are FriCAS ``src/algebra/intrf.spad`` and Maxima
``src/risch.lisp``; they are used for algorithm structure only, not as a
correctness proof.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from cas.algebra.factorization import (
    FactorizationBudget,
    FactorizationBudgetError,
    FactorizationFragmentError,
    factor_polynomial_over_q,
    factorization_key,
)
from cas.algebra.hermite import hermite_reduce
from cas.algebra.polynomial import Polynomial, UnivariatePolynomialRing
from cas.algebra.rational import RationalFunction, RationalFunctionField
from cas.algebra.rationals import RationalField
from cas.foundation.ids import SymbolId

_FIELD_OWNERSHIP_MISSING = frozenset({"field_ownership"})
_RING_OWNERSHIP_MISSING = frozenset({"ring_ownership"})
_NONZERO_DENOMINATOR_MISSING = frozenset({"nonzero_denominator"})
_MONIC_DENOMINATOR_MISSING = frozenset({"monic_denominator"})
_SQUAREFREE_DENOMINATOR_MISSING = frozenset({"squarefree_denominator"})
_PROPER_FRACTION_MISSING = frozenset({"proper_fraction"})
_COPRIME_FRACTION_MISSING = frozenset({"coprime_fraction"})
_MAX_DEGREE_MISSING = frozenset({"max_degree"})
_ALGEBRAIC_LOGARITHMIC_PART_MISSING = frozenset(
    {"rational_residues", "algebraic_logarithmic_part"}
)


@dataclass(frozen=True, slots=True)
class LogarithmicIntegrationBudget:
    """Resource limits for the rational-residue logarithmic part.

    ``max_degree`` bounds the input rational function's numerator and
    denominator degree (and the denominator degree of a direct
    ``residue_polynomial`` request).  ``factorization`` is passed unchanged to
    the ``Q[y]`` factorization of the residue polynomial.
    Both are resource control, not mathematical data; booleans are rejected
    and the nested budget must be a ``FactorizationBudget``.
    """

    max_degree: int = 64
    factorization: FactorizationBudget = FactorizationBudget()

    def __post_init__(self) -> None:
        if isinstance(self.max_degree, bool) or not isinstance(
            self.max_degree, int
        ):
            raise TypeError("a logarithmic-integration degree bound must be an integer")
        if self.max_degree < 0:
            raise ValueError(
                "a logarithmic-integration degree bound cannot be negative"
            )
        if not isinstance(self.factorization, FactorizationBudget):
            raise TypeError(
                "a logarithmic-integration budget needs a factorization budget"
            )


class LogarithmicIntegrationError(ValueError):
    """A logarithmic-integration request is outside the declared fragment.

    ``detail`` is nonempty prose and ``missing`` is the structured capability,
    precondition or budget token.  The error is never a mathematical
    refutation: it states that no complete integral was produced under the
    stated assumptions.
    """

    def __init__(self, detail: str, *, missing: frozenset[str]) -> None:
        if not detail:
            raise ValueError("a logarithmic-integration error needs a detail")
        if not missing:
            raise ValueError("a logarithmic-integration error needs a missing token")
        super().__init__(detail)
        self.detail = detail
        self.missing = frozenset(missing)


class LogarithmicIntegrationFragmentError(LogarithmicIntegrationError):
    """The input leaves the declared rational-residue fragment."""


class LogarithmicIntegrationBudgetError(LogarithmicIntegrationError):
    """The declared resource budget is exhausted; no partial result exists."""


@dataclass(frozen=True, slots=True)
class RationalLogTerm:
    """One logarithmic term ``coefficient * log(argument)`` over ``Q(x)``.

    ``coefficient`` is a nonzero rational.  ``argument`` is monic, nonzero and
    nonconstant, squarefree, and owned by a univariate polynomial ring over
    ``Q``.  The record validates one term; distinct coefficients and pairwise
    coprime arguments across a collection are invariants of
    ``RationalLogIntegral``.
    """

    coefficient: Fraction
    argument: Polynomial[Fraction]

    def __post_init__(self) -> None:
        if not isinstance(self.coefficient, Fraction):
            raise TypeError("a logarithmic term needs a Fraction coefficient")
        if self.coefficient == 0:
            raise ValueError("a logarithmic term coefficient must be nonzero")
        if not isinstance(self.argument, Polynomial):
            raise TypeError("a logarithmic term needs a polynomial argument")
        owner = self.argument.owner
        if not isinstance(owner, UnivariatePolynomialRing) or not isinstance(
            owner.coefficients, RationalField
        ):
            raise TypeError(
                "a logarithmic term argument must be a univariate "
                "polynomial over Q"
            )
        if self.argument.is_zero():
            raise ValueError("a logarithmic term argument must be nonzero")
        degree = owner.degree(self.argument, 0)
        if degree < 1:
            raise ValueError("a logarithmic term argument must be nonconstant")
        if not owner.coefficients.is_one(
            owner.coefficient(self.argument, (degree,))
        ):
            raise ValueError("a logarithmic term argument must be monic")
        derivative = owner.derivative(self.argument, 0)
        if not owner.is_one(owner.gcd(self.argument, derivative)):
            raise ValueError(
                "a logarithmic term argument must be squarefree"
            )


def _term_key(term: RationalLogTerm) -> tuple[Fraction, tuple[int, tuple[Fraction, ...]]]:
    return (term.coefficient, factorization_key(term.argument))


@dataclass(frozen=True, slots=True)
class RationalLogIntegral:
    """The full rational-residue integral of one ``Q(x)`` element.

    The meaning is exactly

        value = D(polynomial_part) + sum(term.coefficient * D(arg)/arg).

    The record claims no algebraic or irrational residue.  Log terms are sorted
    by ``(coefficient, argument structural key)``; their coefficients are
    distinct, their arguments share one ``Q[x]`` ring and are pairwise coprime,
    and ``polynomial_part`` belongs to the same field.  ``polynomial_part`` is
    the non-logarithmic rational part; Hermite reduction may give it a
    nonconstant denominator, so it need not be a polynomial.
    """

    polynomial_part: RationalFunction[Fraction]
    log_terms: tuple[RationalLogTerm, ...]

    def __post_init__(self) -> None:
        part = self.polynomial_part
        if not isinstance(part, RationalFunction):
            raise TypeError(
                "a rational logarithmic integral needs a rational-function part"
            )
        field = part.owner
        if not isinstance(field, RationalFunctionField):
            raise TypeError(
                "a rational logarithmic integral needs a rational-function field"
            )
        ring = field.polynomials
        if not isinstance(ring, UnivariatePolynomialRing) or not isinstance(
            ring.coefficients, RationalField
        ):
            raise TypeError(
                "a rational logarithmic integral needs a Q(x) field"
            )
        if not isinstance(self.log_terms, tuple):
            raise TypeError("a rational logarithmic integral needs a term tuple")
        seen_coefficients: set[Fraction] = set()
        checked: list[RationalLogTerm] = []
        for term in self.log_terms:
            if not isinstance(term, RationalLogTerm):
                raise TypeError("a logarithmic integral carries log terms")
            if term.argument.owner is not ring:
                raise ValueError(
                    "every logarithmic-term argument must belong to the "
                    "integral's polynomial ring"
                )
            if term.coefficient in seen_coefficients:
                raise ValueError(
                    "a logarithmic coefficient appears more than once"
                )
            seen_coefficients.add(term.coefficient)
            for previous in checked:
                if not ring.is_one(
                    ring.gcd(previous.argument, term.argument)
                ):
                    raise ValueError(
                        "logarithmic-term arguments must be pairwise coprime"
                    )
            checked.append(term)
        object.__setattr__(
            self,
            "log_terms",
            tuple(sorted(checked, key=_term_key)),
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


def _residue_ring(
    ring_q: UnivariatePolynomialRing[Fraction],
) -> UnivariatePolynomialRing[Fraction]:
    """A fresh ``Q[y]`` ring on a private, never-interned negative symbol.

    The symbol only names the residue variable inside this module.  It is
    chosen coprime to every generator of ``ring_q`` and is not part of any
    world or frame.  Only the local residue-polynomial ring uses it; log-term
    arguments and the returned integral record are owned by the caller's
    ``Q[x]``.
    """
    taken = set(ring_q.generators)
    candidate = -1
    while candidate in taken:
        candidate -= 1
    return UnivariatePolynomialRing(SymbolId(candidate), RationalField())


def _embed_polynomial(
    tower: UnivariatePolynomialRing[RationalFunction[Fraction]],
    residue_ring: UnivariatePolynomialRing[Fraction],
    field: RationalFunctionField[Fraction],
    ring: UnivariatePolynomialRing[Fraction],
    value: Polynomial[Fraction],
) -> Polynomial[RationalFunction[Fraction]]:
    """Embed one ``Q[x]`` polynomial into ``Q(y)[x]`` as constants in ``y``."""
    return tower.sum(
        tower.monomial(
            (exponents[0],),
            field.of_polynomial(residue_ring.constant(coefficient)),
        )
        for exponents, coefficient in value.terms
    )


def residue_polynomial(
    ring_q: UnivariatePolynomialRing[Fraction],
    denominator: Polynomial[Fraction],
    numerator: Polynomial[Fraction],
    budget: LogarithmicIntegrationBudget = LogarithmicIntegrationBudget(),
) -> Polynomial[Fraction]:
    """The monic residue polynomial ``Res_x(B, A - y*B')`` in a fresh ``Q[y]``.

    Preconditions: ``B`` is monic, squarefree, nonzero and owned by ``ring_q``;
    ``A`` is owned by ``ring_q``, ``deg(A) < deg(B)`` and ``gcd(A, B) = 1``.
    For the constant denominator ``B = 1`` (which forces ``A = 0``) the empty
    resultant product is ``1``.  The returned polynomial is monic; its owner is
    a private ``Q[y]`` ring whose generator is a local dummy symbol that is
    never interned and never appears in any log-term argument.

    The computation is exact: a ``Q(y)`` tower ``Y = Q[y]``,
    ``K = Frac(Y)``, ``X = K[x]`` receives the embedded ``B``, ``A`` and
    ``B'``; the existing univariate resultant is evaluated in ``X``; the
    result must have constant denominator one and its numerator is normalised
    monic.  ``budget.max_degree`` bounds ``deg(B)``.
    """
    if not isinstance(budget, LogarithmicIntegrationBudget):
        raise TypeError("a logarithmic-integration budget is required")
    _require_q_ring(ring_q, "residue-polynomial computation")
    if not ring_q.contains(denominator):
        raise LogarithmicIntegrationFragmentError(
            "the denominator belongs to another polynomial ring",
            missing=_RING_OWNERSHIP_MISSING,
        )
    if not ring_q.contains(numerator):
        raise LogarithmicIntegrationFragmentError(
            "the numerator belongs to another polynomial ring",
            missing=_RING_OWNERSHIP_MISSING,
        )
    if denominator.is_zero():
        raise LogarithmicIntegrationFragmentError(
            "the residue polynomial needs a nonzero denominator",
            missing=_NONZERO_DENOMINATOR_MISSING,
        )
    denominator_degree = ring_q.degree(denominator, 0)
    if denominator_degree > budget.max_degree:
        raise LogarithmicIntegrationBudgetError(
            "the denominator degree exceeds the logarithmic-integration budget",
            missing=_MAX_DEGREE_MISSING,
        )
    if not ring_q.coefficients.is_one(
        ring_q.coefficient(denominator, (denominator_degree,))
    ):
        raise LogarithmicIntegrationFragmentError(
            "the residue polynomial needs a monic denominator",
            missing=_MONIC_DENOMINATOR_MISSING,
        )
    derivative = ring_q.derivative(denominator, 0)
    if not ring_q.is_one(ring_q.gcd(denominator, derivative)):
        raise LogarithmicIntegrationFragmentError(
            "the residue polynomial needs a squarefree denominator",
            missing=_SQUAREFREE_DENOMINATOR_MISSING,
        )
    if ring_q.degree(numerator, 0) >= denominator_degree:
        raise LogarithmicIntegrationFragmentError(
            "the residue polynomial needs a proper fraction",
            missing=_PROPER_FRACTION_MISSING,
        )
    if not ring_q.is_one(ring_q.gcd(numerator, denominator)):
        raise LogarithmicIntegrationFragmentError(
            "the residue polynomial needs a coprime fraction",
            missing=_COPRIME_FRACTION_MISSING,
        )
    residue_ring = _residue_ring(ring_q)
    if denominator_degree == 0:
        return residue_ring.one()
    field = RationalFunctionField(residue_ring)
    tower = UnivariatePolynomialRing(ring_q.generators[0], field)
    embedded_denominator = _embed_polynomial(
        tower, residue_ring, field, ring_q, denominator
    )
    embedded_numerator = _embed_polynomial(
        tower, residue_ring, field, ring_q, numerator
    )
    embedded_derivative = _embed_polynomial(
        tower, residue_ring, field, ring_q, derivative
    )
    y = tower.constant(field.of_polynomial(residue_ring.generator(0)))
    shifted = tower.sub(
        embedded_numerator, tower.mul(y, embedded_derivative)
    )
    resultant = tower.resultant(embedded_denominator, shifted)
    if not residue_ring.is_one(resultant.denominator):
        raise AssertionError(
            "the residue resultant does not have a constant denominator"
        )
    return residue_ring.monic(resultant.numerator)


def _factor_residue_polynomial(
    residue: Polynomial[Fraction],
    budget: LogarithmicIntegrationBudget,
) -> tuple[tuple[Fraction, int], ...]:
    """The rational roots of a monic residue polynomial with multiplicities.

    Any irreducible factor of degree at least two is refused before a partial
    root list is produced.
    """
    ring = residue.owner
    if not isinstance(ring, UnivariatePolynomialRing):
        raise AssertionError("a residue polynomial must have a ring owner")
    try:
        factorization = factor_polynomial_over_q(
            ring, residue, budget.factorization
        )
    except FactorizationBudgetError as error:
        raise LogarithmicIntegrationBudgetError(
            error.detail, missing=error.missing
        ) from error
    except FactorizationFragmentError as error:
        raise AssertionError(
            "the residue polynomial factorization left its fragment"
        ) from error
    if not ring.coefficients.is_one(factorization.unit):
        raise AssertionError(
            "a monic residue polynomial must factor with unit one"
        )
    roots: list[tuple[Fraction, int]] = []
    for factor, multiplicity in factorization.factors:
        degree = ring.degree(factor, 0)
        if degree >= 2:
            raise LogarithmicIntegrationFragmentError(
                "an irreducible residue factor has degree at least two; "
                "rational residues and the algebraic logarithmic part are "
                "outside this fragment",
                missing=_ALGEBRAIC_LOGARITHMIC_PART_MISSING,
            )
        if degree != 1:
            raise AssertionError("a factorization factor must be nonconstant")
        roots.append((-ring.coefficient(factor, (0,)), multiplicity))
    return tuple(roots)


def _log_partition(
    ring: UnivariatePolynomialRing[Fraction],
    denominator: Polynomial[Fraction],
    numerator: Polynomial[Fraction],
    roots: tuple[tuple[Fraction, int], ...],
) -> tuple[RationalLogTerm, ...]:
    """Build ``g_c`` for every rational residue and check the partition of ``B``."""
    derivative = ring.derivative(denominator, 0)
    arguments: list[Polynomial[Fraction]] = []
    terms: list[RationalLogTerm] = []
    for coefficient, multiplicity in roots:
        shifted = ring.sub(
            numerator,
            ring.mul(ring.constant(coefficient), derivative),
        )
        argument = ring.monic(ring.gcd(denominator, shifted))
        if ring.degree(argument, 0) != multiplicity:
            raise AssertionError(
                "a rational residue multiplicity does not match its "
                "gcd degree"
            )
        arguments.append(argument)
        if coefficient != 0:
            terms.append(RationalLogTerm(coefficient, argument))
    product = ring.one()
    for argument in arguments:
        product = ring.mul(product, argument)
    if not ring.equal(product, denominator):
        raise AssertionError(
            "the rational-residue gcd partition does not reconstruct "
            "the squarefree denominator"
        )
    for index, argument in enumerate(arguments):
        for other in arguments[index + 1 :]:
            if not ring.is_one(ring.gcd(argument, other)):
                raise AssertionError(
                    "the rational-residue gcd partition is not pairwise coprime"
                )
    return tuple(terms)


def _verify_identity(
    field: RationalFunctionField[Fraction],
    value: RationalFunction[Fraction],
    polynomial_part: RationalFunction[Fraction],
    terms: tuple[RationalLogTerm, ...],
) -> None:
    ring = field.polynomials
    total = field.derivative(polynomial_part)
    for term in terms:
        log_derivative = field.fraction(
            ring.mul(
                ring.constant(term.coefficient),
                ring.derivative(term.argument, 0),
            ),
            term.argument,
        )
        total = field.add(total, log_derivative)
    if not field.equal(total, value):
        raise AssertionError(
            "the logarithmic decomposition does not reconstruct its input"
        )


def rational_log_integral(
    field: RationalFunctionField[Fraction],
    value: RationalFunction[Fraction],
    budget: LogarithmicIntegrationBudget = LogarithmicIntegrationBudget(),
) -> RationalLogIntegral:
    """Integrate one ``Q(x)`` element when all residues are rational.

    The algorithm divides out the polynomial part, integrates it with zero
    constant, calls the existing Hermite reduction for the proper fraction,
    computes and factors the residue polynomial, builds the rational logarithm
    terms and verifies the exact ``Q(x)`` identity before returning.  Zero,
    constants and polynomials take the same path and return a polynomial part
    with no log terms.

    Inputs with a non-rational residue raise
    ``LogarithmicIntegrationFragmentError`` with
    ``{"rational_residues", "algebraic_logarithmic_part"}``; a numerator or
    denominator degree above ``budget.max_degree`` or an exhausted
    factorization budget raises ``LogarithmicIntegrationBudgetError``.  Neither
    path returns a partial record.
    """
    if not isinstance(budget, LogarithmicIntegrationBudget):
        raise TypeError("a logarithmic-integration budget is required")
    if not isinstance(field, RationalFunctionField):
        raise TypeError("a rational logarithmic integral needs a Q(x) field")
    ring = field.polynomials
    if not isinstance(ring, UnivariatePolynomialRing) or not isinstance(
        ring.coefficients, RationalField
    ):
        raise TypeError("a rational logarithmic integral needs a Q(x) field")
    if not field.contains(value):
        raise LogarithmicIntegrationFragmentError(
            "the value belongs to another rational-function field",
            missing=_FIELD_OWNERSHIP_MISSING,
        )
    if (
        max(
            ring.degree(value.numerator, 0),
            ring.degree(value.denominator, 0),
        )
        > budget.max_degree
    ):
        raise LogarithmicIntegrationBudgetError(
            "the input numerator or denominator degree exceeds the "
            "logarithmic-integration budget",
            missing=_MAX_DEGREE_MISSING,
        )
    quotient, proper_numerator = ring.divmod(
        value.numerator, value.denominator
    )
    polynomial_part = field.of_polynomial(
        ring.antiderivative(quotient, 0)
    )
    if proper_numerator.is_zero():
        return RationalLogIntegral(polynomial_part, ())
    reduction = hermite_reduce(
        field, field.fraction(proper_numerator, value.denominator)
    )
    polynomial_part = field.add(polynomial_part, reduction.polynomial_part)
    remainder = reduction.remainder
    if remainder.numerator.is_zero():
        return RationalLogIntegral(polynomial_part, ())
    denominator = remainder.denominator
    numerator = remainder.numerator
    residue = residue_polynomial(ring, denominator, numerator, budget)
    roots = _factor_residue_polynomial(residue, budget)
    terms = _log_partition(ring, denominator, numerator, roots)
    _verify_identity(field, value, polynomial_part, terms)
    return RationalLogIntegral(polynomial_part, terms)


__all__ = [
    "LogarithmicIntegrationBudget",
    "LogarithmicIntegrationBudgetError",
    "LogarithmicIntegrationError",
    "LogarithmicIntegrationFragmentError",
    "RationalLogIntegral",
    "RationalLogTerm",
    "rational_log_integral",
    "residue_polynomial",
]
