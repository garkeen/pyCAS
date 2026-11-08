"""Multivariate polynomials over an explicit coefficient ring.

Representation: a canonical tuple of `(exponents, coefficient)` pairs. The
coefficient ring owns the coefficients, so no syntax term appears here.

The ring owns its members: an element records the ring that produced it and
every operation refuses an element from another ring. Comparison of elements
goes through the coefficient ring's `equal`, which is the authority — comparing
coefficients with Python `==` would bypass it.

Storage order is the ring's declared monomial order. It is part of the parent's
representation choice, not a hidden default of an algorithm.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field
from enum import StrEnum
from typing import Any, Generic, TypeVar, cast

from cas.algebra.linear import MatrixSpace
from cas.algebra.protocols import (
    CharacteristicZero,
    Euclidean,
    ExactDivision,
    Field,
    Ring,
)
from cas.foundation.ids import SymbolId

E = TypeVar("E")

Exponents = tuple[int, ...]

_SEAL = object()


class MonomialOrder(StrEnum):
    """A declared ordering of monomials with a fixed number of variables."""

    LEX = "lex"
    GRLEX = "grlex"
    GREVLEX = "grevlex"

    def key(self, exponents: Exponents) -> tuple[object, ...]:
        if self is MonomialOrder.LEX:
            return (exponents,)
        degree = sum(exponents)
        if self is MonomialOrder.GRLEX:
            return (degree, exponents)
        return (degree, tuple(-exponent for exponent in reversed(exponents)))


@dataclass(frozen=True, slots=True, eq=False)
class Polynomial(Generic[E]):
    """A polynomial owned by one ring.

    `eq=False` on purpose: two elements are equal when the owning ring says so,
    not when Python compares their internal tuples. The seal makes the canonical
    form unrepresentable-by-hand: only `_make` issues elements, so terms are
    always sorted, duplicate-free and free of zero coefficients.
    """

    owner: PolynomialRing[E]
    terms: tuple[tuple[Exponents, E], ...]
    _seal: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._seal is not _SEAL:
            raise ValueError("a polynomial is issued only by its ring")

    def is_zero(self) -> bool:
        return not self.terms


class PolynomialRing(Ring[Polynomial[E]], Generic[E]):
    """`K[x₁,…,xₙ]` for a fixed coefficient ring `K`."""

    __slots__ = ("_generators", "_coefficients", "_order")

    def __init__(
        self,
        generators: tuple[SymbolId, ...],
        coefficients: Ring[E],
        order: MonomialOrder = MonomialOrder.LEX,
    ) -> None:
        if not generators:
            raise ValueError("a polynomial ring needs at least one generator")
        if len(set(generators)) != len(generators):
            raise ValueError("polynomial generators must be distinct")
        if not isinstance(coefficients, Ring):
            raise TypeError("polynomial coefficients must form a ring")
        if not isinstance(order, MonomialOrder):
            raise TypeError("a polynomial ring needs a monomial order")
        self._generators = tuple(generators)
        self._coefficients = coefficients
        self._order = order

    @property
    def generators(self) -> tuple[SymbolId, ...]:
        return self._generators

    @property
    def coefficients(self) -> Ring[E]:
        return self._coefficients

    @property
    def monomial_order(self) -> MonomialOrder:
        return self._order

    @property
    def parent_kind(self) -> str:
        return "polynomial"

    @property
    def parent_requires_base(self) -> bool:
        return True

    @property
    def parent_options(self) -> tuple[tuple[str, str], ...]:
        return (("monomial_order", self._order.value),)

    @property
    def characteristic(self) -> int:
        """The base characteristic, or -1 when the base does not declare one."""
        return 0 if self._coefficients.characteristic == 0 else -1

    def div_int(self, value: Polynomial[E], factor: int) -> Polynomial[E]:
        """Divide every coefficient by a nonzero integer."""
        self._own(value)
        coefficients = self._coefficients
        if not isinstance(coefficients, CharacteristicZero):
            raise TypeError(
                "integer division needs characteristic-zero coefficients"
            )
        return self._make(
            {
                exponents: coefficients.div_int(coefficient, factor)
                for exponents, coefficient in value.terms
            }
        )

    # --- ownership ---

    def contains(self, value: object) -> bool:
        return isinstance(value, Polynomial) and value.owner is self

    def _own(self, value: Polynomial[E]) -> None:
        if value.owner is not self:
            raise ValueError("a polynomial belongs to another ring")

    def _check_exponents(self, exponents: Exponents) -> None:
        if len(exponents) != len(self._generators):
            raise ValueError(
                f"expected {len(self._generators)} exponents, got {len(exponents)}"
            )
        if any(exponent < 0 for exponent in exponents):
            raise ValueError("monomial exponents must be nonnegative")

    def _check_index(self, index: int) -> None:
        if not 0 <= index < len(self._generators):
            raise IndexError(f"generator index out of range: {index}")

    def _make(self, terms: dict[Exponents, E]) -> Polynomial[E]:
        kept = tuple(
            (exponents, coefficient)
            for exponents, coefficient in sorted(
                terms.items(), key=lambda item: self._order.key(item[0])
            )
            if not self._coefficients.is_zero(coefficient)
        )
        return Polynomial(self, kept, _SEAL)

    # --- construction ---

    def zero(self) -> Polynomial[E]:
        return Polynomial(self, (), _SEAL)

    def one(self) -> Polynomial[E]:
        return self._make({(0,) * len(self._generators): self._coefficients.one()})

    def constant(self, coefficient: E) -> Polynomial[E]:
        if self._coefficients.is_zero(coefficient):
            return self.zero()
        return self._make({(0,) * len(self._generators): coefficient})

    def monomial(self, exponents: Exponents, coefficient: E) -> Polynomial[E]:
        self._check_exponents(exponents)
        return self._make({exponents: coefficient})

    def generator(self, index: int) -> Polynomial[E]:
        self._check_index(index)
        exponents = tuple(
            1 if position == index else 0
            for position in range(len(self._generators))
        )
        return self.monomial(exponents, self._coefficients.one())

    # --- ring operations ---

    def add(self, left: Polynomial[E], right: Polynomial[E]) -> Polynomial[E]:
        self._own(left)
        self._own(right)
        coefficients = self._coefficients
        terms = dict(left.terms)
        for exponents, coefficient in right.terms:
            terms[exponents] = coefficients.add(
                terms.get(exponents, coefficients.zero()), coefficient
            )
        return self._make(terms)

    def neg(self, value: Polynomial[E]) -> Polynomial[E]:
        self._own(value)
        coefficients = self._coefficients
        return self._make(
            {
                exponents: coefficients.neg(coefficient)
                for exponents, coefficient in value.terms
            }
        )

    def sum(self, values: Iterable[Polynomial[E]]) -> Polynomial[E]:
        """Collect every term once, then normalise the result once.

        Repeated `add` rebuilds and sorts a growing prefix polynomial at every
        step.  A bulk sum is the natural construction for the bridge and for
        callers that already hold a finite collection.
        """
        coefficients = self._coefficients
        terms: dict[Exponents, E] = {}
        for value in values:
            self._own(value)
            for exponents, coefficient in value.terms:
                current = terms.get(exponents)
                terms[exponents] = (
                    coefficient
                    if current is None
                    else coefficients.add(current, coefficient)
                )
        return self._make(terms)

    def mul(self, left: Polynomial[E], right: Polynomial[E]) -> Polynomial[E]:
        self._own(left)
        self._own(right)
        coefficients = self._coefficients
        terms: dict[Exponents, E] = {}
        zero = coefficients.zero()
        for left_exponents, left_coefficient in left.terms:
            for right_exponents, right_coefficient in right.terms:
                exponents = tuple(
                    first + second
                    for first, second in zip(left_exponents, right_exponents)
                )
                terms[exponents] = coefficients.add(
                    terms.get(exponents, zero),
                    coefficients.mul(left_coefficient, right_coefficient),
                )
        return self._make(terms)

    def equal(self, left: Polynomial[E], right: Polynomial[E]) -> bool:
        self._own(left)
        self._own(right)
        if len(left.terms) != len(right.terms):
            return False
        coefficients = self._coefficients
        for (left_exponents, left_coefficient), (
            right_exponents,
            right_coefficient,
        ) in zip(left.terms, right.terms):
            if left_exponents != right_exponents:
                return False
            if not coefficients.equal(left_coefficient, right_coefficient):
                return False
        return True

    # --- structure-specific queries and operations ---

    def is_constant(self, value: Polynomial[E]) -> bool:
        """Whether `value` is constant in this ring's generators."""
        self._own(value)
        zero = (0,) * len(self._generators)
        return all(exponents == zero for exponents, _ in value.terms)

    def is_nonzero_constant(self, value: Polynomial[E]) -> bool:
        """Whether `value` is a constant that is nonzero in the base structure.

        This is stronger than `not is_zero`: in `Q[a][x]`, the parameter `a`
        is a constant polynomial of the outer ring but is not globally nonzero
        for every parameter value.  Nested polynomial coefficient rings are
        checked recursively down to their base.  For a non-polynomial
        coefficient structure this only tests the zero member; a bridge that
        interprets members as functions must not treat that as global
        nonvanishing.
        """
        self._own(value)
        if not self.is_constant(value):
            return False
        coefficient = self.coefficient(
            value, (0,) * len(self._generators)
        )
        coefficients = self._coefficients
        if isinstance(coefficients, PolynomialRing):
            return coefficients.is_nonzero_constant(
                cast(Polynomial[Any], coefficient)
            )
        return not coefficients.is_zero(coefficient)

    def degree(self, value: Polynomial[E], index: int) -> int:
        """Degree in one generator; the zero polynomial has degree -1."""
        self._own(value)
        self._check_index(index)
        if not value.terms:
            return -1
        return max(exponents[index] for exponents, _ in value.terms)

    def coefficient(self, value: Polynomial[E], exponents: Exponents) -> E:
        self._own(value)
        self._check_exponents(exponents)
        for stored, coefficient in value.terms:
            if stored == exponents:
                return coefficient
        return self._coefficients.zero()

    def derivative(self, value: Polynomial[E], index: int) -> Polynomial[E]:
        """Formal derivative with respect to one generator."""
        self._own(value)
        self._check_index(index)
        coefficients = self._coefficients
        terms: dict[Exponents, E] = {}
        for exponents, coefficient in value.terms:
            power = exponents[index]
            if power == 0:
                continue
            lowered = tuple(
                exponent - (1 if position == index else 0)
                for position, exponent in enumerate(exponents)
            )
            terms[lowered] = coefficients.mul_int(coefficient, power)
        return self._make(terms)

    def pseudo_divmod(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> tuple[Polynomial[E], Polynomial[E], E]:
        """Pseudo-division in one generator over any commutative ring.

        Return `(quotient, remainder, multiplier)` with

            multiplier * left == quotient * right + remainder

        and `degree(remainder) < degree(right)`.  The multiplier is a power of
        the leading coefficient of `right`; no coefficient inverse is used, so
        this works over `Z[x]` and over polynomial coefficient rings.  The
        algorithm is the standard pseudo-division recurrence (Knuth, TAOCP
        vol. 2, §4.6.1; see also Geddes--Czapor--Labahn, *Algorithms for
        Computer Algebra*, §2.3).  Maxima's `src/rat3c.lisp` (`psquorem1`,
        `prem`) and FriCAS's `src/algebra/prs.spad` are the corresponding
        reference implementations.
        """
        self._own(left)
        self._own(right)
        if len(self._generators) != 1:
            raise ValueError("pseudo-division needs exactly one generator")
        if right.is_zero():
            raise ZeroDivisionError("polynomial division by zero")
        coefficients = self._coefficients
        if left.is_zero():
            return self.zero(), self.zero(), coefficients.one()
        divisor_degree = self.degree(right, 0)
        divisor_leading = self.coefficient(right, (divisor_degree,))
        quotient = self.zero()
        remainder = left
        multiplier = coefficients.one()
        while (
            not remainder.is_zero()
            and self.degree(remainder, 0) >= divisor_degree
        ):
            degree = self.degree(remainder, 0)
            leading = self.coefficient(remainder, (degree,))
            term = self.monomial((degree - divisor_degree,), leading)
            quotient = self.add(
                self.mul(self.constant(divisor_leading), quotient), term
            )
            remainder = self.sub(
                self.mul(self.constant(divisor_leading), remainder),
                self.mul(term, right),
            )
            multiplier = coefficients.mul(multiplier, divisor_leading)
        return quotient, remainder, multiplier

    def exact_div(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> Polynomial[E]:
        """Exact polynomial quotient in one generator.

        The coefficient structure must provide `div_exact`; a non-exact
        division raises instead of returning a truncated quotient.
        """
        self._own(left)
        self._own(right)
        if len(self._generators) != 1:
            raise ValueError("exact division needs exactly one generator")
        if right.is_zero():
            raise ZeroDivisionError("polynomial division by zero")
        coefficients = self._coefficients
        if not isinstance(coefficients, ExactDivision):
            raise TypeError(
                "exact polynomial division needs exact coefficient division"
            )
        divisor_degree = self.degree(right, 0)
        divisor_leading = self.coefficient(right, (divisor_degree,))
        quotient = self.zero()
        remainder = left
        while not remainder.is_zero():
            degree = self.degree(remainder, 0)
            if degree < divisor_degree:
                break
            leading = self.coefficient(remainder, (degree,))
            factor = coefficients.div_exact(leading, divisor_leading)
            term = self.monomial((degree - divisor_degree,), factor)
            quotient = self.add(quotient, term)
            remainder = self.sub(remainder, self.mul(term, right))
        if not remainder.is_zero():
            raise ValueError("the polynomial division is not exact")
        return quotient

    def content(self, value: Polynomial[E]) -> E:
        """The content of a univariate polynomial over a Euclidean ring.

        Over a field the content is the unit 1; over `Z` it is the nonnegative
        gcd of the coefficients.  Other coefficient structures have no declared
        content algorithm, so the request is refused rather than guessed.
        """
        self._own(value)
        if value.is_zero():
            return self._coefficients.zero()
        coefficients = self._coefficients
        if isinstance(coefficients, Euclidean):
            euclidean = cast("Euclidean[E]", coefficients)
            result = euclidean.zero()
            for _, coefficient in value.terms:
                result = euclidean.gcd(result, coefficient)
            return result
        if isinstance(coefficients, Field):
            return cast("Field[E]", coefficients).one()
        raise TypeError(
            "content needs Euclidean or field coefficients"
        )

    def primitive_part(self, value: Polynomial[E]) -> Polynomial[E]:
        """The primitive part `value / content(value)`."""
        self._own(value)
        if value.is_zero():
            return self.zero()
        content = self.content(value)
        if self._coefficients.is_one(content):
            return value
        if self._coefficients.is_zero(content):
            raise AssertionError("a nonzero polynomial has zero content")
        return self.exact_div(value, self.constant(content))

    def antiderivative(
        self,
        value: Polynomial[E],
        index: int,
    ) -> Polynomial[E]:
        """A polynomial antiderivative with zero constant term.

        The coefficient structure must be characteristic zero and provide
        division by a nonzero integer.  The result is one representative of the
        antiderivative class; the constant of integration is not invented.
        """
        self._own(value)
        self._check_index(index)
        coefficients = self._coefficients
        if not isinstance(coefficients, CharacteristicZero):
            raise TypeError(
                "polynomial integration needs characteristic-zero coefficients"
            )
        terms: dict[Exponents, E] = {}
        for exponents, coefficient in value.terms:
            power = exponents[index]
            raised = tuple(
                exponent + (1 if position == index else 0)
                for position, exponent in enumerate(exponents)
            )
            terms[raised] = coefficients.div_int(coefficient, power + 1)
        return self._make(terms)


class UnivariatePolynomialRing(PolynomialRing[E], Euclidean[Polynomial[E]]):
    """`K[x]` for a field `K`: the one case where polynomial division exists.

    Division is defined only for a single generator over a field; a multivariate
    ring never advertises the Euclidean capability.
    """

    __slots__ = ()

    def __init__(
        self,
        generator: SymbolId,
        coefficients: Field[E],
        order: MonomialOrder = MonomialOrder.LEX,
    ) -> None:
        if not isinstance(coefficients, Field):
            raise TypeError("univariate division needs a field of coefficients")
        super().__init__((generator,), coefficients, order)

    @property
    def coefficients(self) -> Field[E]:
        """Narrowed on purpose: this ring was built with field coefficients."""
        return cast("Field[E]", self._coefficients)

    def divmod(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> tuple[Polynomial[E], Polynomial[E]]:
        """Long division; the remainder has strictly smaller degree."""
        self._own(left)
        self._own(right)
        if right.is_zero():
            raise ZeroDivisionError("polynomial division by zero")
        coefficients = self.coefficients
        divisor_degree = self.degree(right, 0)
        divisor_leading = self.coefficient(right, (divisor_degree,))
        quotient = self.zero()
        remainder = left
        while not remainder.is_zero():
            degree = self.degree(remainder, 0)
            if degree < divisor_degree:
                break
            leading = self.coefficient(remainder, (degree,))
            factor = self.monomial(
                (degree - divisor_degree,),
                coefficients.div(leading, divisor_leading),
            )
            quotient = self.add(quotient, factor)
            remainder = self.sub(remainder, self.mul(factor, right))
        return quotient, remainder

    def gcd(self, left: Polynomial[E], right: Polynomial[E]) -> Polynomial[E]:
        """Greatest common divisor, normalised to a monic polynomial."""
        self._own(left)
        self._own(right)
        current = super().gcd(left, right)
        if current.is_zero():
            return self.zero()
        leading = self.coefficient(current, (self.degree(current, 0),))
        return self.mul(
            self.monomial((0,), self.coefficients.inv(leading)),
            current,
        )

    def monic(self, value: Polynomial[E]) -> Polynomial[E]:
        """Scale `value` by the inverse of its leading coefficient."""
        self._own(value)
        if value.is_zero():
            return value
        leading = self.coefficient(value, (self.degree(value, 0),))
        if self.coefficients.is_one(leading):
            return value
        return self.mul(
            self.monomial((0,), self.coefficients.inv(leading)), value
        )

    def div_exact(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> Polynomial[E]:
        """Exact polynomial quotient; this ring is an `ExactDivision` member."""
        return self.exact_div(left, right)

    def xgcd(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> tuple[Polynomial[E], Polynomial[E], Polynomial[E]]:
        """Extended Euclid with a monic gcd and Bezout coefficients."""
        self._own(left)
        self._own(right)
        gcd, left_coefficient, right_coefficient = super().xgcd(left, right)
        if gcd.is_zero():
            return gcd, left_coefficient, right_coefficient
        leading = self.coefficient(gcd, (self.degree(gcd, 0),))
        scale = self.coefficients.inv(leading)
        factor = self.monomial((0,), scale)
        return (
            self.mul(factor, gcd),
            self.mul(factor, left_coefficient),
            self.mul(factor, right_coefficient),
        )

    def squarefree_part(self, value: Polynomial[E]) -> Polynomial[E]:
        """The monic squarefree part `value / gcd(value, value')`.

        The coefficient field must be characteristic zero; positive
        characteristic needs a separate Frobenius-based algorithm and is
        refused here rather than silently using the derivative formula.
        """
        self._own(value)
        self._require_characteristic_zero("squarefree part")
        if value.is_zero():
            return value
        if self.is_constant(value):
            return self.one()
        derivative = self.derivative(value, 0)
        divisor = self.gcd(value, derivative)
        quotient, _ = self.divmod(value, divisor)
        return self.monic(quotient)

    def squarefree_decomposition(
        self,
        value: Polynomial[E],
    ) -> tuple[E, tuple[tuple[Polynomial[E], int], ...]]:
        """Yun's squarefree decomposition in characteristic zero.

        Return `(unit, factors)` with `value == unit * product(factor**multiplicity)`
        and every factor monic and squarefree.  The algorithm is Yun's
        squarefree decomposition (Yun, 1976; Geddes--Czapor--Labahn,
        *Algorithms for Computer Algebra*, §8.2).
        """
        self._own(value)
        self._require_characteristic_zero("squarefree decomposition")
        if value.is_zero():
            raise ValueError("the zero polynomial has no squarefree decomposition")
        unit = self.coefficient(value, (self.degree(value, 0),))
        if self.is_constant(value):
            return unit, ()
        monic = self.monic(value)
        derivative = self.derivative(monic, 0)
        gcd = self.gcd(monic, derivative)
        quotient, _ = self.divmod(monic, gcd)
        factors: list[tuple[Polynomial[E], int]] = []
        multiplicity = 1
        while not self.is_one(quotient):
            common = self.gcd(quotient, gcd)
            factor, _ = self.divmod(quotient, common)
            if not self.is_one(factor):
                factors.append((self.monic(factor), multiplicity))
            quotient = common
            gcd, _ = self.divmod(gcd, common)
            multiplicity += 1
        if not self.is_one(gcd):
            raise AssertionError(
                "Yun's decomposition left a nontrivial repeated part"
            )
        return unit, tuple(factors)

    def subresultant_chain(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> tuple[Polynomial[E], ...]:
        """The subresultant polynomial remainder sequence.

        This is a subresultant PRS in the Brown/Collins family (Cohen,
        *A Course in Computational Algebraic Number Theory*, Algorithm 3.3.7),
        not a list of determinant-normalised subresultant polynomials.  The
        terms are proportional to Brown's subresultants; the scalar
        normalisation is not the determinant normalisation.  The last nonzero
        member is a gcd up to a nonzero scalar, and the sequence keeps the
        remainder structure with controlled coefficient growth.

        The first two entries are the supplied pair, swapped only when the
        first has smaller degree.  Equal-degree inputs are therefore allowed;
        from the second remainder onward the degrees strictly decrease.

        Reference implementations: Maxima `src/result.lisp:95-144`
        (`subresult`, Brown's subresultant PRS) and `src/rat3c.lisp:252-264`
        (`subresgcd`); FriCAS `src/algebra/prs.spad:699-721`
        (`chainSubResultants`).  The present implementation is the field
        version of the same PRS recurrence.

        The coefficient field must be characteristic zero; positive
        characteristic needs a separate Frobenius-based treatment.
        """
        self._own(left)
        self._own(right)
        self._require_characteristic_zero("subresultant chain")
        if left.is_zero():
            return (right,) if not right.is_zero() else (left,)
        if right.is_zero():
            return (left,)
        if self.degree(left, 0) < self.degree(right, 0):
            left, right = right, left
        coefficients = self.coefficients
        previous, current = left, right
        difference = self.degree(previous, 0) - self.degree(current, 0)
        beta = coefficients.neg(
            coefficients.pow(
                coefficients.neg(coefficients.one()), difference + 1
            )
        )
        psi = coefficients.neg(coefficients.one())
        chain = [previous, current]
        while not current.is_zero():
            difference = self.degree(previous, 0) - self.degree(current, 0)
            scaled = self.mul(
                self.constant(coefficients.pow(psi, difference)), previous
            )
            _, remainder = self.divmod(scaled, current)
            following = self.neg(
                self.mul(self.constant(coefficients.inv(beta)), remainder)
            )
            if following.is_zero():
                break
            chain.append(following)
            leading = self.coefficient(current, (self.degree(current, 0),))
            denominator = (
                coefficients.one()
                if difference == 0
                else coefficients.pow(psi, difference - 1)
            )
            next_psi = coefficients.div(
                coefficients.pow(coefficients.neg(leading), difference),
                denominator,
            )
            next_beta = coefficients.neg(
                coefficients.mul(leading, next_psi)
            )
            previous, current = current, following
            psi, beta = next_psi, next_beta
        return tuple(chain)

    def resultant(
        self,
        left: Polynomial[E],
        right: Polynomial[E],
    ) -> E:
        """The resultant with respect to the unique generator.

        The Sylvester determinant is evaluated by exact field elimination.  The
        selected main variable is the ring's generator; a multivariate caller
        must build the corresponding univariate view first.  Reference
        implementations: Maxima `src/result.lisp` (subresultant PRS resultant)
        and FriCAS `src/algebra/prs.spad` (`resultant`).
        """
        self._own(left)
        self._own(right)
        coefficients = self.coefficients
        if left.is_zero() or right.is_zero():
            return coefficients.zero()
        left_degree = self.degree(left, 0)
        right_degree = self.degree(right, 0)
        if left_degree == 0:
            return coefficients.pow(
                self.coefficient(left, (0,)), right_degree
            )
        if right_degree == 0:
            return coefficients.pow(
                self.coefficient(right, (0,)), left_degree
            )
        size = left_degree + right_degree
        space = MatrixSpace(coefficients, size, size)
        left_coefficients = [
            self.coefficient(left, (index,))
            for index in range(left_degree, -1, -1)
        ]
        right_coefficients = [
            self.coefficient(right, (index,))
            for index in range(right_degree, -1, -1)
        ]
        rows: list[list[E]] = []
        zero = coefficients.zero()
        for shift in range(right_degree):
            row = [zero for _ in range(size)]
            for index, coefficient in enumerate(left_coefficients):
                row[shift + index] = coefficient
            rows.append(row)
        for shift in range(left_degree):
            row = [zero for _ in range(size)]
            for index, coefficient in enumerate(right_coefficients):
                row[shift + index] = coefficient
            rows.append(row)
        return space.determinant(space.matrix(rows))

    def discriminant(self, value: Polynomial[E]) -> E:
        """The discriminant `(-1)^{m(m-1)/2} res(f, f') / lc(f)`."""
        self._own(value)
        if value.is_zero():
            return self.coefficients.zero()
        degree = self.degree(value, 0)
        if degree == 0:
            return self.coefficients.one()
        derivative = self.derivative(value, 0)
        resultant = self.resultant(value, derivative)
        leading = self.coefficient(value, (degree,))
        result = self.coefficients.div(resultant, leading)
        if (degree * (degree - 1) // 2) % 2:
            result = self.coefficients.neg(result)
        return result

    def _require_characteristic_zero(self, operation: str) -> None:
        if self.coefficients.characteristic != 0:
            raise ValueError(
                f"{operation} needs a characteristic-zero coefficient field"
            )
