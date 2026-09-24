"""Q(i), the Gaussian rational field."""

from __future__ import annotations

from fractions import Fraction
from typing import TypeAlias

from cas.math.domains.base import Domain, DomainCapabilities, DomainElement, Ring
from cas.math.domains.poly import Poly
from cas.math.domains.q import Q_RING
from cas.math.domains.qarith import fold
from cas.math.domains.ratfunc import rf_from_term
from cas.syntax import term as T
from cas.syntax.term import Expr, Sym, Term
from cas.syntax.termpath import free_vars

GaussianElement: TypeAlias = tuple[Fraction, Fraction]


class QIRing(Ring):
    """Gaussian coefficients represented by normalized rational pairs."""

    is_field = True

    def from_int(self, value: int) -> DomainElement:
        return (Fraction(value), Fraction(0))

    def from_frac(self, value: Fraction) -> DomainElement:
        return (value, Fraction(0))

    def add(self, left: DomainElement, right: DomainElement) -> DomainElement:
        left_pair = self._pair(left)
        right_pair = self._pair(right)
        return (left_pair[0] + right_pair[0], left_pair[1] + right_pair[1])

    def neg(self, value: DomainElement) -> DomainElement:
        real, imaginary = self._pair(value)
        return (-real, -imaginary)

    def mul(self, left: DomainElement, right: DomainElement) -> DomainElement:
        left_real, left_imaginary = self._pair(left)
        right_real, right_imaginary = self._pair(right)
        return (
            left_real * right_real - left_imaginary * right_imaginary,
            left_real * right_imaginary + left_imaginary * right_real,
        )

    def equal(self, left: DomainElement, right: DomainElement) -> bool:
        return self._pair(left) == self._pair(right)

    def div_exact(self, left: DomainElement, right: DomainElement) -> DomainElement:
        left_real, left_imaginary = self._pair(left)
        right_real, right_imaginary = self._pair(right)
        norm = right_real * right_real + right_imaginary * right_imaginary
        if norm == 0:
            raise ZeroDivisionError("division by zero")
        return (
            (left_real * right_real + left_imaginary * right_imaginary) / norm,
            (left_imaginary * right_real - left_real * right_imaginary) / norm,
        )

    @staticmethod
    def _pair(value: DomainElement) -> GaussianElement:
        if (
            not isinstance(value, tuple)
            or len(value) != 2
            or not isinstance(value[0], Fraction)
            or not isinstance(value[1], Fraction)
        ):
            raise TypeError("Q(i) ring elements must be rational pairs")
        return value[0], value[1]


QI_RING = QIRing()


def _lift_const(term: Term, constant: Term, variable: Sym) -> Term:
    """Replace the injected constant atom by a fresh variable."""
    if term is constant:
        return variable
    if isinstance(term, Expr) and term.args:
        return T.mk(
            term.head,
            tuple(_lift_const(argument, constant, variable) for argument in term.args),
        )
    return term


def _pair_mod(polynomial: Poly) -> GaussianElement:
    """Reduce a univariate polynomial modulo z^2 + 1."""
    real = Fraction(0)
    imaginary = Fraction(0)
    for exponents, coefficient in polynomial.monos:
        if not isinstance(coefficient, Fraction):
            raise TypeError("Q(i) reduction requires rational coefficients")
        value = -coefficient if (exponents[0] // 2) % 2 else coefficient
        if exponents[0] % 2:
            imaginary += value
        else:
            real += value
    return real, imaginary


def qi_of_term(i_constant: Term, term: Term) -> GaussianElement | None:
    """Project a closed term into Q(i), or return ``None``."""
    if free_vars(term):
        return None
    variable = T.S("z")
    rational_function = rf_from_term(
        Q_RING,
        _lift_const(term, i_constant, variable),
        (variable,),
    )
    if rational_function is None:
        return None
    numerator = _pair_mod(rational_function.num)
    denominator = _pair_mod(rational_function.den)
    if denominator == (Fraction(0), Fraction(0)):
        return None
    pair = QI_RING.div_exact(numerator, denominator)
    return QI_RING._pair(pair)


class QIDomain(Domain):
    """Q(i) with its constant identity injected by the assembly layer."""

    name = "Q(i)"
    capabilities = DomainCapabilities(field=True)
    ring = QI_RING

    def __init__(self, i_constant: Term) -> None:
        self.i = i_constant

    def member(self, term: Term) -> bool:
        return qi_of_term(self.i, term) is not None

    def to_term(self, pair: GaussianElement) -> Term:
        real, imaginary = pair
        if imaginary == 0:
            return T.N(real)
        imaginary_part = T.times(T.N(imaginary), self.i)
        if real == 0:
            return fold(imaginary_part)
        return fold(T.plus(T.N(real), imaginary_part))

    def normalize(self, term: Term) -> Term | None:
        pair = qi_of_term(self.i, term)
        if pair is None:
            return None
        return self.to_term(pair)

    def equal(self, left: Term, right: Term) -> bool | None:
        left_pair = qi_of_term(self.i, left)
        right_pair = qi_of_term(self.i, right)
        if left_pair is None or right_pair is None:
            return None
        return left_pair == right_pair
