"""K[x1..xn] polynomial domain over an explicit coefficient ring."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias, cast

from cas.math.domains.base import (
    Domain,
    DomainCapabilities,
    DomainElement,
    PolynomialView,
    Ring,
    RingError,
)
from cas.syntax import term as T
from cas.syntax.term import Expr, Int, Sym, Term

MonomialKey: TypeAlias = tuple[int, ...]
Monomial: TypeAlias = tuple[MonomialKey, DomainElement]
CoefficientDict: TypeAlias = dict[MonomialKey, DomainElement]


@dataclass(frozen=True, slots=True)
class Poly:
    """A polynomial with a fixed variable order and ascending exponents."""

    vars: tuple[Sym, ...]
    monos: tuple[Monomial, ...]

    def is_zero(self) -> bool:
        return not self.monos

    def deg_in(self, index: int) -> int:
        return max((key[index] for key, _ in self.monos), default=-1)


def _norm(
    ring: Ring,
    variables: tuple[Sym, ...],
    coefficients: Mapping[MonomialKey, DomainElement],
) -> Poly:
    keys = sorted(
        key for key, coefficient in coefficients.items()
        if not ring.is_zero(coefficient)
    )
    return Poly(
        variables,
        tuple((key, coefficients[key]) for key in keys),
    )


def p_zero(variables: tuple[Sym, ...]) -> Poly:
    return Poly(variables, ())


def p_const(ring: Ring, variables: tuple[Sym, ...], coefficient: DomainElement) -> Poly:
    zero = (0,) * len(variables)
    return _norm(ring, variables, {zero: coefficient})


def p_add(ring: Ring, left: Poly, right: Poly) -> Poly:
    coefficients = dict(left.monos)
    for key, coefficient in right.monos:
        coefficients[key] = ring.add(
            coefficients.get(key, ring.from_int(0)), coefficient
        )
        if ring.is_zero(coefficients[key]):
            del coefficients[key]
    return _norm(ring, left.vars, coefficients)


def p_neg(ring: Ring, polynomial: Poly) -> Poly:
    return Poly(
        polynomial.vars,
        tuple((key, ring.neg(coefficient)) for key, coefficient in polynomial.monos),
    )


def p_sub(ring: Ring, left: Poly, right: Poly) -> Poly:
    return p_add(ring, left, p_neg(ring, right))


def p_mul(ring: Ring, left: Poly, right: Poly) -> Poly:
    if left.is_zero() or right.is_zero():
        return p_zero(left.vars)
    coefficients: CoefficientDict = {}
    for left_key, left_coefficient in left.monos:
        for right_key, right_coefficient in right.monos:
            key = tuple(
                left_exponent + right_exponent
                for left_exponent, right_exponent in zip(left_key, right_key)
            )
            coefficients[key] = ring.add(
                coefficients.get(key, ring.from_int(0)),
                ring.mul(left_coefficient, right_coefficient),
            )
    return _norm(ring, left.vars, coefficients)


def p_pow(ring: Ring, polynomial: Poly, exponent: int) -> Poly:
    """Fast exponentiation for a nonnegative exponent."""
    if exponent < 0:
        raise ValueError("negative exponent")
    result = p_const(ring, polynomial.vars, ring.from_int(1))
    base = polynomial
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = p_mul(ring, result, base)
        base = p_mul(ring, base, base)
        remaining >>= 1
    return result


def p_scale(ring: Ring, polynomial: Poly, coefficient: DomainElement) -> Poly:
    if ring.is_zero(coefficient):
        return p_zero(polynomial.vars)
    return Poly(
        polynomial.vars,
        tuple(
            (key, ring.mul(coefficient, value))
            for key, value in polynomial.monos
        ),
    )


def p_divmod_field(
    ring: Ring,
    dividend: Poly,
    divisor: Poly,
    variable_index: int,
) -> tuple[Poly, Poly]:
    """Divide over a field coefficient ring with respect to one variable."""
    if divisor.is_zero():
        raise ZeroDivisionError("poly division by zero")
    remainder: CoefficientDict = dict(dividend.monos)
    quotient: CoefficientDict = {}
    divisor_top = max(
        (key[variable_index] for key, _ in divisor.monos), default=-1
    )
    divisor_lead = max(
        divisor.monos, key=lambda item: item[0][variable_index]
    )
    while True:
        live = [
            (key, coefficient)
            for key, coefficient in remainder.items()
            if not ring.is_zero(coefficient)
        ]
        if not live:
            break
        key, coefficient = max(
            live, key=lambda item: item[0][variable_index]
        )
        exponent_difference = key[variable_index] - divisor_top
        if exponent_difference < 0:
            break
        quotient_key = tuple(
            left - right
            for left, right in zip(key, divisor_lead[0])
        )
        quotient_coefficient = ring.div_exact(
            coefficient, divisor_lead[1]
        )
        quotient[quotient_key] = ring.add(
            quotient.get(quotient_key, ring.from_int(0)),
            quotient_coefficient,
        )
        subtraction: CoefficientDict = {}
        for divisor_key, divisor_coefficient in divisor.monos:
            target_key = tuple(
                left + right
                for left, right in zip(quotient_key, divisor_key)
            )
            subtraction[target_key] = ring.mul(
                quotient_coefficient, divisor_coefficient
            )
        for target_key, target_coefficient in subtraction.items():
            new_value = ring.sub(
                remainder.get(target_key, ring.from_int(0)),
                target_coefficient,
            )
            if ring.is_zero(new_value):
                remainder.pop(target_key, None)
            else:
                remainder[target_key] = new_value
    return _norm(ring, dividend.vars, quotient), _norm(
        ring, dividend.vars, remainder
    )


def p_gcd_univar(ring: Ring, left: Poly, right: Poly) -> Poly:
    """Compute a monic univariate gcd over a field coefficient ring."""
    if len(left.vars) != 1:
        raise ValueError("univariate only")
    first, second = left, right
    while not second.is_zero():
        _, remainder = p_divmod_field(ring, first, second, 0)
        first, second = second, remainder
    if first.is_zero():
        return p_zero(left.vars)
    leading = max(first.monos, key=lambda item: item[0][0])
    return p_scale(
        ring,
        first,
        ring.div_exact(ring.from_int(1), leading[1]),
    )


def p_deriv(ring: Ring, polynomial: Poly, variable_index: int) -> Poly:
    """Apply the ring derivation and the formal variable derivative."""
    coefficients: CoefficientDict = {}
    for key, coefficient in polynomial.monos:
        derivative = ring.deriv(coefficient)
        if not ring.is_zero(derivative):
            coefficients[key] = ring.add(
                coefficients.get(key, ring.from_int(0)), derivative
            )
        exponent = key[variable_index]
        if exponent:
            target_key = tuple(
                value - (1 if index == variable_index else 0)
                for index, value in enumerate(key)
            )
            coefficients[target_key] = ring.add(
                coefficients.get(target_key, ring.from_int(0)),
                ring.mul(ring.from_int(exponent), coefficient),
            )
    return _norm(ring, polynomial.vars, coefficients)


def from_term(
    ring: Ring,
    term: Term,
    variables: tuple[Sym, ...],
) -> Poly | None:
    """Convert a term into a polynomial or return ``None`` for a non-member."""
    indices = {variable: index for index, variable in enumerate(variables)}
    zero = (0,) * len(variables)

    def convert(current: Term) -> CoefficientDict | None:
        if isinstance(current, Int):
            return {zero: ring.from_int(current.v)} if current.v else {}
        if T.is_num(current):
            try:
                return {zero: ring.from_frac(T.num_val(current))}
            except RingError:
                return None
        if isinstance(current, Sym):
            if current not in indices:
                return None
            key = tuple(
                1 if index == indices[current] else 0
                for index in range(len(variables))
            )
            return {key: ring.from_int(1)}
        if isinstance(current, Expr):
            name = current.head.name
            if name == "Plus":
                accumulator: CoefficientDict = {}
                for argument in current.args:
                    converted = convert(argument)
                    if converted is None:
                        return None
                    for key, coefficient in converted.items():
                        accumulator[key] = ring.add(
                            accumulator.get(key, ring.from_int(0)),
                            coefficient,
                        )
                return {
                    key: coefficient
                    for key, coefficient in accumulator.items()
                    if not ring.is_zero(coefficient)
                }
            if name == "Times":
                accumulator = {zero: ring.from_int(1)}
                for argument in current.args:
                    converted = convert(argument)
                    if converted is None:
                        return None
                    next_values: CoefficientDict = {}
                    for left_key, left_coefficient in accumulator.items():
                        for right_key, right_coefficient in converted.items():
                            key = tuple(
                                left + right
                                for left, right in zip(left_key, right_key)
                            )
                            next_values[key] = ring.add(
                                next_values.get(key, ring.from_int(0)),
                                ring.mul(left_coefficient, right_coefficient),
                            )
                    accumulator = {
                        key: coefficient
                        for key, coefficient in next_values.items()
                        if not ring.is_zero(coefficient)
                    }
                return accumulator
            if name == "Power":
                base_term, exponent_term = current.args
                base = convert(base_term)
                if (
                    base is None
                    or not isinstance(exponent_term, Int)
                    or exponent_term.v < 0
                ):
                    return None
                if exponent_term.v == 0:
                    return {zero: ring.from_int(1)} if base else None
                current_power: CoefficientDict = {zero: ring.from_int(1)}
                base_power = base
                remaining = exponent_term.v
                while remaining:
                    if remaining & 1:
                        next_values = {}
                        for left_key, left_coefficient in current_power.items():
                            for right_key, right_coefficient in base_power.items():
                                key = tuple(
                                    left + right
                                    for left, right in zip(left_key, right_key)
                                )
                                next_values[key] = ring.add(
                                    next_values.get(key, ring.from_int(0)),
                                    ring.mul(left_coefficient, right_coefficient),
                                )
                        current_power = {
                            key: coefficient
                            for key, coefficient in next_values.items()
                            if not ring.is_zero(coefficient)
                        }
                    remaining >>= 1
                    if remaining:
                        next_values = {}
                        for left_key, left_coefficient in base_power.items():
                            for right_key, right_coefficient in base_power.items():
                                key = tuple(
                                    left + right
                                    for left, right in zip(left_key, right_key)
                                )
                                next_values[key] = ring.add(
                                    next_values.get(key, ring.from_int(0)),
                                    ring.mul(left_coefficient, right_coefficient),
                                )
                        base_power = {
                            key: coefficient
                            for key, coefficient in next_values.items()
                            if not ring.is_zero(coefficient)
                        }
                return current_power
        return None

    converted = convert(term)
    if converted is None:
        return None
    return _norm(ring, variables, converted)


def to_term(ring: Ring, polynomial: Poly) -> Term:
    """Render a polynomial in the canonical interned term language."""
    terms: list[Term] = []
    for key, coefficient in polynomial.monos:
        factors = [
            variable if exponent == 1 else T.pw(variable, T.N(exponent))
            for variable, exponent in zip(polynomial.vars, key)
            if exponent > 0
        ]
        coefficient_is_one = ring.equal(coefficient, ring.from_int(1))
        if coefficient_is_one and factors:
            term = factors[0] if len(factors) == 1 else T.mk(
                T.S("Times"), tuple(factors)
            )
        else:
            rendered = (
                T.N(coefficient)
                if isinstance(coefficient, Fraction)
                else ring.render_coefficient(coefficient)
            )
            all_factors = [rendered, *factors]
            term = all_factors[0] if len(all_factors) == 1 else T.mk(
                T.S("Times"), tuple(all_factors)
            )
        terms.append(term)
    if not terms:
        return T.N(0)
    return terms[0] if len(terms) == 1 else T.mk(T.S("Plus"), tuple(terms))


class PolyDomain(Domain):
    """A polynomial domain over an explicit coefficient ring."""

    def __init__(
        self,
        variables: Iterable[Sym],
        ring: Ring,
        name: str | None = None,
    ) -> None:
        self.vars = tuple(variables)
        self.ring = ring
        self.name = name or "K[" + ",".join(variable.name for variable in self.vars) + "]"
        self.capabilities = DomainCapabilities(
            euclidean=bool(ring.is_field and len(self.vars) == 1)
        )

    def member(self, term: Term) -> bool:
        ring = self.ring
        variables = self.vars
        if ring is None or variables is None:
            raise RuntimeError("polynomial domain is not initialized")
        return from_term(ring, term, variables) is not None

    def normalize(self, term: Term) -> Term | None:
        ring = self.ring
        variables = self.vars
        if ring is None or variables is None:
            raise RuntimeError("polynomial domain is not initialized")
        polynomial = from_term(ring, term, variables)
        if polynomial is None:
            return None
        return to_term(ring, polynomial)

    def equal(self, left: Term, right: Term) -> bool | None:
        ring = self.ring
        variables = self.vars
        if ring is None or variables is None:
            raise RuntimeError("polynomial domain is not initialized")
        left_poly = from_term(ring, left, variables)
        right_poly = from_term(ring, right, variables)
        if left_poly is None or right_poly is None:
            return None
        return left_poly.monos == right_poly.monos

    def element_is_zero(self, element: DomainElement) -> bool:
        if not isinstance(element, Poly):
            raise TypeError("PolyDomain received a non-polynomial element")
        return element.is_zero()

    def element_to_term(self, element: DomainElement) -> Term:
        if not isinstance(element, Poly):
            raise TypeError("PolyDomain received a non-polynomial element")
        ring = self.ring
        if ring is None:
            raise RuntimeError("polynomial domain is not initialized")
        return to_term(ring, element)

    def element_poly(self, element: DomainElement) -> PolynomialView | None:
        if not isinstance(element, Poly):
            raise TypeError("PolyDomain received a non-polynomial element")
        return cast(PolynomialView, element)

    def element_as_poly(self, element: DomainElement) -> PolynomialView | None:
        if not isinstance(element, Poly):
            raise TypeError("PolyDomain received a non-polynomial element")
        return cast(PolynomialView, element)


_domain_cache: dict[tuple[tuple[Sym, ...], Ring], PolyDomain] = {}


def poly_domain(*variables: Sym, ring: Ring) -> PolyDomain:
    """Return a cached polynomial domain for an explicit variable set and ring."""
    variable_key = tuple(variables)
    key = (variable_key, ring)
    domain = _domain_cache.get(key)
    if domain is None:
        domain = PolyDomain(variable_key, ring)
        _domain_cache[key] = domain
    return domain
