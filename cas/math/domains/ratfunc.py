"""K(x1..xn) rational function field over an explicit coefficient ring."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from typing import TypeAlias, cast

from cas.math.domains.base import (
    Domain,
    DomainCapabilities,
    DomainElement,
    PolynomialView,
    Ring,
)
from cas.math.domains.poly import (
    CoefficientDict,
    Poly,
    _norm,
    p_deriv,
    p_divmod_field,
    p_gcd_univar,
    p_mul,
    p_scale,
    to_term,
)
from cas.math.domains.poly import (
    from_term as poly_from_term,
)
from cas.syntax import term as T
from cas.syntax.term import Expr, Int, Sym, Term

RFIntermediate: TypeAlias = tuple[CoefficientDict, CoefficientDict]


@dataclass(frozen=True, slots=True)
class RatFunc:
    """A numerator/denominator pair with a nonzero denominator."""

    num: Poly
    den: Poly


def _add(
    ring: Ring,
    left: CoefficientDict,
    right: CoefficientDict,
) -> CoefficientDict:
    result = dict(left)
    for key, coefficient in right.items():
        result[key] = ring.add(
            result.get(key, ring.from_int(0)), coefficient
        )
        if ring.is_zero(result[key]):
            del result[key]
    return result


def _mul(
    ring: Ring,
    left: CoefficientDict,
    right: CoefficientDict,
) -> CoefficientDict:
    result: CoefficientDict = {}
    for left_key, left_coefficient in left.items():
        for right_key, right_coefficient in right.items():
            key = tuple(
                left_exponent + right_exponent
                for left_exponent, right_exponent in zip(left_key, right_key)
            )
            result[key] = ring.add(
                result.get(key, ring.from_int(0)),
                ring.mul(left_coefficient, right_coefficient),
            )
    return {
        key: coefficient
        for key, coefficient in result.items()
        if not ring.is_zero(coefficient)
    }


def _pow(ring: Ring, value: CoefficientDict, exponent: int) -> CoefficientDict:
    if exponent < 0:
        raise ValueError("negative rational-function exponent")
    result: CoefficientDict = {(0,) * _width(value): ring.from_int(1)}
    base = value
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = _mul(ring, result, base)
        remaining >>= 1
        if remaining:
            base = _mul(ring, base, base)
    return result


def _width(value: CoefficientDict) -> int:
    return len(next(iter(value))) if value else 0


def _is_zero(value: CoefficientDict) -> bool:
    return not value


def rf_from_term(
    ring: Ring,
    term: Term,
    variables: tuple[Sym, ...],
) -> RatFunc | None:
    """Convert a term into a rational function or return ``None``."""
    one: CoefficientDict = {(0,) * len(variables): ring.from_int(1)}

    def convert(current: Term) -> RFIntermediate | None:
        polynomial = poly_from_term(ring, current, variables)
        if polynomial is not None:
            return dict(polynomial.monos), dict(one)
        if not isinstance(current, Expr):
            return None
        name = current.head.name
        if name == "Plus":
            accumulator: RFIntermediate | None = None
            for argument in current.args:
                converted = convert(argument)
                if converted is None:
                    return None
                if accumulator is None:
                    accumulator = converted
                else:
                    left_num, left_den = accumulator
                    right_num, right_den = converted
                    accumulator = (
                        _add(
                            ring,
                            _mul(ring, left_num, right_den),
                            _mul(ring, right_num, left_den),
                        ),
                        _mul(ring, left_den, right_den),
                    )
            return accumulator
        if name == "Times":
            accumulator = None
            for argument in current.args:
                converted = convert(argument)
                if converted is None:
                    return None
                if accumulator is None:
                    accumulator = converted
                else:
                    accumulator = (
                        _mul(ring, accumulator[0], converted[0]),
                        _mul(ring, accumulator[1], converted[1]),
                    )
            return accumulator
        if name == "Power":
            base_term, exponent_term = current.args
            base = convert(base_term)
            if base is None or not isinstance(exponent_term, Int):
                return None
            numerator, denominator = base
            exponent = exponent_term.v
            if exponent >= 0:
                if exponent == 0 and _is_zero(numerator):
                    return None
                return (
                    _pow(ring, numerator, exponent),
                    _pow(ring, denominator, exponent),
                )
            if _is_zero(numerator):
                return None
            return (
                _pow(ring, denominator, -exponent),
                _pow(ring, numerator, -exponent),
            )
        return None

    converted = convert(term)
    if converted is None:
        return None
    numerator, denominator = converted
    if _is_zero(denominator):
        return None
    return RatFunc(
        _norm(ring, variables, numerator),
        _norm(ring, variables, denominator),
    )


def rf_equal(ring: Ring, left: RatFunc, right: RatFunc) -> bool:
    """Decide equality by exact cross multiplication."""
    return (
        p_mul(ring, left.num, right.den).monos
        == p_mul(ring, right.num, left.den).monos
    )


def rf_reduce(ring: Ring, value: RatFunc) -> RatFunc:
    """Apply the available univariate gcd reduction fast path."""
    if len(value.num.vars) != 1 or value.den.is_zero():
        return value
    gcd = p_gcd_univar(ring, value.num, value.den)
    if gcd.is_zero():
        return value
    reduced_num, _ = p_divmod_field(ring, value.num, gcd, 0)
    reduced_den, _ = p_divmod_field(ring, value.den, gcd, 0)
    if reduced_den.is_zero():
        return value
    leading = max(reduced_den.monos, key=lambda item: item[0][0])
    inverse = ring.div_exact(ring.from_int(1), leading[1])
    return RatFunc(
        p_scale(ring, reduced_num, inverse),
        p_scale(ring, reduced_den, inverse),
    )


def rf_to_term(ring: Ring, value: RatFunc) -> Term:
    """Render a rational function as a canonical term."""
    numerator = to_term(ring, value.num)
    denominator = to_term(ring, value.den)
    if T.is_num(denominator) and T.num_val(denominator) == 1:
        return numerator
    return T.mk(
        T.S("Times"),
        (numerator, T.pw(denominator, T.N(-1))),
    )


def rf_deriv(ring: Ring, value: RatFunc, variable_index: int) -> RatFunc:
    """Apply the quotient-rule derivation."""
    numerator_derivative = p_deriv(ring, value.num, variable_index)
    denominator_derivative = p_deriv(ring, value.den, variable_index)
    numerator = _norm(
        ring,
        value.num.vars,
        _add(
            ring,
            _mul(
                ring,
                dict(numerator_derivative.monos),
                dict(value.den.monos),
            ),
            {
                key: ring.neg(coefficient)
                for key, coefficient in _mul(
                    ring,
                    dict(value.num.monos),
                    dict(denominator_derivative.monos),
                ).items()
            },
        ),
    )
    denominator = _norm(
        ring,
        value.den.vars,
        _mul(ring, dict(value.den.monos), dict(value.den.monos)),
    )
    return rf_reduce(ring, RatFunc(numerator, denominator))


class RatFuncDomain(Domain):
    """A rational function domain over an explicit coefficient ring."""

    def __init__(
        self,
        variables: Iterable[Sym],
        ring: Ring,
        name: str | None = None,
    ) -> None:
        self.vars = tuple(variables)
        self.ring = ring
        self.name = name or "K(" + ",".join(variable.name for variable in self.vars) + ")"
        self.capabilities = DomainCapabilities(
            field=True,
            euclidean=bool(ring.is_field and len(self.vars) == 1),
        )

    def _parts(self) -> tuple[Ring, tuple[Sym, ...]]:
        ring = self.ring
        variables = self.vars
        if ring is None or variables is None:
            raise RuntimeError("rational-function domain is not initialized")
        return ring, variables

    def member(self, term: Term) -> bool:
        ring, variables = self._parts()
        return rf_from_term(ring, term, variables) is not None

    def normalize(self, term: Term) -> Term | None:
        ring, variables = self._parts()
        value = rf_from_term(ring, term, variables)
        if value is None:
            return None
        return rf_to_term(ring, rf_reduce(ring, value))

    def equal(self, left: Term, right: Term) -> bool | None:
        ring, variables = self._parts()
        left_value = rf_from_term(ring, left, variables)
        right_value = rf_from_term(ring, right, variables)
        if left_value is None or right_value is None:
            return None
        return rf_equal(ring, left_value, right_value)

    def element_is_zero(self, element: DomainElement) -> bool:
        if not isinstance(element, RatFunc):
            raise TypeError("RatFuncDomain received a non-rational-function element")
        return element.num.is_zero()

    def element_to_term(self, element: DomainElement) -> Term:
        if not isinstance(element, RatFunc):
            raise TypeError("RatFuncDomain received a non-rational-function element")
        ring, _ = self._parts()
        return rf_to_term(ring, rf_reduce(ring, element))

    def element_poly(self, element: DomainElement) -> PolynomialView | None:
        if not isinstance(element, RatFunc):
            raise TypeError("RatFuncDomain received a non-rational-function element")
        ring, _ = self._parts()
        return cast(PolynomialView, rf_reduce(ring, element).num)

    def element_as_poly(self, element: DomainElement) -> PolynomialView | None:
        if not isinstance(element, RatFunc):
            raise TypeError("RatFuncDomain received a non-rational-function element")
        ring, _ = self._parts()
        reduced = rf_reduce(ring, element)
        denominator = reduced.den.monos
        if len(denominator) != 1 or any(exponent for exponent in denominator[0][0]):
            return None
        coefficient = denominator[0][1]
        return cast(
            PolynomialView,
            p_scale(
                ring,
                reduced.num,
                ring.div_exact(ring.from_int(1), coefficient),
            ),
        )


_domain_cache: dict[tuple[tuple[Sym, ...], Ring], RatFuncDomain] = {}


def ratfunc_domain(*variables: Sym, ring: Ring) -> RatFuncDomain:
    """Return a cached rational-function domain."""
    variable_key = tuple(variables)
    key = (variable_key, ring)
    domain = _domain_cache.get(key)
    if domain is None:
        domain = RatFuncDomain(variable_key, ring)
        _domain_cache[key] = domain
    return domain
