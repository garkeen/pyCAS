"""Shared polynomial resultant and squarefree-decomposition operations."""

from __future__ import annotations

from cas.math.domains.base import DomainElement, Ring
from cas.math.domains.poly import (
    Poly,
    p_deriv,
    p_divmod_field,
    p_gcd_univar,
    p_scale,
    p_sub,
)


def p_deg(polynomial: Poly, variable_index: int = 0) -> int:
    return polynomial.deg_in(variable_index)


def p_lc(polynomial: Poly, variable_index: int = 0) -> DomainElement:
    """Return the leading coefficient of a nonzero polynomial."""
    top = max(polynomial.monos, key=lambda item: item[0][variable_index])
    return top[1]


def p_monic(ring: Ring, polynomial: Poly, variable_index: int = 0) -> Poly:
    if polynomial.is_zero():
        return polynomial
    return p_scale(
        ring,
        polynomial,
        ring.div_exact(ring.from_int(1), p_lc(polynomial, variable_index)),
    )


def p_div_exact(
    ring: Ring,
    numerator: Poly,
    denominator: Poly,
    variable_index: int = 0,
) -> Poly:
    quotient, remainder = p_divmod_field(
        ring, numerator, denominator, variable_index
    )
    if not remainder.is_zero():
        raise ValueError("inexact division")
    return quotient


def resultant(
    ring: Ring,
    left: Poly,
    right: Poly,
    variable_index: int = 0,
) -> DomainElement:
    """Compute a resultant by the remainder sequence recursion."""
    if left.is_zero() or right.is_zero():
        return ring.from_int(0)
    sign = ring.from_int(1)
    while True:
        left_degree = p_deg(left, variable_index)
        right_degree = p_deg(right, variable_index)
        if left_degree < right_degree:
            left, right = right, left
            left_degree, right_degree = right_degree, left_degree
            if (left_degree * right_degree) % 2:
                sign = ring.neg(sign)
        if right_degree == 0:
            constant = right.monos[0][1] if not right.is_zero() else ring.from_int(0)
            return ring.mul(sign, ring.pow_pos(constant, left_degree))
        _, remainder = p_divmod_field(ring, left, right, variable_index)
        if remainder.is_zero():
            return ring.from_int(0)
        if (left_degree * right_degree) % 2:
            sign = ring.neg(sign)
        leading = p_lc(right, variable_index)
        sign = ring.mul(
            sign,
            ring.pow_pos(leading, left_degree - p_deg(remainder, variable_index)),
        )
        left, right = right, remainder


def squarefree(ring: Ring, polynomial: Poly) -> list[tuple[Poly, int]]:
    """Return Yun squarefree decomposition over a characteristic-zero field."""
    if polynomial.is_zero() or p_deg(polynomial) == 0:
        return []
    current = p_monic(ring, polynomial)
    derivative = p_deriv(ring, current, 0)
    gcd = p_gcd_univar(ring, current, derivative)
    reduced = p_div_exact(ring, current, gcd)
    next_reduced = p_div_exact(ring, derivative, gcd)
    next_value = p_sub(ring, next_reduced, p_deriv(ring, reduced, 0))
    result: list[tuple[Poly, int]] = []
    multiplicity = 1
    while p_deg(reduced) > 0:
        factor = p_gcd_univar(ring, reduced, next_value)
        if p_deg(factor) > 0:
            result.append((factor, multiplicity))
            reduced = p_div_exact(ring, reduced, factor)
        if p_deg(factor) > 0:
            next_reduced = p_div_exact(ring, next_value, factor)
        else:
            next_reduced = next_value
        next_value = p_sub(ring, next_reduced, p_deriv(ring, reduced, 0))
        multiplicity += 1
    return result
