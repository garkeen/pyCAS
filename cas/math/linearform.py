# -*- coding: utf-8 -*-
"""The single implementation of linear-form decomposition and classification.

The syntactic channel is used by the constraint solver, where coefficients may
be arbitrary terms.  The semantic channel is used by the solving tactic, where
the domain's own polynomial view is the authority.  Keeping both channels here
prevents the two notions of linearity from drifting apart.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.syntax.term import Sym
from cas.math.domains.poly import _norm, to_term
from cas.math.project import is_zero, normalize as proj_normalize, project


# ---------------------------------------------------------------------------
# Syntactic channel


def decompose(t, unknowns):
    """Return ``(coefficients, constant)`` or ``None``.

    A coefficient is a term that contains none of ``unknowns``.  This channel
    intentionally does not use semantic simplification: it is the exact input
    format of the linear Gaussian eliminator.
    """
    unknowns = tuple(unknowns)
    unknown_set = set(unknowns)
    if t in unknown_set:
        return ({t: T.ONE}, T.ZERO)
    if not (T.free_vars(t) & unknown_set):
        return ({}, t)
    if not isinstance(t, T.Expr):
        return None
    name = t.head.name
    if name == "Plus":
        coeffs, const = {}, T.ZERO
        for arg in t.args:
            part = decompose(arg, unknowns)
            if part is None:
                return None
            for key, value in part[0].items():
                coeffs[key] = T.plus(coeffs.get(key, T.ZERO), value)
            const = T.plus(const, part[1])
        return coeffs, const
    if name == "Times":
        parts = [decompose(arg, unknowns) for arg in t.args]
        if any(part is None for part in parts):
            return None
        unknown_indices = [i for i, part in enumerate(parts) if part[0]]
        if len(unknown_indices) > 1:
            return None
        if not unknown_indices:
            product = T.ONE
            for _coeffs, const in parts:
                product = T.times(product, const)
            return {}, product
        index = unknown_indices[0]
        factor = T.ONE
        for i, (_coeffs, const) in enumerate(parts):
            if i != index:
                factor = T.times(factor, const)
        coeffs, const = parts[index]
        return ({key: T.times(value, factor)
                 for key, value in coeffs.items()},
                T.times(const, factor))
    if name == "Power" and len(t.args) == 2 and t.args[1] is T.ONE:
        return decompose(t.args[0], unknowns)
    return None


def is_linear(t, unknowns):
    """Whether ``t`` is linear in the given unknowns."""
    return decompose(t, unknowns) is not None


def normalized(ctx, t):
    """Normalize a coefficient through the projection, or fold literals."""
    hit = project(ctx, t)
    if hit is not None:
        return proj_normalize(hit)
    from cas.math.domains.qarith import fold
    return fold(t)


def relation(ctx, rel, unknowns):
    """Convert an equation to ``(row, rhs)`` for ``sum(row_i*u_i)=rhs``."""
    if not (isinstance(rel, T.Expr) and isinstance(rel.head, Sym)
            and rel.head.name == "Eq"):
        return None
    lhs, rhs = rel.args
    left = decompose(lhs, unknowns)
    right = decompose(rhs, unknowns)
    if left is None or right is None:
        return None
    left_coeffs, left_const = left
    right_coeffs, right_const = right
    row = [normalized(ctx, T.plus(left_coeffs.get(u, T.ZERO),
                                  T.neg(right_coeffs.get(u, T.ZERO))))
           for u in unknowns]
    rhs_value = normalized(ctx, T.plus(right_const, T.neg(left_const)))
    return row, rhs_value


# ---------------------------------------------------------------------------
# Semantic channel


@dataclass(frozen=True, slots=True)
class LinearForm:
    """The result of reading linearity from a domain polynomial view."""

    kind: str
    payload: object = None


def _coefficient(ring, monos, var_index, power, rest_vars):
    coefficients = {}
    for exponents, value in monos:
        if exponents[var_index] == power:
            coefficients[tuple(e for i, e in enumerate(exponents)
                              if i != var_index)] = value
    return to_term(ring, _norm(ring, rest_vars, coefficients))


def linear_form(ctx, t, var: Sym) -> LinearForm:
    """Classify ``t`` as a linear form in ``var``.

    Other symbols are parameters.  ``outside``, ``no_view``, ``degree`` and
    ``independent`` are explicit refusal/classification outcomes; only
    ``linear`` supplies a candidate coefficient pair.
    """
    hit = project(ctx, t)
    if hit is None:
        return LinearForm("outside", "outside the declared projection domains")
    if hit.element is None:
        return LinearForm("constant", is_zero(hit))
    element = hit.domain.element_poly(hit.element)
    if element is None:
        return LinearForm("no_view", "the projected domain exposes no polynomial view")
    if element.is_zero():
        return LinearForm("zero")
    if var not in element.vars:
        return LinearForm("independent")
    index = element.vars.index(var)
    powers = {monomial[index] for monomial, _value in element.monos}
    degree = max(powers)
    if degree == 0:
        return LinearForm("independent")
    if degree != 1:
        return LinearForm("degree", degree)
    rest_vars = tuple(v for i, v in enumerate(element.vars) if i != index)
    return LinearForm(
        "linear",
        (_coefficient(hit.domain.ring, element.monos, index, 1, rest_vars),
         _coefficient(hit.domain.ring, element.monos, index, 0, rest_vars)),
    )


def nonzero_condition(coefficient):
    """Return the domain condition needed to divide by a linear coefficient."""
    return T.mk(T.S("Ne"), (coefficient, T.ZERO))
