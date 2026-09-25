"""Independent solving tactics for admitted exact fragments."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from cas.errors import TacticsError
from cas.kernel.verdict import (
    No,
    Refutation,
    RefutationChannel,
    refute,
)
from cas.math.domains.base import Ring, RingError
from cas.math.domains.poly import Poly, from_term
from cas.math.linearform import linear_form, nonzero_condition, normalized
from cas.math.project import zero_of
from cas.syntax import term as T
from cas.syntax.term import Sym, Term
from cas.syntax.termpath import free_vars, subst

if TYPE_CHECKING:
    from cas.math.context import MathContext


@dataclass(frozen=True, slots=True)
class LinearSolution:
    solution: Term
    condition: Term


@dataclass(frozen=True, slots=True)
class IdentityEquation:
    pass


@dataclass(frozen=True, slots=True)
class NonzeroEquation:
    pass


@dataclass(frozen=True, slots=True)
class LinearRefusal:
    detail: str


LinearCoreResult = LinearSolution | IdentityEquation | NonzeroEquation | LinearRefusal


@dataclass(frozen=True, slots=True)
class ConditionalSolution:
    solution: Term | None
    condition: Term


@dataclass(frozen=True, slots=True)
class PiecewiseSolutions:
    points: list[Term]
    regions: list[Term]
    conditionals: list[ConditionalSolution]
    refutations: tuple[Refutation, ...] = ()


def _nonzero_difference(difference: Term, detail: str) -> No:
    return refute(
        RefutationChannel.NORMAL_FORM,
        T.eq(difference, T.ZERO),
        difference,
        T.ZERO,
        detail=detail,
    )

def _lin_core(
    ctx: MathContext,
    difference: Term,
    variable: Sym,
) -> LinearCoreResult:
    form = linear_form(ctx, difference, variable)
    if form.kind == "linear":
        payload = form.payload
        if not isinstance(payload, tuple) or len(payload) != 2:
            raise TacticsError("linear-form payload is malformed")
        coefficient, constant = payload
        normalized_coefficient = normalized(ctx, coefficient)
        solution = normalized(
            ctx,
            T.times(T.neg(constant), T.pw(normalized_coefficient, T.MONE)),
        )
        return LinearSolution(
            solution,
            nonzero_condition(normalized_coefficient),
        )
    if form.kind == "zero":
        return IdentityEquation()
    if form.kind in ("constant", "independent"):
        return NonzeroEquation()
    if form.kind in ("outside", "no_view"):
        return LinearRefusal(str(form.payload))
    return LinearRefusal(
        f"degree {form.payload} equation: only linear is supported"
    )


def solve_linear_with_condition(
    ctx: MathContext,
    content: Term,
    variable: Sym,
) -> tuple[Term, Term]:
    """Return a linear candidate and its required nonzero slope condition."""
    if not (isinstance(content, T.Expr) and content.head.name == "Eq"):
        raise TacticsError("solve needs an equation")
    left, right = content.args
    result = _lin_core(ctx, T.plus(left, T.neg(right)), variable)
    if isinstance(result, LinearSolution):
        return result.solution, result.condition
    if isinstance(result, IdentityEquation):
        raise TacticsError(
            "identity: the solution set is everything, no unique solution"
        )
    if isinstance(result, NonzeroEquation):
        raise TacticsError(
            "contradictory equation: independent of the variable and never zero"
        )
    raise TacticsError(result.detail)


def solve_linear(
    ctx: MathContext,
    content: Term,
    variable: Sym,
) -> Term:
    """Return the linear candidate; its condition is available separately."""
    return solve_linear_with_condition(ctx, content, variable)[0]


def _integer_ring(ctx: MathContext) -> Ring:
    """Select the unique Euclidean non-field coefficient ring."""
    try:
        domain = ctx.domains.require_unique(
            lambda candidate: (
                candidate.is_euclidean
                and not candidate.is_field
                and candidate.ring is not None
            ),
            "Diophantine host ring",
        )
    except RingError as error:
        raise TacticsError(str(error)) from error
    if domain.ring is None:
        raise TacticsError("selected Diophantine domain has no ring")
    return domain.ring


def solve_diophantine_linear(
    ctx: MathContext,
    a: int,
    b: int,
    c: int,
) -> tuple[tuple[int, int], tuple[int, int]]:
    """Return a point and direction for ``a*x + b*y = c``."""
    ring = _integer_ring(ctx)
    raw_g, raw_s, raw_t = ring.xgcd(ring.from_int(a), ring.from_int(b))
    g = ring.integer_value(raw_g)
    s = ring.integer_value(raw_s)
    t = ring.integer_value(raw_t)
    if g is None or s is None or t is None:
        raise TacticsError("extended gcd returned a non-integral coefficient")
    if g == 0:
        if c != 0:
            raise TacticsError(f"0 = {c} != 0: no solution")
        return (0, 0), (1, 0)
    if c % g != 0:
        raise TacticsError(
            f"no integer solution: gcd({a},{b})={g} does not divide {c}"
        )
    multiple = c // g
    return (s * multiple, t * multiple), (b // g, -a // g)


def integer_roots(polynomial: Poly, variable: Sym, ring: Ring) -> list[int]:
    """Return all roots in the one-variable integer fragment."""
    if variable not in polynomial.vars:
        return []
    variable_index = polynomial.vars.index(variable)
    other_indices = [
        index
        for index in range(len(polynomial.vars))
        if index != variable_index
    ]
    coefficients: dict[int, int] = {}
    for monomial, coefficient in polynomial.monos:
        if any(monomial[index] for index in other_indices):
            raise TacticsError(
                "involves other variables: only single-variable is supported"
            )
        integer = ring.integer_value(coefficient)
        if integer is None:
            raise TacticsError(
                "non-integer coefficients: outside the integer-root fragment"
            )
        coefficients[monomial[variable_index]] = integer
    if not coefficients:
        return []
    roots: list[int] = []
    while coefficients.get(0, 0) == 0:
        roots.append(0)
        coefficients = {
            exponent - 1: coefficient
            for exponent, coefficient in coefficients.items()
            if exponent > 0
        }
        if not coefficients:
            return roots
    degree = max(coefficients)
    constant = coefficients[0]
    from cas.math.realroot import divisors

    candidates: set[int] = set()
    for divisor in divisors(constant):
        candidates.update((divisor, -divisor))
    for root in sorted(candidates):
        accumulator = coefficients[degree]
        for exponent in range(degree - 1, -1, -1):
            accumulator = accumulator * root + coefficients.get(exponent, 0)
        if accumulator == 0:
            roots.append(root)
    return sorted(set(roots))


def integer_roots_of_term(
    ctx: MathContext,
    term: Term,
    variable: Sym,
) -> list[int]:
    """All integer roots of a univariate integer-coefficient polynomial term.

    The host ring is the unique Euclidean non-field domain of the assembled
    catalog, so the caller passes a term rather than a ring.
    """
    if variable not in free_vars(term):
        return []
    ring = _integer_ring(ctx)
    polynomial = from_term(ring, term, (variable,))
    if polynomial is None:
        raise TacticsError("not a polynomial over the integer ring")
    return integer_roots(polynomial, variable, ring)


def solve_piecewise(
    ctx: MathContext,
    function: Term,
    variable: Sym,
    target: Term,
) -> PiecewiseSolutions:
    """Solve a piecewise equation completely inside the linear fragment."""
    from cas.kernel.scope import Assumptions
    from cas.math.decide import decide
    from cas.math.domains.qarith import fold
    from cas.math.piecewise import branches, fold_nested, is_piecewise

    if not is_piecewise(function):
        raise TacticsError("solve_piecewise needs a piecewise function")
    flattened = fold_nested(function)
    points: list[Term] = []
    regions: list[Term] = []
    conditionals: list[ConditionalSolution] = []
    refutations: list[Refutation] = []
    for value, condition in branches(flattened):
        difference = fold(T.plus(value, T.neg(target)))
        if variable not in free_vars(difference):
            zero = zero_of(ctx, difference)
            if zero is True:
                regions.append(condition)
            elif zero is False:
                refutations.append(
                    _nonzero_difference(
                        difference,
                        "the branch difference has a nonzero normal form",
                    ).evidence
                )
            else:
                conditionals.append(ConditionalSolution(None, condition))
            continue
        result = _lin_core(ctx, difference, variable)
        if isinstance(result, IdentityEquation):
            regions.append(condition)
            continue
        if isinstance(result, NonzeroEquation):
            refutations.append(
                _nonzero_difference(
                    difference,
                    "the branch equation is independent and nonzero",
                ).evidence
            )
            continue
        if isinstance(result, LinearRefusal):
            raise TacticsError(
                "branch equation is outside the linear fragment, completeness "
                f"cannot be guaranteed: {result.detail}"
            )
        substituted_condition = fold(
            subst(condition, {variable: result.solution})
        )
        verdict = decide(
            ctx,
            substituted_condition,
            Assumptions(),
        )
        if verdict.is_yes():
            points.append(result.solution)
        elif isinstance(verdict, No):
            refutations.append(verdict.evidence)
        else:
            conditionals.append(
                ConditionalSolution(result.solution, condition)
            )
    return PiecewiseSolutions(points, regions, conditionals, tuple(refutations))
