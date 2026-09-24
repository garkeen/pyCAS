"""Value-owned domain projection ladder."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Protocol

from cas.math.domains.base import Domain, DomainCatalog, DomainElement, Ring
from cas.math.domains.poly import from_term as poly_from_term
from cas.math.domains.poly import poly_domain
from cas.math.domains.ratfunc import ratfunc_domain, rf_from_term
from cas.syntax import term as T
from cas.syntax.term import Sym, Term
from cas.syntax.termpath import free_vars

if TYPE_CHECKING:
    from cas.math.context import MathContext


@dataclass(frozen=True, slots=True)
class Projected:
    """One domain hit; the opaque element remains owned by ``domain``."""

    domain: Domain
    element: DomainElement | None
    term: Term
    name: str


class ProjectionAttempt(Protocol):
    """Callable implementing one projection rung."""

    def __call__(
        self,
        term: Term,
        variables: tuple[Sym, ...],
    ) -> Projected | None:
        """Return a hit, or ``None`` to continue to the next rung."""

        ...


@dataclass(frozen=True, slots=True)
class ProjectionStage:
    """One named rung in an explicitly ordered projection ladder."""

    name: str
    try_projection: ProjectionAttempt


@dataclass(frozen=True, slots=True)
class ProjectionLadder:
    """The assembled projection stages and their coefficient ring."""

    stages: tuple[ProjectionStage, ...]
    coeff_ring: Ring


def _variables_of(term: Term) -> tuple[Sym, ...]:
    return tuple(sorted(free_vars(term), key=lambda symbol: symbol.name))


def _base_field_ring(domains: DomainCatalog) -> Ring:
    """Select the unique ordered Euclidean field coefficient ring."""

    domain = domains.require_unique(
        lambda candidate: (
            candidate.is_field
            and candidate.is_ordered
            and candidate.is_euclidean
            and candidate.ring is not None
        ),
        "projection coefficient ring",
    )
    if domain.ring is None:
        raise RuntimeError("selected projection domain has no coefficient ring")
    return domain.ring


def _constant_stage(domain: Domain) -> ProjectionStage:
    """Build a constant-cell rung for one resident domain."""

    def attempt(term: Term, variables: tuple[Sym, ...]) -> Projected | None:
        if variables or not domain.member(term):
            return None
        return Projected(domain, None, term, domain.name)

    return ProjectionStage(domain.name, attempt)


def _polynomial_stage(ring: Ring) -> ProjectionStage:
    def attempt(term: Term, variables: tuple[Sym, ...]) -> Projected | None:
        if not variables:
            return None
        domain = poly_domain(*variables, ring=ring)
        element = poly_from_term(ring, term, variables)
        if element is None:
            return None
        return Projected(domain, element, term, domain.name)

    return ProjectionStage("K[x]", attempt)


def _rational_function_stage(ring: Ring) -> ProjectionStage:
    def attempt(term: Term, variables: tuple[Sym, ...]) -> Projected | None:
        if not variables:
            return None
        domain = ratfunc_domain(*variables, ring=ring)
        element = rf_from_term(ring, term, variables)
        if element is None:
            return None
        return Projected(domain, element, term, domain.name)

    return ProjectionStage("K(x)", attempt)


def build_ladder(domains: DomainCatalog) -> ProjectionLadder:
    """Build a fresh ladder from an explicit domain catalog."""

    ring = _base_field_ring(domains)
    stages = (
        tuple(_constant_stage(domain) for domain in domains.resident)
        + (_polynomial_stage(ring), _rational_function_stage(ring))
    )
    return ProjectionLadder(stages=stages, coeff_ring=ring)


def project(ctx: MathContext, term: Term) -> Projected | None:
    """Project along the context's immutable ladder."""

    variables = _variables_of(term)
    for stage in ctx.projection_ladder.stages:
        hit = stage.try_projection(term, variables)
        if hit is not None:
            return hit
    return None


def is_zero(hit: Projected) -> bool:
    """Let the producing domain decide element vanishing."""

    if hit.element is None:
        return hit.domain.equal(hit.term, T.ZERO) is True
    element = hit.element
    return hit.domain.element_is_zero(element)


def normalize(hit: Projected) -> Term:
    """Let the producing domain render its normal form."""

    if hit.element is None:
        normalized = hit.domain.normalize(hit.term)
        if normalized is None:
            raise ValueError("constant projection lost its domain membership")
        return normalized
    return hit.domain.element_to_term(hit.element)


def zero_of(ctx: MathContext, term: Term) -> bool | None:
    """Return exact zerohood when a declared projection covers ``term``."""

    hit = project(ctx, term)
    if hit is None:
        return None
    return is_zero(hit)
