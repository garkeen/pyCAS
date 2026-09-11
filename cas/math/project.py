"""Domain projection layer: which domain an expression belongs to is assigned by
projection, never by leaf sniffing.

Projection is a **registered ladder**: assembly registers stages in order
(`ProjectionStage`) and `project()` tries them in turn, returning the first hit.
The ladder order is given explicitly by assembly (bootstrap -> bind_domains); it
is not an if-chain hardcoded here, and nothing is registered on import.

· resident base domains (Z / Q / Q(i)) are built by bootstrap through the builder
  and bound by `bind_domains` into constant-cell stages in the assembly-provided
  domain order;
· the K[x] and K(x) stages are registered here, and their coefficient domain is
  taken by capability through `find_domain` as the unique base field rather than
  by hardcoding `Q_RING`.

A domain enters by explicit declaration, never by name sniffing; ladder order is
given by assembly, not scattered through decision logic.

Variables are ordered lexicographically by free symbol, so the projection of an
expression is deterministic. When a tower structure is added later it appends
stages to this ladder and the protocol is unchanged.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.math.domains.base import (
    register, lookup, find_domain, set_default_coeff_ring,
)
from cas.math.domains.poly import poly_domain, from_term as poly_from_term, \
    Poly, to_term
from cas.math.domains.ratfunc import ratfunc_domain, rf_from_term, RatFunc, \
    rf_reduce, rf_to_term


@dataclass(frozen=True, slots=True)
class Projected:
    """Projection result: the domain object, the element inside it, and the
    original term."""
    domain: object          # a Domain instance
    element: object         # Poly | RatFunc; None for a constant cell
    term: object            # the original interned term
    name: str               # domain name, for step attribution display


@dataclass(frozen=True, slots=True)
class ProjectionStage:
    """One rung of the projection ladder: a name plus a try function.

    `try_fn(term, vars) -> Projected | None`; None means this rung did not hit and
    the next one is tried. Order is registration order, given explicitly by
    assembly.
    """
    name: str
    try_fn: object


_STAGES = ()


def register_stage(stage) -> None:
    """Register one projection rung at assembly time; never on import. A duplicate
    name is rejected."""
    global _STAGES
    if any(existing.name == stage.name for existing in _STAGES):
        raise ValueError(f"projection stage already registered: {stage.name}")
    _STAGES = _STAGES + (stage,)


def clear_stages() -> None:
    """Clear the ladder, for re-assembly."""
    global _STAGES
    _STAGES = ()


def _vars_of(t):
    return tuple(sorted(T.free_vars(t), key=lambda s: s.name))


def _base_field_ring():
    """The coefficient domain ring of K[x] / K(x): an **ordered Euclidean field**.

    Taken by capability rather than by hardcoding `Q_RING`. The system currently
    has exactly one match, Q; if another ordered field is added, this query fails
    loudly on an ambiguous match, because the coefficient domain is part of the
    projection semantics and an ambiguity must be resolved explicitly.
    """
    hits = find_domain(lambda d: d.is_field and d.is_ordered
                       and d.is_euclidean and d.ring is not None)
    if len(hits) != 1:
        raise RuntimeError(
            f"projection needs a unique base field, matched {[d.name for d in hits]}")
    return hits[0].ring


def _const_stage(domain) -> ProjectionStage:
    """A constant-cell rung: hits when the expression has no free variable and is
    a member of the domain."""
    def try_fn(t, vs):
        if vs or not domain.member(t):
            return None
        return Projected(domain, None, t, domain.name)
    return ProjectionStage(domain.name, try_fn)


def _poly_stage(ring) -> ProjectionStage:
    """The polynomial-ring rung: K[x1..xn]."""
    def try_fn(t, vs):
        if not vs:
            return None
        pd = poly_domain(*vs, ring=ring)
        p = poly_from_term(ring, t, vs)
        if p is None:
            return None
        return Projected(pd, p, t, pd.name)
    return ProjectionStage("K[x]", try_fn)


def _ratfunc_stage(ring) -> ProjectionStage:
    """The rational-function-field rung: K(x1..xn)."""
    def try_fn(t, vs):
        if not vs:
            return None
        rfd = ratfunc_domain(*vs, ring=ring)
        r = rf_from_term(ring, t, vs)
        if r is None:
            return None
        return Projected(rfd, r, t, rfd.name)
    return ProjectionStage("K(x)", try_fn)


def bind_domains(domains) -> None:
    """Install the resident base domains and build the projection ladder in
    order.

    The ladder order is the assembly-provided domain order (Z then Q then Q(i)),
    followed by K[x] and K(x). The coefficient ring of the parameterized domains
    is chosen here by capability and injected into the domain foundations
    (`set_default_coeff_ring`), so the domain package never has to bootstrap a
    concrete domain. Re-assembly clears the old ladder first, avoiding duplicate
    registration.
    """
    for d in domains:
        if lookup(d.name) is None:
            register(d)
    ring = _base_field_ring()
    set_default_coeff_ring(ring)
    clear_stages()
    for d in domains:
        register_stage(_const_stage(d))
    register_stage(_poly_stage(ring))
    register_stage(_ratfunc_stage(ring))


def project(t) -> Projected | None:
    """Project along the registered ladder. Returns None when every rung misses:
    honest, no guessing."""
    vs = _vars_of(t)
    for stage in _STAGES:
        hit = stage.try_fn(t, vs)
        if hit is not None:
            return hit
    return None


def is_zero(hit: Projected) -> bool:
    """Vanishing of a projected element, decided completely inside the fragment
    by the domain normal form.

    A constant cell (Z/Q/Q(i)) is decided by domain equality, uniformly for every
    constant domain rather than by type-specific cases: the hit's term is a
    member of that domain (guaranteed by the projection hit), zero is a member of
    every number domain, so equality is value comparison."""
    if hit.element is None:
        return hit.domain.equal(hit.term, T.ZERO) is True
    if isinstance(hit.element, Poly):
        return hit.element.is_zero()
    if isinstance(hit.element, RatFunc):
        return hit.element.num.is_zero()
    raise TypeError(f"unknown projected element {hit.element!r}")


def normalize(hit: Projected):
    """A projected element to its domain normal form as an interned term."""
    if hit.element is None:                 # constant cell: domain normal form
        return hit.domain.normalize(hit.term)
    if isinstance(hit.element, Poly):
        return to_term(hit.domain.ring, hit.element)
    if isinstance(hit.element, RatFunc):
        return rf_to_term(hit.domain.ring, rf_reduce(hit.domain.ring, hit.element))
    raise TypeError(f"unknown projected element {hit.element!r}")


def zero_of(t):
    """The vanishing shortcut for a term's projection: True / False / None, where
    None means non-member and outside the fragment."""
    hit = project(t)
    if hit is None:
        return None
    return is_zero(hit)
