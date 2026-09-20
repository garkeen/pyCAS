"""Domain projection layer: which domain an expression belongs to is assigned by
projection, never by leaf sniffing.

Projection is a **registered ladder**: assembly builds the rungs in order
(`ProjectionStage`) and `project` tries them in turn, returning the first hit.
The ladder is a value produced by `build_ladder`, not module-level state, and the
caller passes it in through the math context -- so nothing is registered on import
and no assembly-time write is hidden behind a module global.

· resident base domains (Z / Q / Q(i)) are built by bootstrap through the builder
  and bound here into constant-cell rungs in the assembly-provided domain order;
· the K[x] and K(x) stages are built here, and their coefficient domain is taken
  by capability through `find_domain` as the unique base field rather than by
  hardcoding `Q_RING`.

A domain enters by explicit declaration, never by name sniffing; ladder order is
given by assembly, not scattered through decision logic.

Variables are ordered lexicographically by free symbol, so the projection of an
expression is deterministic. When a tower structure is added later it appends
stages to this ladder and the protocol is unchanged.
"""

from dataclasses import dataclass

from cas.syntax import term as T
from cas.math.domains.base import (
    register, lookup, find_domain,
)
from cas.math.domains.poly import poly_domain, from_term as poly_from_term
from cas.math.domains.ratfunc import ratfunc_domain, rf_from_term


@dataclass(frozen=True, slots=True)
class Projected:
    """Projection result: the domain object, the element inside it, and the
    original term.

    `element` is opaque here: the producing domain consumes it
    (`element_is_zero` / `element_to_term`) and this layer never inspects its
    representation. None marks a constant cell, whose term the domain consumes
    directly."""
    domain: object          # a Domain instance
    element: object         # the producing domain's own element; None for a constant cell
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


@dataclass(frozen=True, slots=True)
class ProjectionLadder:
    """The assembled ladder: the rungs in order, plus the coefficient ring the
    parameterized rungs were built with.

    A value, not a registry: `build_ladder` returns it, the caller keeps it (in the
    math context), and a test that wants its own rung builds its own ladder
    instead of mutating a shared one.
    """
    stages: tuple
    coeff_ring: object


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


def build_ladder(domains) -> ProjectionLadder:
    """Register the resident base domains and build the projection ladder in
    order.

    The ladder order is the assembly-provided domain order (Z then Q then Q(i)),
    followed by K[x] and K(x). The coefficient ring of the parameterized domains
    is chosen here by capability and carried in the returned value, so the domain
    package never has to bootstrap a concrete domain and no module-level default
    ring is needed. Re-assembly builds a fresh ladder rather than appending to an
    old one, so duplicate rungs cannot accumulate.
    """
    for d in domains:
        if lookup(d.name) is None:
            register(d)
    ring = _base_field_ring()
    stages = (tuple(_const_stage(d) for d in domains)
              + (_poly_stage(ring), _ratfunc_stage(ring)))
    return ProjectionLadder(stages=stages, coeff_ring=ring)


def project(ctx, t) -> Projected | None:
    """Project along the context's ladder. Returns None when every rung misses:
    honest, no guessing."""
    vs = _vars_of(t)
    for stage in ctx.projection_stages:
        hit = stage.try_fn(t, vs)
        if hit is not None:
            return hit
    return None


def is_zero(hit: Projected) -> bool:
    """Vanishing of a projected element, decided completely inside the fragment
    by the domain normal form.

    The producing domain consumes its own element; a constant cell (Z/Q/Q(i))
    is decided by domain equality, uniformly for every constant domain rather
    than by type-specific cases: the hit's term is a member of that domain
    (guaranteed by the projection hit), zero is a member of every number
    domain, so equality is value comparison."""
    if hit.element is None:
        return hit.domain.equal(hit.term, T.ZERO) is True
    return hit.domain.element_is_zero(hit.element)


def normalize(hit: Projected):
    """A projected element to its domain normal form as an interned term.

    The producing domain consumes its own element; a constant cell goes through
    the domain normal form directly."""
    if hit.element is None:                 # constant cell: domain normal form
        return hit.domain.normalize(hit.term)
    return hit.domain.element_to_term(hit.element)


def zero_of(ctx, t):
    """The vanishing shortcut for a term's projection: True / False / None, where
    None means non-member and outside the fragment."""
    hit = project(ctx, t)
    if hit is None:
        return None
    return is_zero(hit)
