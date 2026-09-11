"""Number-field system foundations: the domain protocol and the coefficient-ring
protocol.

Layer discipline: this package depends only on cas.syntax.term and is consumed by
the decision and simplification layers above it; it never imports upward. Domains
are the foundation and the decision pipeline sits on top of them.

Design decisions:
· every domain provides normalize (normal form), equal (complete equality
  decision) and member (membership test);
· a domain enters by explicit declaration, never by leaf sniffing;
· `equal` is defined only for members and decides completely inside the
  fragment. It returns a bool; a non-member returns None, meaning the caller
  overstepped. "Unknown" is never produced inside a domain, because three-valued
  decisions belong to the decision layer.
· the derivation D belongs to the domain protocol: a coefficient ring's
  derivation defaults to zero (constant domains) and is overridden as the
  extension grows -- an algebraic extension uses D(alpha) = -D(m)(alpha)/m'(alpha),
  and a transcendental extension is given by the generator's defining equation.
"""

from abc import ABC, abstractmethod
from fractions import Fraction as Fr


class Ring(ABC):
    """Coefficient-ring protocol: everything a polynomial domain requires of its
    coefficient structure.

    A coefficient value is an opaque object; the ring owns its arithmetic and
    equality. The rational ring uses native Fraction arithmetic directly, with no
    wrapping overhead.

    Capability fields: algorithms dispatch on capability, never on type.
    · is_field: nonzero elements are invertible, so exact division is available
    · is_euclidean: division with remainder is available (divmod/gcd implemented)
    """

    is_field = False
    is_euclidean = False

    @abstractmethod
    def from_int(self, n: int):
        """Embed an integer."""

    @abstractmethod
    def from_frac(self, f: Fr):
        """Embed a rational; raises RingError when the ring does not contain Q."""

    @abstractmethod
    def add(self, a, b): ...

    @abstractmethod
    def neg(self, a): ...

    @abstractmethod
    def mul(self, a, b): ...

    @abstractmethod
    def equal(self, a, b) -> bool: ...

    def is_zero(self, a) -> bool:
        return self.equal(a, self.from_int(0))

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def divmod_(self, a, b):
        """Division with remainder, (q, r). A Euclidean ring overrides this;
        otherwise it refuses."""
        raise RingError(f"{type(self).__name__} is not a Euclidean ring")

    def deriv(self, c):
        """The coefficient derivation: identically zero on a constant domain. An
        extension ring overrides it, because the derivation belongs to the domain
        protocol."""
        return self.from_int(0)

    def pow_pos(self, a, n: int):
        """a ** n for n >= 0, by fast exponentiation."""
        r = self.from_int(1)
        while n:
            if n & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            n >>= 1
        return r


class RingError(Exception):
    pass


class FracRing(Ring):
    """Shared part of coefficient rings containing Q: exact division, zero and
    one constants, equality."""

    is_field = True

    def div_exact(self, a, b):
        """Exact division by a nonzero element of the field."""
        if self.is_zero(b):
            raise ZeroDivisionError("division by zero")
        return a / b

    def equal(self, a, b) -> bool:
        return a == b


class Domain(ABC):
    """Number-field protocol: normalization, equality and membership in one.

    · normalize(t) -> Term | None: returns None for a non-member, and the normal
      form (an interned term, so identical forms share a pointer) for a member.
    · equal(a, b) -> bool | None: defined only for members and decided completely
      inside the fragment; a non-member returns None, meaning the caller
      overstepped. No three-valued result is produced here.

    Capability fields: is_field (nonzero elements invertible), is_ordered (an
    order is available), is_euclidean (division with remainder). Algorithms
    dispatch on capability.

    ring: the domain's coefficient ring (its arithmetic realization). A constant
    domain uses its own ring (Q -> QRing, Z -> ZZRing, Q(i) -> QIRing) and a
    polynomial/rational-function domain uses its coefficient ring. An algorithm
    needing "the ring of some capable domain" takes it through find_domain by
    capability rather than hardcoding a specific singleton.

    scoped: True marks a single-computation domain (an algebraic extension or a
    radical parameter). Such a domain must not be registered resident and must be
    confined to one computation by domain_scope, because a resident registration
    would leak into every later computation.
    """

    name: str = "?"
    is_field = False
    is_ordered = False
    is_euclidean = False
    scoped = False
    ring = None

    @abstractmethod
    def normalize(self, t): ...

    @abstractmethod
    def equal(self, a, b): ...


_DOMAINS = {}
_SCOPES = []


def register(d: Domain) -> Domain:
    """Resident registration, for system base domains only (Z / Q / Q(i) / K[x] /
    K(x) and the like).

    A scoped single-computation domain (an algebraic extension or a radical
    parameter) must be registered through domain_scope: a resident registration
    would leak it into every later computation.
    """
    if getattr(d, "scoped", False):
        raise ValueError(
            f"scoped domain must be registered through domain_scope(): {d.name}")
    if d.name in _DOMAINS and _DOMAINS[d.name] is not d:
        raise ValueError(f"domain redeclared: {d.name}")
    _DOMAINS[d.name] = d
    return d


class domain_scope:
    """Temporary domain registration for one computation's scope.

    Algebraic domains and radical parameters are only allowed to live inside this
    scope: exit (including on an exception) unconditionally unregisters them, so
    they never leak into a later computation. A name colliding with a resident
    base domain or an outer scope is rejected, because shadowing an existing
    domain is exactly the precursor of a leak.

    Usage:
        with domain_scope(QAlphaDomain(...)):
            ...            # lookup hits the temporary domain inside this block
        # unregistered on exit
    """

    def __init__(self, *domains):
        self._domains = domains

    def __enter__(self):
        frame = {}
        for d in self._domains:
            if d.name in _DOMAINS or any(d.name in f for f in _SCOPES):
                raise ValueError(f"scoped domain collides with an existing registration: {d.name}")
            frame[d.name] = d
        _SCOPES.append(frame)
        return self

    def __exit__(self, *exc):
        _SCOPES.pop()
        return False


def lookup(name):
    """Look a domain up by name: inner scopes first, then resident base domains;
    returns None when not found."""
    for frame in reversed(_SCOPES):
        hit = frame.get(name)
        if hit is not None:
            return hit
    return _DOMAINS.get(name)


def find_domain(predicate):
    """Look resident base domains up by **capability predicate**, never by name or
    Python type.

    Returns every match in registration order. This is the mechanical channel for
    capability-based domain dispatch: an algorithm expresses the capability it
    needs (for example `lambda d: d.is_field and d.is_ordered`) and the query
    matches it, instead of hardcoding `Q_RING` in the algorithm body.

    Ambiguity is not resolved here: zero or several matches are returned as they
    are and the caller decides, usually requiring uniqueness and raising on an
    ambiguous match. Silently taking the first would hide the ambiguity.
    """
    return tuple(d for d in _DOMAINS.values() if predicate(d))


# ---------------------------------------------------------------------------
# The default coefficient ring for parameterized domains (the K in K[x] / K(x))
#
# Injected at assembly time (bootstrap -> the projection layer picks a base field
# by capability): the domain package neither hardcodes Q_RING nor bootstraps a
# concrete domain on import or first call. An unset ring raises, because a silent
# default domain would turn "forgot to assemble" into a hard-to-find wrong answer.
# ---------------------------------------------------------------------------

_DEFAULT_COEFF_RING = None


def set_default_coeff_ring(ring) -> None:
    """Inject the default coefficient ring of K[x] / K(x) at assembly time."""
    global _DEFAULT_COEFF_RING
    _DEFAULT_COEFF_RING = ring


def default_coeff_ring():
    """Take the default coefficient ring; raises when not assembled, failing
    loudly instead of degrading silently."""
    if _DEFAULT_COEFF_RING is None:
        raise RingError("default coefficient ring is not assembled: call "
                        "bootstrap() first (the domain package never bootstraps "
                        "a concrete domain itself)")
    return _DEFAULT_COEFF_RING
