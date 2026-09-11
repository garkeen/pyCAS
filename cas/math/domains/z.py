"""Z: an ordered Euclidean integral domain, not a field.

Two reasons it is a first-class domain:
· factorization must pass through it: Zassenhaus lifts to Z[x] (content and
  primitive part);
· it hosts the decidable Diophantine fragment: linear Diophantine equations by
  the extended Euclidean algorithm and univariate integer roots by the rational
  root theorem. The general multivariate Diophantine problem is UNDECIDABLE by
  Hilbert's tenth problem, which is a theorem rather than a TODO.

Division uses the Euclidean convention that the remainder has the same sign as
the divisor (|r| < |b| and r >= 0 when b > 0), which keeps the gcd chain
strictly decreasing.
"""

from fractions import Fraction as Fr

from cas.math.qarith import fold, eval_exact, EvalNumError
from cas.math.domains.base import Domain, Ring, RingError


class ZZRing(Ring):
    """The integer ring: native int arithmetic with no wrapping."""

    is_euclidean = True

    def from_int(self, n):
        return int(n)

    def from_frac(self, f):
        if f.denominator != 1:
            raise RingError(f"Z does not contain the rational {f}")
        return f.numerator

    def add(self, a, b):
        return a + b

    def neg(self, a):
        return -a

    def mul(self, a, b):
        return a * b

    def equal(self, a, b):
        return a == b

    def divmod_(self, a, b):
        if b == 0:
            raise ZeroDivisionError("division by zero")
        q, r = divmod(a, b)
        if b < 0 and r > 0:              # make the remainder share the divisor's sign
            q += 1
            r -= b
        return q, r

    def xgcd(self, a, b):
        """Extended Euclidean algorithm: return (g, s, t) with s*a + t*b = g =
        gcd(a, b)."""
        old_r, r = a, b
        old_s, s = 1, 0
        old_t, t = 0, 1
        while r != 0:
            q, rem = self.divmod_(old_r, r)
            old_r, r = r, rem
            old_s, s = s, old_s - q * s
            old_t, t = t, old_t - q * t
        if old_r < 0:
            return -old_r, -old_s, -old_t
        return old_r, old_s, old_t


Z_RING = ZZRing()


class ZDomain(Domain):
    """The integers Z, as the first rung of the domain ladder: solving semantics
    is divisibility, not division."""

    name = "Z"
    is_ordered = True
    is_euclidean = True
    ring = Z_RING

    def member(self, t) -> bool:
        try:
            v = eval_exact(t, {})
        except (EvalNumError, ZeroDivisionError):
            return False
        return isinstance(v, Fr) and v.denominator == 1

    def normalize(self, t):
        if not self.member(t):
            return None
        return fold(t)

    def equal(self, a, b):
        if not (self.member(a) and self.member(b)):
            return None
        return eval_exact(a, {}) == eval_exact(b, {})


# The singleton. Registration is not this module's business: the domain package
# only declares, and assembly (including registration into the projection ladder)
# belongs to the projection layer.
Z_DOMAIN = ZDomain()
