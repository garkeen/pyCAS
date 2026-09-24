"""Z: an ordered Euclidean integral domain, not a field."""

from fractions import Fraction

from cas.math.domains.base import Domain, DomainCapabilities, DomainElement, Ring, RingError
from cas.math.domains.qarith import EvalNumError, eval_exact, fold
from cas.syntax.term import Term


class ZZRing(Ring):
    """The integer ring: native int arithmetic with no wrapping."""

    is_euclidean = True

    def from_int(self, value: int) -> DomainElement:
        return value

    def from_frac(self, value: Fraction) -> DomainElement:
        if value.denominator != 1:
            raise RingError(f"Z does not contain the rational {value}")
        return value.numerator

    def add(self, left: DomainElement, right: DomainElement) -> DomainElement:
        if not isinstance(left, int) or not isinstance(right, int):
            raise TypeError("Z ring elements must be integers")
        return left + right

    def neg(self, value: DomainElement) -> DomainElement:
        if not isinstance(value, int):
            raise TypeError("Z ring elements must be integers")
        return -value

    def mul(self, left: DomainElement, right: DomainElement) -> DomainElement:
        if not isinstance(left, int) or not isinstance(right, int):
            raise TypeError("Z ring elements must be integers")
        return left * right

    def equal(self, left: DomainElement, right: DomainElement) -> bool:
        return left == right

    def divmod_(self, left: DomainElement, right: DomainElement) -> tuple[DomainElement, DomainElement]:
        if not isinstance(left, int) or not isinstance(right, int):
            raise TypeError("Z ring elements must be integers")
        if right == 0:
            raise ZeroDivisionError("division by zero")
        quotient, remainder = divmod(left, right)
        if right < 0 and remainder > 0:
            quotient += 1
            remainder -= right
        return quotient, remainder

    def xgcd(self, left: DomainElement, right: DomainElement) -> tuple[DomainElement, DomainElement, DomainElement]:
        if not isinstance(left, int) or not isinstance(right, int):
            raise TypeError("Z ring elements must be integers")
        old_r, remainder = left, right
        old_s, s = 1, 0
        old_t, t = 0, 1
        while remainder != 0:
            quotient, rem = divmod(old_r, remainder)
            old_r, remainder = remainder, rem
            old_s, s = s, old_s - quotient * s
            old_t, t = t, old_t - quotient * t
        if old_r < 0:
            return -old_r, -old_s, -old_t
        return old_r, old_s, old_t

    def integer_value(self, value: DomainElement) -> int | None:
        return value if isinstance(value, int) else None


Z_RING = ZZRing()


class ZDomain(Domain):
    """The integers Z."""

    name = "Z"
    capabilities = DomainCapabilities(ordered=True, euclidean=True)
    ring = Z_RING

    def member(self, term: Term) -> bool:
        try:
            value = eval_exact(term, {})
        except (EvalNumError, ZeroDivisionError):
            return False
        return value.denominator == 1

    def normalize(self, term: Term) -> Term | None:
        if not self.member(term):
            return None
        return fold(term)

    def equal(self, left: Term, right: Term) -> bool | None:
        if not (self.member(left) and self.member(right)):
            return None
        return eval_exact(left, {}) == eval_exact(right, {})


Z_DOMAIN = ZDomain()
