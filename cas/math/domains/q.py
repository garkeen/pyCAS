"""The field Q: literal rational arithmetic."""

from fractions import Fraction

from cas.math.domains.base import Domain, DomainCapabilities, DomainElement, FracRing
from cas.math.domains.qarith import EvalNumError, eval_exact, fold
from cas.syntax.term import Term


class QRing(FracRing):
    """The coefficient ring Q: native Fraction arithmetic with no wrapping."""

    is_euclidean = True
    supports_rational_evaluation = True

    def from_int(self, value: int) -> DomainElement:
        return Fraction(value)

    def from_frac(self, value: Fraction) -> DomainElement:
        return value

    def to_fraction(self, value: DomainElement) -> Fraction:
        if not isinstance(value, Fraction):
            raise TypeError("Q ring elements must be Fractions")
        return value

    def add(self, left: DomainElement, right: DomainElement) -> DomainElement:
        if not isinstance(left, Fraction) or not isinstance(right, Fraction):
            raise TypeError("Q ring elements must be Fractions")
        return left + right

    def neg(self, value: DomainElement) -> DomainElement:
        if not isinstance(value, Fraction):
            raise TypeError("Q ring elements must be Fractions")
        return -value

    def mul(self, left: DomainElement, right: DomainElement) -> DomainElement:
        if not isinstance(left, Fraction) or not isinstance(right, Fraction):
            raise TypeError("Q ring elements must be Fractions")
        return left * right

    def divmod_(self, left: DomainElement, right: DomainElement) -> tuple[DomainElement, DomainElement]:
        if not isinstance(left, Fraction) or not isinstance(right, Fraction):
            raise TypeError("Q ring elements must be Fractions")
        return left / right, Fraction(0)


Q_RING = QRing()


class QDomain(Domain):
    """The rational field Q."""

    name = "Q"
    capabilities = DomainCapabilities(field=True, ordered=True, euclidean=True)
    ring = Q_RING

    def member(self, term: Term) -> bool:
        try:
            eval_exact(term, {})
            return True
        except (EvalNumError, ZeroDivisionError):
            return False

    def normalize(self, term: Term) -> Term | None:
        if not self.member(term):
            return None
        return fold(term)

    def equal(self, left: Term, right: Term) -> bool | None:
        if not (self.member(left) and self.member(right)):
            return None
        return eval_exact(left, {}) == eval_exact(right, {})


Q_DOMAIN = QDomain()
