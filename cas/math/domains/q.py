"""The field Q: literal rational arithmetic.

Normal form: qarith.fold, folding all-numeric subtrees exactly and absorbing
identity elements.
Equality: numeric comparison after folding, decided completely inside the
fragment.
Membership: an all-numeric tree, i.e. exact evaluation succeeds in an empty
environment.
"""

from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.math.domains.qarith import fold, eval_exact, EvalNumError
from cas.math.domains.base import Domain, FracRing


class QRing(FracRing):
    """The coefficient ring Q: native Fraction arithmetic with no wrapping."""

    is_euclidean = True

    def from_int(self, n):
        return Fr(n)

    def from_frac(self, f):
        return f

    def add(self, a, b):
        return a + b

    def neg(self, a):
        return -a

    def mul(self, a, b):
        return a * b

    def divmod_(self, a, b):
        return a / b, Fr(0)


Q_RING = QRing()


class QDomain(Domain):
    """The rational field Q."""

    name = "Q"
    is_field = True
    is_ordered = True
    is_euclidean = True
    ring = Q_RING

    def member(self, t) -> bool:
        try:
            eval_exact(t, {})
            return True
        except (EvalNumError, ZeroDivisionError):
            return False

    def normalize(self, t):
        if not self.member(t):
            return None
        return fold(t)

    def equal(self, a, b):
        if not (self.member(a) and self.member(b)):
            return None                  # non-member: the caller overstepped
        return T.num_val(fold(a)) == T.num_val(fold(b))


# The singleton. Registration is not this module's business: the domain package
# only declares, and registration into the ladder belongs to the projection layer.
Q_DOMAIN = QDomain()
