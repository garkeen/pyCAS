# -*- coding: utf-8 -*-
"""Q(i), the Gaussian field: the first algebraic extension.

Element representation is the normal-form pair (re, im) with re, im in Q. The
quotient-ring view makes the structure plain: Q(i) = Q[z]/(z^2+1), the normal form
is unique so equality is structural equality, multiplication is the direct dual
operation (ac-bd, ad+bc) -- the d=2 instance of polynomial arithmetic modulo
x^2+1 -- and division goes through the conjugate times the norm.

Membership channel: in a closed term, replace the constant i by a fresh variable z,
project to the rational function field Q(z) (reusing the existing rf machinery),
reduce numerator and denominator modulo z^2+1 separately, and multiply the
numerator by the inverse of the denominator. Since x^2+1 is irreducible over Q, a
nonzero denominator has nonzero norm after reduction and is always invertible --
which is exactly why Q(i) is a field; a denominator reducing to zero means the
original term divided by zero, i.e. not a member.

Layer discipline: this module depends only on cas.syntax.term and the base of this
package (plus the poly/ratfunc machinery shared with q/qarith). The identity of the
constant i is injected by the constructor -- the declaration layer owns constant
declarations and the projection layer wires them -- never by name sniffing.

Capabilities (algorithms dispatch on capabilities, never on type):
* is_field = True: Q(i) is a field. Irreducibility of x^2+1 is a construction
  premise carried by the declaration, not checked at runtime.
* is_ordered = False: the complex field is unordered, so every order test must be
  refused by capability lookup.
* is_euclidean = False: the division with remainder / Euclidean structure belongs to
  Z[i] via the norm function; Q(i) as a field needs no such declaration.
"""

from fractions import Fraction as Fr

from cas.syntax import term as T
from cas.syntax.term import Sym
from cas.math.domains.qarith import fold
from cas.math.domains.base import Domain, Ring
from cas.math.domains.q import Q_RING
from cas.math.domains.poly import Poly
from cas.math.domains.ratfunc import rf_from_term


# ---------------------------------------------------------------------------
# Coefficient ring: arithmetic on normal-form pairs
# ---------------------------------------------------------------------------

class QIRing(Ring):
    """Q(i) coefficient ring: elements are (re, im) pairs, and the normal form is
    the representation itself (equality is structural equality)."""

    is_field = True

    def from_int(self, n):
        return (Fr(n), Fr(0))

    def from_frac(self, f):
        return (Fr(f), Fr(0))

    def add(self, a, b):
        return (a[0] + b[0], a[1] + b[1])

    def neg(self, a):
        return (-a[0], -a[1])

    def mul(self, a, b):
        return (a[0] * b[0] - a[1] * b[1],
                a[0] * b[1] + a[1] * b[0])

    def equal(self, a, b) -> bool:
        return a == b

    def div_exact(self, a, b):
        """a/b = a*conj(b)/norm(b), the conjugate-times-norm channel.

        b nonzero implies norm(b) = re^2+im^2 > 0 (positive definite over Q), so it
        is always invertible."""
        n = b[0] * b[0] + b[1] * b[1]
        if n == 0:
            raise ZeroDivisionError("division by zero")
        return self.mul(a, (b[0] / n, -b[1] / n))


QI_RING = QIRing()


# ---------------------------------------------------------------------------
# Membership channel: closed term -> Q(z) -> reduction modulo z^2+1
# ---------------------------------------------------------------------------

def _lift_const(t, const, z: Sym):
    """Replace the constant atom `const` (pointer equality, no name sniffing) by
    the variable z wherever it occurs in t."""
    if t is const:
        return z
    if isinstance(t, T.Expr) and t.args:
        return T.mk(t.head, tuple(_lift_const(a, const, z) for a in t.args))
    return t


def _pair_mod(p: Poly):
    """Reduce a univariate polynomial modulo z^2+1 to (re, im):
    z^k = (-1)^(k//2) * z^(k mod 2)."""
    re, im = Fr(0), Fr(0)
    for k, c in p.monos:
        v = -c if (k[0] // 2) % 2 else c
        if k[0] % 2:
            im += v
        else:
            re += v
    return (re, im)


def qi_of_term(i_const, t):
    """Closed term -> Q(i) normal-form pair; None when not a member.

    Free variables, other constants or functions (pi, sin, ...), non-integer powers,
    and division by zero all fail the Q(z) projection or make the denominator
    non-invertible, and are reported as None without guessing."""
    if T.free_vars(t):
        return None                     # not closed: Q(i) is a constant field
    z = Sym("z")                        # a closed term has no free variable, so z cannot collide
    rf = rf_from_term(Q_RING, _lift_const(t, i_const, z), (z,))
    if rf is None:
        return None
    num = _pair_mod(rf.num)
    den = _pair_mod(rf.den)
    if den[0] == 0 and den[1] == 0:
        return None                     # denominator = 0 (mod z^2+1): a division-by-zero term
    return QI_RING.div_exact(num, den)


# ---------------------------------------------------------------------------
# The domain
# ---------------------------------------------------------------------------

class QIDomain(Domain):
    """Q(i) = {a + b*i}. The identity of the constant i is injected by the
    constructor (declaration-based, never sniffed)."""

    name = "Q(i)"
    is_field = True
    is_ordered = False
    is_euclidean = False
    ring = QI_RING

    def __init__(self, i_const):
        self.i = i_const

    def member(self, t) -> bool:
        return qi_of_term(self.i, t) is not None

    def to_term(self, pair):
        """Normal-form pair -> canonical interned term (same value, same shape, same
        pointer)."""
        re, im = pair
        if im == 0:
            return T.N(re)
        im_part = T.times(T.N(im), self.i)
        if re == 0:
            return fold(im_part)
        return fold(T.plus(T.N(re), im_part))

    def normalize(self, t):
        pair = qi_of_term(self.i, t)
        if pair is None:
            return None
        return self.to_term(pair)

    def equal(self, a, b):
        pa = qi_of_term(self.i, a)
        pb = qi_of_term(self.i, b)
        if pa is None or pb is None:
            return None                  # not a member: caller out of bounds
        return pa == pb
