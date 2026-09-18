"""Equality and domain normal form.

**The domain normal form is the decision procedure.** This is not a simplifier
guessing: equality is decided by reducing to a canonical form and comparing.

`normal_form` reduces a term (or an equation) to the normal form of its domain;
`equal` decides on normal forms. A projection hit decides completely; when the
projection misses, it falls back to literal folding, and if that also misses,
the caller handles it as undecided. Nothing is guessed.

This is also where "equality comes first" is implemented: before any new
structure enters the system, this channel must work.
"""

from cas.syntax import term as T
from cas.math.project import project, zero_of, normalize as proj_normalize
from cas.math.domains.qarith import fold


def normal_form(t):
    """The domain normal form of a term or equation: on a projection hit, the
    domain normal form; otherwise the input unchanged.

    An equation is normalized as "the difference of the two sides is zero":
    `Eq(l, r) -> Eq(nf(l - r), 0)`. Reducing both sides to one canonical form
    and reducing their difference to zero are the same thing, and the latter
    avoids maintaining a separate equation-specific canonical form.
    """
    if T.is_eq(t):
        lhs, rhs = t.args
        hit = project(T.plus(lhs, T.neg(rhs)))
        if hit is not None:
            return T.eq(proj_normalize(hit), T.ZERO)
        return t
    hit = project(t)
    if hit is not None:
        return proj_normalize(hit)
    return t


def equal(a, b) -> bool:
    """Equality of equations: the difference of the two sides is decided to
    vanish through projection (K(x) contains K[x] contains Q).

    This decides completely only within the covered fragment. When the
    projection misses, it falls back to a literal-fold comparison (syntactic
    equivalence counts as true); if that is also inconclusive it returns "not
    equal". A caller needing three-valued semantics should check fragment
    coverage first (verdict/decide); UNKNOWN is not produced here to avoid
    mixing the decision-layer vocabulary.
    """
    if not T.is_eq(a) or not T.is_eq(b):
        return a is b
    la, ra = a.args
    lb, rb = b.args
    d = T.plus(T.plus(la, T.neg(ra)), T.neg(T.plus(lb, T.neg(rb))))
    z = zero_of(d)
    if z is True:
        return True
    if z is False:
        return False
    return fold(T.plus(la, T.neg(ra))) is fold(T.plus(lb, T.neg(rb)))
